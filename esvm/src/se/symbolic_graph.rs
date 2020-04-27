use std::io;
use std::io::Write;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};
use std::thread::{self, JoinHandle};

use crossbeam::queue::SegQueue;
use crossbeam_channel as channel;

use crate::se::symbolic_edge::{EdgeType, SymbolicEdge};
use crate::se::symbolic_executor::{self, symbolic_step};
use crate::se::symbolic_state::SeState;

pub struct SymbolicGraph {
    states: Vec<Arc<SeState>>,
    edges: Vec<SymbolicEdge>,
    initial_state: Arc<SeState>,
    end_states: Vec<Arc<SeState>>,

    unprocessed_states: Arc<SegQueue<Arc<SeState>>>,
    being_processed: Arc<AtomicUsize>,

    // channels for communicating with worker threads
    transition_input: Channels<Arc<SeState>>,
    transition_output: Channels<Transition>,

    solver_needed_input: Channels<SolverInput>,
    solver_needed_output: Channels<SolverOutput>,

    solver_not_needed: Channels<(usize, Vec<(SeState, EdgeType)>)>,

    kill_switch_sender: Option<channel::Sender<()>>, // only used for ending all threads
    kill_switch_receiver: channel::Receiver<()>,     // only used for ending all threads

    // Worker threads
    transition_workers: Vec<TransitionWorker>,
    solver_needed_workers: Vec<SolverWorker>,
}

struct TransitionWorker {
    handle: Option<JoinHandle<()>>,
}

impl TransitionWorker {
    fn new(
        input: channel::Receiver<Arc<SeState>>,
        output: channel::Sender<Transition>,
        kill_switch: channel::Receiver<()>,
    ) -> Self {
        let handle = Some(thread::spawn(move || {
            loop {
                select! {
                    recv(input, msg) => {
                        let input_state = msg.unwrap(); // channel does not close
                        let transitions = symbolic_step(&input_state);
                        let res = Transition::new(input_state.id, transitions);
                        output.send(res);
                    },
                    // closing signal, shut down worker
                    recv(kill_switch, msg) => {
                        debug_assert_eq!(msg, None);
                        break;
                    }
                }
            }
        }));
        Self { handle }
    }
}

struct SolverWorker {
    handle: Option<JoinHandle<()>>,
}

impl SolverWorker {
    fn new(
        input: channel::Receiver<SolverInput>,
        output: channel::Sender<SolverOutput>,
        kill_switch: channel::Receiver<()>,
    ) -> Self {
        let handle = Some(thread::spawn(move || {
            loop {
                select! {
                    recv(input, msg) => {
                        let input = msg.unwrap(); // channel does not close
                        let mut res = Vec::with_capacity(input.len());
                        let len = input.len();
                        for (state, edge) in input.transitions {
                            let check = if len == 1 {
                                true
                            } else {
                                state.check_sat()
                            };
                            res.push(  ((state, edge),  check) );
                        }
                        output.send(SolverOutput{ id: input.id, transitions: res});
                    },
                    // closing signal, shut down worker
                    recv(kill_switch, msg) => {
                        debug_assert_eq!(msg, None);
                        break;
                    }
                }
            }
        }));
        Self { handle }
    }
}

struct SolverInput {
    // the id of the input state corresponding to the transitions
    id: usize,
    transitions: Vec<(SeState, EdgeType)>,
}

impl SolverInput {
    fn len(&self) -> usize {
        self.transitions.len()
    }
}

struct SolverOutput {
    id: usize,
    transitions: Vec<((SeState, EdgeType), bool)>,
}

struct Channels<T> {
    sender: channel::Sender<T>,
    receiver: channel::Receiver<T>,
}

impl<T> Channels<T> {
    fn new_bounded(bound: usize) -> Self {
        let (sender, receiver) = channel::bounded(bound);
        Self { sender, receiver }
    }

    fn new_unbounded() -> Self {
        let (sender, receiver) = channel::unbounded();
        Self { sender, receiver }
    }
}

struct Transition {
    // the id of the input state corresponding to the transitions
    id: usize,
    transitions: Vec<(SeState, EdgeType)>,
}

impl Transition {
    fn new(id: usize, transitions: Vec<(SeState, EdgeType)>) -> Self {
        Self { id, transitions }
    }
}

// since the select macro borrows a channel from the graph immutably, we can not call a mutable
// function from the select macros, thus we simply inline the handle_transitions function
// passing self as an identifier is required see:
// https://stackoverflow.com/questions/44120455/how-to-call-methods-on-self-in-macros
// https://danielkeep.github.io/tlborm/book/mbe-min-non-identifier-identifiers.html
macro_rules! handle_transitions {
    ($self:ident, $next_id:ident, $transitions:ident) => {
        // splitt vec into two
        // use vec.drain_filter once available to reuse memory
        let (conditional, simple): (Vec<_>, Vec<_>) =
            $transitions.into_iter().partition(|(_, edge_info)| {
                if let EdgeType::Cond(_) = edge_info {
                    true
                } else {
                    false
                }
            });

        // handle easy cases first
        if !simple.is_empty() {
            $self.solver_not_needed.sender.send(($next_id, simple));
            $self.being_processed.fetch_add(1, Ordering::SeqCst);
        }

        if !conditional.is_empty() {
            // send more complex state transitions to be processed async
            $self.solver_needed_input.sender.send(SolverInput {
                id: $next_id,
                transitions: conditional,
            });
            $self.being_processed.fetch_add(1, Ordering::SeqCst);
        }
    };
}

// cleanup worker threads
impl Drop for SymbolicGraph {
    fn drop(&mut self) {
        // close all workers when we don't execute the graph
        // mainly for testing
        if self.kill_switch_sender.is_some() {
            let kill_switch = self
                .kill_switch_sender
                .take()
                .expect("Could not take kill switch");
            drop(kill_switch); // closes kill switch channel
        }
        for worker in &mut self.transition_workers {
            worker
                .handle
                .take()
                .expect("Handle not set correctly on worker thread")
                .join()
                .expect("Threads not closed properly after analysis");
        }
        for worker in &mut self.solver_needed_workers {
            worker
                .handle
                .take()
                .expect("Handle not set correctly on worker thread")
                .join()
                .expect("Threads not closed properly after analysis");
        }
    }
}

impl SymbolicGraph {
    pub fn new(initial_state: SeState) -> Self {
        let initial_state = Arc::new(initial_state);
        let states = vec![Arc::clone(&initial_state)];
        let edges = vec![];
        let end_states = vec![];

        let unprocessed_states = Arc::new(SegQueue::new());
        unprocessed_states.push(Arc::clone(&initial_state));
        let being_processed = Arc::new(AtomicUsize::new(0));

        // + 1 for uneven number of cores, they block on solver anyways
        let cores = (initial_state.config().cores / 2) + 1;

        //  create channels
        let transition_input = Channels::new_unbounded();
        let transition_output = Channels::new_unbounded();

        let solver_needed_input = Channels::new_unbounded();
        let solver_needed_output = Channels::new_unbounded();

        let solver_not_needed = Channels::new_unbounded();

        let kill_switch = Channels::new_bounded(0);
        let kill_switch_sender = Some(kill_switch.sender);
        let kill_switch_receiver = kill_switch.receiver;

        // create worker threads
        let mut transition_workers = Vec::with_capacity(cores);
        for _ in 0..cores {
            let (input, output, kill_switch) = (
                transition_input.receiver.clone(),
                transition_output.sender.clone(),
                kill_switch_receiver.clone(),
            );
            transition_workers.push(TransitionWorker::new(input, output, kill_switch));
        }

        let mut solver_needed_workers = Vec::with_capacity(cores);
        for _ in 0..cores {
            let (input, output, kill_switch) = (
                solver_needed_input.receiver.clone(),
                solver_needed_output.sender.clone(),
                kill_switch_receiver.clone(),
            );
            solver_needed_workers.push(SolverWorker::new(input, output, kill_switch));
        }

        SymbolicGraph {
            unprocessed_states,
            initial_state,
            states,
            edges,
            end_states,
            transition_input,
            transition_output,
            solver_needed_input,
            solver_needed_output,
            solver_not_needed,
            kill_switch_sender,
            kill_switch_receiver,
            transition_workers,
            solver_needed_workers,
            being_processed,
        }
    }

    pub fn analyze_graph(&mut self) {
        let kill_switch_sender = self.kill_switch_sender.take().unwrap();
        let unprocessed_states = Arc::clone(&self.unprocessed_states);
        let being_processed = Arc::clone(&self.being_processed);
        let transition_input_sender = self.transition_input.sender.clone();
        let solver_not_needed_sender = self.solver_not_needed.sender.clone();
        let solver_needed_input_sender = self.solver_needed_input.sender.clone();

        let main_thread = thread::spawn(move || {
            let mut counter = 0;

            loop {
                if let Ok(next_state) = unprocessed_states.pop() {
                    counter += 1;
                    if counter >= 20_000 {
                        break;
                    }
                    // send expansive transtions to worker threads, this blocks when all worker threads
                    // are used
                    if symbolic_executor::expensive_computation(&next_state) {
                        debug!("Sending expensive computation to thread");
                        being_processed.fetch_add(1, Ordering::SeqCst);
                        transition_input_sender.send(next_state);
                        continue;
                    }

                    let next_id = next_state.id;
                    let transitions = symbolic_step(&next_state);

                    let (conditional, simple): (Vec<_>, Vec<_>) =
                        transitions.into_iter().partition(|(_, edge_info)| {
                            if let EdgeType::Cond(_) = edge_info {
                                true
                            } else {
                                false
                            }
                        });

                    // handle easy cases first
                    if !simple.is_empty() {
                        solver_not_needed_sender.send((next_id, simple));
                        being_processed.fetch_add(1, Ordering::SeqCst);
                    }

                    if !conditional.is_empty() {
                        // send more complex state transitions to be processed async
                        solver_needed_input_sender.send(SolverInput {
                            id: next_id,
                            transitions: conditional,
                        });
                        being_processed.fetch_add(1, Ordering::SeqCst);
                    }
                } else if being_processed.load(Ordering::SeqCst) == 0
                    && unprocessed_states.is_empty()
                {
                    // if we can not pop a new state and there are no ongoing computations we have
                    // reached the end of the symbolic execution
                    break;
                }
            }

            // shutdown all threads
            drop(kill_switch_sender);
        });

        loop {
            select! {
                recv(self.transition_output.receiver, msg) => {
                    let Transition{id: next_id, transitions} = msg.unwrap();
                    handle_transitions!(self, next_id, transitions);
                }
                recv(self.solver_needed_output.receiver, msg) => {
                    let SolverOutput{id: next_id, transitions: conditional } = msg.unwrap();

                    for ((state, edge_info), check) in conditional.into_iter() {
                        let id = state.id;
                        let state = Arc::new(state);
                        if check {
                            self.unprocessed_states.push(Arc::clone(&state));
                            self.edges.push(SymbolicEdge::new(next_id, id, edge_info));
                        } else {
                            self
                                .edges
                                .push(SymbolicEdge::new(next_id, id, EdgeType::Unsat));
                        }
                        self.states.push(state);
                    }
                }
                recv(self.solver_not_needed.receiver, msg) => {
                    let (next_id, simple) = msg.unwrap();
                    for (state, edge_info) in simple.into_iter() {
                        let id = state.id;
                        let state = Arc::new(state);

                        if let EdgeType::Terminal = edge_info {
                            self.end_states.push(Arc::clone(&state));
                            self.edges.push(SymbolicEdge::new(next_id, id, edge_info));
                        } else {
                            self.unprocessed_states.push(Arc::clone(&state));
                            self.edges.push(SymbolicEdge::new(next_id, id, edge_info));
                        }
                        self.states.push(state);
                    }
                }
                recv(self.kill_switch_receiver, msg) => {
                    debug_assert_eq!(msg, None);
                    break;
                }
            }

            self.being_processed.fetch_sub(1, Ordering::SeqCst);
        }

        main_thread.join().expect("Could not close main thread");
        debug_assert_eq!(self.being_processed.load(Ordering::SeqCst), 0);
    }

    /// This function only returns states where changes occured
    pub fn end_states_storage(&self) -> Vec<SeState> {
        let mut res = vec![];
        for state in &self.end_states {
            if state.env != self.initial_state.env {
                res.push((**state).clone());
            }
        }
        res
    }

    pub fn initial_state(&self) -> &SeState {
        &(*self.initial_state)
    }

    // only available for testing, very expensive
    #[cfg(test)]
    pub fn get_state_by_id(&self, id: usize) -> SeState {
        for state in &self.states {
            if state.id == id {
                return (**state).clone();
            }
        }
        unreachable!()
    }

    pub fn end_states(&self) -> Vec<SeState> {
        let mut res = vec![];
        for state in &self.end_states {
            res.push((**state).clone());
        }
        res
    }

    pub fn to_dot<W: Write>(&self, w: &mut W) -> Result<(), io::Error> {
        writeln!(w, "digraph se_graph {{")?;
        for s in &self.states {
            s.to_dot(w)?;
        }
        for e in &self.edges {
            e.to_dot(w)?;
        }
        writeln!(w, "}}")?;
        Ok(())
    }
}
