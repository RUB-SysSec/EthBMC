use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{self, Debug, Formatter};
use std::io::{self, Write};
use std::sync::{Arc, RwLock};
use std::usize;

use ena::unify::{InPlaceUnificationTable, NoError, UnificationTable, UnifyKey, UnifyValue};

use crate::bytecode::Instr;
use crate::se::{
    env::{fresh_var_name, Account, AccountId, Env, Transaction, TxId, GLOBAL_COVERAGE_MAP},
    expr::{
        bval::*,
        formel_builder::SmtLib2Builder,
        solver::SolverPool,
        symbolic_memory::{self, MVal, MemoryOperation, MemoryType, SymbolicMemory},
    },
    symbolic_analysis::{Context, SeConfig},
    symbolic_edge::*,
};

bitflags! {
    #[derive(Default)]
    pub struct Flags: u32 {
        const REENTRANCY = 0b0000_0001;
        const HIJACK_CONTROL_FLOW = 0b0000_0010;
        const STATIC = 0b1000_0000;
        const FAILURE = 0b0000_0100;
        const NON_STATIC_MASK = 0b0111_1111;

        // precompiled contracts
        const ECDSA_RECOVERY = 0b0000_0001_0000_0000;
        const SHA256 = 0b0000_0010_0000_0000;
        const RIPEMD160 = 0b0000_0100_0000_0000;
        const IDENTITY = 0b0000_1000_0000_0000;
        const MODULAR_EXPONENTIATION = 0b0001_0000_0000_0000;
        const EC_ADDITION = 0b0010_0000_0000_0000;
        const EC_SCALAR_MULTIPLICATION = 0b0100_0000_0000_0000;
        const EC_PAIRING_EQUATION = 0b1000_0000_0000_0000;
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum HaltingReason {
    Return,
    Revert,
    Stop,
    Selfdestruct,
}

#[derive(Clone, Debug)]
pub struct ResultState {
    /// The content of the stack
    pub stack: Vec<BVal>,

    /// The current enviroment the execution runs in. Copy-on-write, e.g. when a new account gets
    /// created or it is written to storage
    pub env: Arc<Env>,

    /// The memory graph for this execution
    pub memory: Arc<SymbolicMemory>,

    /// The memory for the current execution
    pub mem: MVal,

    /// The current path constraints
    pub constraints: Arc<Vec<BVal>>,

    /// The input transaction for the current execution
    pub input_tx: TxId,

    /// The account associated with the code being executed
    pub account: AccountId,

    /// The return data of previous execution. Only set if last execution ended in a return
    /// statement
    pub returndata: Option<MVal>,

    /// The size of the returndata for the previous execution
    pub returndata_size: BVal,

    /// The halting reason for an end of path
    pub halting_reason: Option<HaltingReason>,

    pub call_depth: usize,

    pub old_memory: Arc<HashSet<MVal>>,
    pub reads: ReadTracker,
    pub previous_tx: Vec<TxId>,
    pub flags: Flags,
    pub solver_pool: Arc<SolverPool>,
    pub keccaks: Arc<HashSet<BVal>>,
    pub constraints_tracker: Arc<ConstraintSetSplitter>,
}

// rc for everything that does not change each state
#[derive(Clone)]
pub struct SeState {
    /// The state id
    pub id: usize,

    /// The current programm counter
    pub pc: usize,

    /// The content of the stack
    pub stack: Vec<BVal>,

    /// The current enviroment the execution runs in. Copy-on-write, e.g. when a new account gets
    /// created or it is written to storage
    pub env: Arc<Env>,

    /// The memory for the current execution
    pub mem: MVal,

    /// The memory graph for this execution
    pub memory: Arc<SymbolicMemory>,

    /// The current path constraints
    #[cfg(not(test))]
    constraints: Arc<Vec<BVal>>,

    #[cfg(test)]
    pub constraints: Arc<Vec<BVal>>,

    /// The input transaction for the current execution
    pub input_tx: TxId,

    /// The account associated with the code being executed
    pub account: AccountId,

    /// The return data of previous execution. Only set if last execution ended in a return
    /// statement
    pub returndata: Option<MVal>,

    /// The size of the returndata for the previous execution
    pub returndata_size: BVal,

    /// The halting reason for an end of path
    pub halting_reason: Option<HaltingReason>,

    /// The counter for the call depth
    pub call_depth: usize,

    /// The Context of the current execution
    pub context: Arc<Context>,

    /// Memory from previous transactions
    pub old_memory: Arc<HashSet<MVal>>,

    /// Shortcut for tracking reads on memory
    pub reads: ReadTracker,

    /// The transactions from the previous round
    pub previous_tx: Vec<TxId>,

    /// Flags for tracking reenetrancy etc.
    pub flags: Flags,

    /// All symbolic keccak results which are present in the execution
    pub keccaks: Arc<HashSet<BVal>>,

    /// Variable Tracker vor easier constraint handling
    pub constraints_tracker: Arc<ConstraintSetSplitter>,

    // loop detection
    last_addrs: Arc<VecDeque<BVal>>,
    addrs_counter: Arc<HashMap<BVal, usize>>,
}

pub type ReadTracker = Arc<HashMap<MVal, HashSet<BVal>>>;

impl Debug for SeState {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "State{{\n\tid: {}\n\tpc: {} ({:?})\n\tstack: {:?}\n\tconstrainst: {:?}\n\tmemory: {}\n\tstorage: {}\n}}", self.id, self.pc, self.get_instruction(), self.stack, self.constraints, symbolic_memory::pretty_print(&(*self.memory), self.mem), symbolic_memory::pretty_print(&self.memory, self.account().storage))
    }
}

impl SeState {
    pub fn new(
        context: Arc<Context>,
        mut memory: Arc<SymbolicMemory>,
        env: &Arc<Env>,
        account: AccountId,
        input_tx: TxId,
    ) -> Self {
        let constraints = Arc::new(vec![]);
        let stack = vec![];
        let mem = symbolic_memory::create_new_memory(
            Arc::make_mut(&mut memory),
            fresh_var_name(&format!("{}_mem", env.get_account(&account).name)),
            MemoryType::Memory,
            None,
        );
        let id = context.next_id();

        let last_addrs = Arc::new(VecDeque::new());
        let addrs_counter = Arc::new(HashMap::new());
        let reads = Arc::new(HashMap::new());
        let previous_tx = vec![];
        let returndata = None;
        let returndata_size = const_usize(0);

        let call_depth = 0;
        let halting_reason = None;
        let old_memory = Arc::new(HashSet::new());
        let env = Arc::clone(env);
        let keccaks = Arc::new(HashSet::new());
        let constraints_tracker = Arc::new(ConstraintSetSplitter::new());

        SeState {
            id,
            pc: 0,
            env,
            stack,
            constraints,
            memory,
            mem,
            last_addrs,
            addrs_counter,
            account,
            input_tx,
            reads,
            previous_tx,
            returndata,
            returndata_size,
            call_depth,
            halting_reason,
            old_memory,
            flags: Default::default(),
            context,
            keccaks,
            constraints_tracker,
        }
    }

    pub fn from_result_state(
        s: ResultState,
        context: Arc<Context>,
        memory: Arc<SymbolicMemory>,
        env: &Arc<Env>,
        account_id: AccountId,
        input_tx: TxId,
    ) -> Self {
        // copy env and config
        let mut new_state = SeState::new(context, memory, env, account_id, input_tx);

        // call_depth
        new_state.call_depth = s.call_depth;

        // constrints
        new_state.constraints = s.constraints;

        // update previous_tx
        let mut previous_tx = vec![s.input_tx];
        previous_tx.append(&mut s.previous_tx.clone());
        new_state.previous_tx = previous_tx;

        // update old memory
        let mut old_memory = Arc::clone(&s.old_memory);
        Arc::make_mut(&mut old_memory).insert(s.mem);
        new_state.old_memory = old_memory;

        // reads
        new_state.reads = s.reads;

        // flags
        new_state.flags = s.flags;

        // keccaks known in this execution context
        new_state.keccaks = s.keccaks;

        // tracker
        new_state.constraints_tracker = Arc::clone(&s.constraints_tracker);

        // tracker
        new_state.constraints_tracker = Arc::clone(&s.constraints_tracker);

        new_state
    }

    pub fn create_succ(&self) -> Self {
        // this is necessary since solc might put a jump instruction at the end of the code
        let new_pc = match self.context.instruction_size(self.pc) {
            Some(s) => self.pc + s,
            None => usize::MAX, // usize::MAX ensures that the code panics if the
                                // pc is not overwritten after calling this function
                                // (jump)
        };

        let id = self.context.next_id();
        SeState {
            id,
            pc: new_pc,
            stack: self.stack.clone(),
            env: self.env.clone(),
            mem: self.mem,
            constraints: self.constraints.clone(),
            last_addrs: self.last_addrs.clone(),
            addrs_counter: self.addrs_counter.clone(),
            account: self.account,
            input_tx: self.input_tx,
            reads: self.reads.clone(),
            previous_tx: self.previous_tx.clone(),
            returndata: self.returndata,
            returndata_size: self.returndata_size.clone(),
            call_depth: self.call_depth,
            halting_reason: self.halting_reason.clone(),
            old_memory: self.old_memory.clone(),
            flags: self.flags,
            context: Arc::clone(&self.context),
            keccaks: Arc::clone(&self.keccaks),
            memory: Arc::clone(&self.memory),
            constraints_tracker: Arc::clone(&self.constraints_tracker),
        }
    }

    pub fn fork(&self) -> Self {
        let id = self.context.next_id();
        SeState {
            id,
            pc: self.pc,
            stack: self.stack.clone(),
            env: self.env.clone(),
            mem: self.mem,
            constraints: self.constraints.clone(),
            last_addrs: self.last_addrs.clone(),
            addrs_counter: self.addrs_counter.clone(),
            account: self.account,
            input_tx: self.input_tx,
            reads: self.reads.clone(),
            previous_tx: self.previous_tx.clone(),
            returndata: self.returndata,
            returndata_size: self.returndata_size.clone(),
            call_depth: self.call_depth,
            halting_reason: self.halting_reason.clone(),
            old_memory: self.old_memory.clone(),
            flags: self.flags,
            context: Arc::clone(&self.context),
            keccaks: Arc::clone(&self.keccaks),
            memory: Arc::clone(&self.memory),
            constraints_tracker: Arc::clone(&self.constraints_tracker),
        }
    }

    pub fn as_result_state(&self) -> ResultState {
        ResultState {
            call_depth: self.call_depth,
            stack: self.stack.clone(),
            env: Arc::clone(&self.env),
            mem: self.mem,
            memory: Arc::clone(&self.memory),
            constraints: Arc::clone(&self.constraints),
            input_tx: self.input_tx,
            account: self.account,
            returndata: self.returndata,
            returndata_size: Arc::clone(&self.returndata_size),
            halting_reason: self.halting_reason.clone(),
            old_memory: Arc::clone(&self.old_memory),
            reads: Arc::clone(&self.reads),
            previous_tx: self.previous_tx.clone(),
            flags: self.flags,
            solver_pool: self.context.solver_pool(),
            keccaks: Arc::clone(&self.keccaks),
            constraints_tracker: Arc::clone(&self.constraints_tracker),
        }
    }

    pub fn get_jump_info(
        &self,
        cond: &BVal,
        target_val: &BVal,
        mut target_state: Self,
    ) -> Option<(Self, EdgeType)> {
        let mut needs_condition = false;
        let mut needs_addr = false;
        match FVal::check_truth(cond) {
            SymbolicTruth::False => return None,
            SymbolicTruth::Maybe => needs_condition = true,
            SymbolicTruth::True => {}
        }

        match FVal::check_truth(&eql(target_val, &const_usize(target_state.pc))) {
            SymbolicTruth::True => {}
            SymbolicTruth::False => return None,
            SymbolicTruth::Maybe => needs_addr = true,
        }

        let check = match (needs_condition, needs_addr) {
            (true, true) => and(cond, &eql(target_val, &const_usize(target_state.pc))),
            (false, true) => eql(target_val, &const_usize(target_state.pc)),
            (true, false) => cond.clone(),
            (false, false) => one(),
        };

        if needs_condition || needs_addr {
            target_state.push_constraint(Arc::clone(&check));
        }
        Some((target_state, edge_conditional(check)))
    }

    pub fn check_sat(&self) -> bool {
        let constraints = self.env_constraints();
        // this is the case when we only added simple constraints so far
        let mut splitter = (*self.constraints_tracker).clone();
        for c in constraints {
            if let SymbolicTruth::False = FVal::check_truth(&c) {
                return false;
            }
            splitter.add_constraint(&self.memory, &c);
        }
        for c in self.constraints.iter() {
            if let SymbolicTruth::False = FVal::check_truth(&c) {
                return false;
            }
        }
        debug_assert_eq!(self.constraints_tracker.constraints, *self.constraints);

        SplittingBuilder::check_sat(
            splitter,
            &self.memory,
            self.context.solver_pool(),
            &self.reads,
        )
    }

    pub fn get_value(&self, value: &BVal) -> Option<BVal> {
        let constraints = self.env_constraints();
        // this is the case when we only added simple constraints so far
        let mut splitter = (*self.constraints_tracker).clone();
        for c in constraints {
            splitter.add_constraint(&self.memory, &c);
        }
        debug_assert_eq!(self.constraints_tracker.constraints, *self.constraints);
        SplittingBuilder::get_value(
            splitter,
            &self.memory,
            self.context.solver_pool(),
            &self.reads,
            value,
        )
    }

    pub fn get_values_for_array(&self, values: &[BVal]) -> Option<Vec<BVal>> {
        let constraints = self.env_constraints();
        // this is the case when we only added simple constraints so far
        let mut splitter = (*self.constraints_tracker).clone();
        for c in constraints {
            splitter.add_constraint(&self.memory, &c);
        }
        debug_assert_eq!(self.constraints_tracker.constraints, *self.constraints);
        SplittingBuilder::get_values_for_array(
            splitter,
            &self.memory,
            self.context.solver_pool(),
            &self.reads,
            values,
        )
    }

    pub fn config(&self) -> &SeConfig {
        self.context.config()
    }

    pub fn reset_returndata(&mut self) {
        self.returndata = None;
        self.returndata_size = const_usize(0);
    }

    pub fn revert_state_changes(&mut self) {
        let old_stor = self.account().storage;
        Arc::make_mut(&mut self.old_memory).insert(old_stor);
        self.account_mut().storage = self.context.initial_storage();
    }

    pub fn get_instruction(&self) -> Option<Instr> {
        GLOBAL_COVERAGE_MAP
            .lock()
            .get_mut(&self.account)
            .unwrap()
            .taint(self.pc);
        self.context.instruction(self.pc)
    }
    pub fn get_codesize(&self) -> usize {
        self.account().get_codesize()
    }

    pub fn remove_keccak_result(&mut self, val: &BVal) {
        Arc::make_mut(&mut self.keccaks).remove(val);
    }

    pub fn record_keccak_result(&mut self, val: &BVal) {
        Arc::make_mut(&mut self.keccaks).insert(Arc::clone(val));
    }

    fn get_jump_targets_for(&mut self, val: &BVal) -> Vec<usize> {
        // check for loops
        if self.check_for_loop(val) {
            return vec![];
        }

        if let Some(v) = FVal::as_usize(&val) {
            if self.context.is_jump_target(v) {
                return vec![v];
            } else {
                debug!("Tried to jump to invalid jump target: {}, droping path!", v);
            }
            return vec![];
        }
        let res = self.context.jump_targets().iter().cloned().collect();
        res
    }

    fn check_for_loop(&mut self, val: &BVal) -> bool {
        for addr in self.last_addrs.iter() {
            if let SymbolicTruth::True = FVal::check_truth(&eql(val, addr)) {
                // increase counter
                let count = *self.addrs_counter.get(val).unwrap();
                if count >= self.context.config().loop_bound {
                    info!(
                        "Loop detected, dropping path after {} iterations!",
                        self.context.config().loop_bound
                    );
                    return true;
                }
                Arc::make_mut(&mut self.addrs_counter).insert(Arc::clone(val), count + 1);
                return false;
            }
        }

        Arc::make_mut(&mut self.last_addrs).push_back(Arc::clone(val));
        Arc::make_mut(&mut self.addrs_counter).insert(Arc::clone(val), 0);

        // track last 10 addresses
        if self.last_addrs.len() > 10 {
            let key = Arc::make_mut(&mut self.last_addrs).pop_front().unwrap();
            Arc::make_mut(&mut self.addrs_counter).remove(&key);
        }
        false
    }

    pub fn jump_to(&mut self, addr_val: &BVal) -> Vec<Self> {
        let mut res = vec![];
        for addr in self.get_jump_targets_for(addr_val) {
            let mut cur = self.create_succ();
            cur.pc = addr;
            res.push(cur)
        }
        res
    }

    pub fn pop1(&mut self) -> Option<(BVal)> {
        match self.stack.pop() {
            Some(a) => Some(a),
            _ => None,
        }
    }

    pub fn pop2(&mut self) -> Option<(BVal, BVal)> {
        match (self.stack.pop(), self.stack.pop()) {
            (Some(a), Some(b)) => Some((a, b)),
            _ => None,
        }
    }

    pub fn pop3(&mut self) -> Option<(BVal, BVal, BVal)> {
        match (self.stack.pop(), self.stack.pop(), self.stack.pop()) {
            (Some(a), Some(b), Some(c)) => Some((a, b, c)),
            _ => None,
        }
    }

    pub fn pop4(&mut self) -> Option<(BVal, BVal, BVal, BVal)> {
        match (
            self.stack.pop(),
            self.stack.pop(),
            self.stack.pop(),
            self.stack.pop(),
        ) {
            (Some(a), Some(b), Some(c), Some(d)) => Some((a, b, c, d)),
            _ => None,
        }
    }

    #[cfg_attr(feature = "cargo-clippy", allow(many_single_char_names))]
    pub fn pop6(&mut self) -> Option<(BVal, BVal, BVal, BVal, BVal, BVal)> {
        match (
            self.stack.pop(),
            self.stack.pop(),
            self.stack.pop(),
            self.stack.pop(),
            self.stack.pop(),
            self.stack.pop(),
        ) {
            (Some(a), Some(b), Some(c), Some(d), Some(e), Some(f)) => Some((a, b, c, d, e, f)),
            _ => None,
        }
    }
    #[cfg_attr(feature = "cargo-clippy", allow(many_single_char_names))]
    pub fn pop7(&mut self) -> Option<(BVal, BVal, BVal, BVal, BVal, BVal, BVal)> {
        match (
            self.stack.pop(),
            self.stack.pop(),
            self.stack.pop(),
            self.stack.pop(),
            self.stack.pop(),
            self.stack.pop(),
            self.stack.pop(),
        ) {
            (Some(a), Some(b), Some(c), Some(d), Some(e), Some(f), Some(g)) => {
                Some((a, b, c, d, e, f, g))
            }
            _ => None,
        }
    }

    pub fn push(&mut self, v: BVal) {
        self.stack.push(v);
    }

    pub fn push_constraint(&mut self, v: BVal) {
        // a constrain which is allways true is not a constraint
        if let SymbolicTruth::True = FVal::check_truth(&v) {
            return;
        }
        Arc::make_mut(&mut self.constraints_tracker).add_constraint(&self.memory, &v);
        Arc::make_mut(&mut self.constraints).push(v);
    }

    pub fn set_constraints(&mut self, con: &Arc<Vec<BVal>>) {
        self.constraints = Arc::clone(con);
    }

    fn env_constraints(&self) -> Vec<BVal> {
        self.env
            .get_constraints()
            .into_iter()
            .filter(|ref c| {
                if let SymbolicTruth::True = FVal::check_truth(c) {
                    false
                } else {
                    true
                }
            })
            .collect()
    }

    fn record_mload(&mut self, mem: MVal, read: &BVal) {
        let entry = Arc::make_mut(&mut self.reads)
            .entry(mem)
            .or_insert_with(HashSet::new);

        entry.insert(Arc::clone(read));
    }

    pub fn record_read(&mut self, read: &BVal) {
        match read.val() {
            Val256::FMLoad(mem, _) | Val256::FSLoad(mem, _) => self.record_mload(*mem, read),
            Val256::FCombine32(ref v) => {
                for load in v {
                    if let Val256::FMLoad(mem, _) = load.val() {
                        self.record_mload(*mem, load);
                    } else if cfg!(feature = "memcopy") {
                        // this is not allowed to happen in memcopy enviroment
                        panic!("Called record_read with: {:?}", load);
                    }
                }
            }
            _ => {}
        }
    }

    #[cfg(test)]
    pub fn get_reads(&self, mem: MVal) -> Option<HashSet<BVal>> {
        self.reads.get(&mem).cloned()
    }

    pub fn account(&self) -> &Account {
        self.env.get_account(&self.account)
    }

    pub fn account_mut(&mut self) -> &mut Account {
        Arc::make_mut(&mut self.env).get_account_mut(&self.account)
    }

    pub fn input_tx(&self) -> &Transaction {
        self.env.get_tx(&self.input_tx)
    }

    pub fn to_dot<W: Write>(&self, w: &mut W) -> Result<(), io::Error> {
        write!(w, "{} [ shape=\"Mrecord\" fontname=\"Courier New\" label =<<table border=\"0\" cellborder=\"0\" cellpadding=\"3\">", self.id)?;
        write!(
            w,
            "<tr><td colspan=\"2\" align=\"center\" bgcolor=\"grey\"> {} {:?} </td></tr>",
            self.pc,
            self.get_instruction().unwrap_or(Instr::IInvalid)
        )?;
        write!(
            w,
            "<tr><td align=\"left\"> pc: {}</td></tr>",
            escape_special_chars(format!("{:#?}", self.pc), 300)
        )?;
        write!(
            w,
            "<tr><td align=\"left\"> stack: {}</td></tr>",
            escape_special_chars(format!("{:?}", self.stack), 300)
        )?;
        write!(
            w,
            "<tr><td align=\"left\"> mem: {}</td></tr>",
            escape_special_chars(format!("{:?}", self.mem), 300)
        )?;
        write!(
            w,
            "<tr><td align=\"left\"> const: {}</td></tr>",
            escape_special_chars(format!("{:?}", self.constraints), 300)
        )?;
        writeln!(w, "</table>> ];")?;
        Ok(())
    }
}

// also check the length of the string so we can actually display it
pub fn escape_special_chars(val: String, cut: usize) -> String {
    let result = if val.len() > cut {
        format!("{} ...", String::from(val.get(0..cut).unwrap()))
    } else {
        val
    };
    result
        .replace("&", "&amp;")
        .replace("\"", "&quot;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace("[", "&#91;")
        .replace("]", "&#93;")
        .replace("{", "&#40;")
        .replace("}", "&#41;")
        .replace("|", "&#124;")
}

lazy_static! {
    static ref SAT_CACHE: RwLock<HashMap<Vec<BVal>, bool>> = { RwLock::new(HashMap::new()) };
}

fn get_sat_cached_or_insert(
    constraint_set: Vec<BVal>,
    memory: &SymbolicMemory,
    pool: Arc<SolverPool>,
    reads: &ReadTracker,
    read_cache: &mut HashMap<MVal, HashSet<BVal>>,
) -> bool {
    if let Some(sat) = SAT_CACHE.read().unwrap().get(&constraint_set) {
        return *sat;
    }

    let sat;
    {
        let builder =
            SmtLib2Builder::initialize_from_constraints(reads, memory, read_cache, &constraint_set);
        let mut solver = pool.initialize_from_formel_builder(&builder);
        sat = solver.check_sat();
    }
    SAT_CACHE.write().unwrap().insert(constraint_set, sat);
    sat
}

pub struct SplittingBuilder {}

impl SplittingBuilder {
    pub fn check_sat(
        mut splitter: ConstraintSetSplitter,
        memory: &SymbolicMemory,
        pool: Arc<SolverPool>,
        reads: &ReadTracker,
    ) -> bool {
        let disjoint_sets = splitter.disjoint_sets();
        let mut read_cache = HashMap::new();
        for constraint_set in disjoint_sets {
            let sat = get_sat_cached_or_insert(
                constraint_set,
                memory,
                Arc::clone(&pool),
                reads,
                &mut read_cache,
            );
            if !sat {
                return false;
            }
        }
        true
    }

    pub fn get_value(
        mut splitter: ConstraintSetSplitter,
        memory: &SymbolicMemory,
        pool: Arc<SolverPool>,
        reads: &ReadTracker,
        value: &BVal,
    ) -> Option<BVal> {
        let set = splitter.get_set_for_val(TrackingVariable::bval(value));
        let mut read_cache = HashMap::new();
        let mut builder =
            SmtLib2Builder::initialize_from_constraints(reads, memory, &mut read_cache, &set);
        let mut solver = pool.initialize_from_formel_builder(&builder);
        solver.get_value(&builder.to_smt(value))
    }

    pub fn get_values_for_array(
        mut splitter: ConstraintSetSplitter,
        memory: &SymbolicMemory,
        pool: Arc<SolverPool>,
        reads: &ReadTracker,
        loads: &[BVal],
    ) -> Option<Vec<BVal>> {
        // loads are all on the same memory anyway
        let set = splitter.get_set_for_val(TrackingVariable::bval(&loads[0]));
        let mut read_cache = HashMap::new();
        let mut builder =
            SmtLib2Builder::initialize_from_constraints(reads, memory, &mut read_cache, &set);
        let mut solver = pool.initialize_from_formel_builder(&builder);
        solver.get_values(
            loads
                .iter()
                .map(|l| builder.to_smt(l))
                .collect::<Vec<_>>()
                .as_slice(),
        )
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
struct IsConstraints(Option<usize>);

impl UnifyValue for IsConstraints {
    type Error = NoError;

    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, NoError> {
        // allways use the first arg, doesn't really matter as long as it is deterministic
        match (value1.0, value2.0) {
            (Some(_), Some(_)) => Ok(IsConstraints(value1.0)),
            (Some(_), None) => Ok(IsConstraints(value1.0)),
            (None, Some(_)) => Ok(IsConstraints(value2.0)),
            (None, None) => Ok(IsConstraints(None)),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
struct TrackingKey(u32);

impl UnifyKey for TrackingKey {
    type Value = IsConstraints;

    fn index(&self) -> u32 {
        self.0
    }
    fn from_index(u: u32) -> Self {
        TrackingKey(u)
    }
    fn tag() -> &'static str {
        "TrackingKey"
    }

    // order towards the lowest key, since the n constraints get assigened the n lowest keys of the
    // union find
    fn order_roots(
        a: TrackingKey,
        a_rank: &Self::Value,
        b: TrackingKey,
        b_rank: &Self::Value,
    ) -> Option<(Self, Self)> {
        if a_rank.0.is_some() {
            Some((a, b))
        } else if b_rank.0.is_some() {
            Some((b, a))
        } else if a.0 > b.0 {
            Some((b, a))
        } else {
            Some((a, b))
        }
    }
}

#[derive(Clone, Debug, Eq, Hash)]
enum TrackingVariable {
    BVal(BVal),
    MVal(MVal),
}

impl PartialEq for TrackingVariable {
    fn eq(&self, other: &TrackingVariable) -> bool {
        match (self, other) {
            (TrackingVariable::BVal(ref l), TrackingVariable::BVal(ref r)) => bval_depended(l, r),
            (TrackingVariable::MVal(ref l), TrackingVariable::MVal(ref r)) => l.eq(r),
            _ => false,
        }
    }
}

// special function for determining if two bvals are dependent of each other
fn bval_depended(l: &BVal, r: &BVal) -> bool {
    match (l.val(), r.val()) {
        // equal constant values do not imply dependency
        (Val256::FConst(_), Val256::FConst(_)) | (Val256::FConst8(_), Val256::FConst8(_)) => false,
        // equal variable names does however (we use unique variable names for all sym variables)
        (Val256::FVarRef(ref l), Val256::FVarRef(ref r)) => l == r,
        (_, _) => l.eq(r),
    }
}

impl TrackingVariable {
    fn bval(val: &BVal) -> Self {
        TrackingVariable::BVal(Arc::clone(val))
    }

    fn mval(val: MVal) -> Self {
        TrackingVariable::MVal(val)
    }
}

#[derive(Clone, Debug)]
pub struct ConstraintSetSplitter {
    constraints: Vec<BVal>,
    ut: InPlaceUnificationTable<TrackingKey>,
    mapping: HashMap<TrackingVariable, TrackingKey>,
}

impl ConstraintSetSplitter {
    fn new() -> Self {
        let constraints = Vec::new();
        let ut = UnificationTable::new();
        let mapping = HashMap::new();
        Self {
            constraints,
            ut,
            mapping,
        }
    }

    #[cfg(test)]
    fn with_capacity(size: u32) -> Self {
        let constraints = Vec::with_capacity(size as usize);
        let ut = UnificationTable::new();
        let mapping = HashMap::new();
        Self {
            constraints,
            ut,
            mapping,
        }
    }

    #[cfg(test)]
    fn from_constraints(memory: &SymbolicMemory, constraints: Vec<BVal>) -> Self {
        let mut splitter = ConstraintSetSplitter::with_capacity(constraints.len() as u32);
        // assign keys to constraints first so their keys match their position in the vec
        for c in &constraints {
            splitter.add_constraint(memory, c);
        }
        splitter
    }

    fn add_constraint(&mut self, memory: &SymbolicMemory, constraint: &BVal) -> TrackingKey {
        let val = TrackingVariable::bval(constraint);
        if let Some(key) = self.mapping.get(&val) {
            return *key;
        }
        let key = self.ut.new_key(IsConstraints(Some(self.constraints.len())));
        self.constraints.push(Arc::clone(&constraint));
        self.mapping.insert(val, key);
        self.process_bval(key, memory, constraint);
        key
    }

    // used for none constraints
    fn get_or_create_key(&mut self, val: TrackingVariable) -> (bool, TrackingKey) {
        if let Some(key) = self.mapping.get(&val) {
            return (true, *key);
        }
        let key = self.ut.new_key(IsConstraints(None));
        self.mapping.insert(val, key);
        (false, key)
    }

    fn disjoint_sets(&mut self) -> Vec<Vec<BVal>> {
        let mut constraints: Vec<Option<Vec<BVal>>> = vec![None; self.constraints.len()];
        for c in &self.constraints {
            let key = self.mapping[&TrackingVariable::bval(c)];
            let root = self.ut.find(key);
            let index = self.ut.probe_value(root);
            let superset = &mut constraints[index.0.unwrap()];
            if let Some(ref mut vec) = superset {
                vec.push(Arc::clone(c));
            } else {
                *superset = Some(vec![Arc::clone(c)]);
            }
        }
        constraints.into_iter().filter_map(|v| v).collect()
    }

    fn get_set_for_val(&mut self, target: TrackingVariable) -> Vec<BVal> {
        let mut constraints = Vec::new();
        let key = self.mapping[&target];
        let target_key = self.ut.find(key);
        for c in &self.constraints {
            let key = self.mapping[&TrackingVariable::bval(c)];
            let root = self.ut.find(key);
            if target_key == root {
                constraints.push(Arc::clone(c));
            }
        }
        constraints
    }

    fn explore_bval(&mut self, parent_key: TrackingKey, memory: &SymbolicMemory, var: &BVal) {
        let (explored, key) = self.get_or_create_key(TrackingVariable::bval(var));
        self.ut.union(parent_key, key);
        if !explored {
            self.process_bval(parent_key, memory, var);
        }
    }

    fn explore_mval(&mut self, parent_key: TrackingKey, memory: &SymbolicMemory, var: MVal) {
        let (explored, key) = self.get_or_create_key(TrackingVariable::mval(var));
        self.ut.union(parent_key, key);
        if !explored {
            self.process_mval(parent_key, memory, var);
        }
    }

    fn process_mval(&mut self, parent_key: TrackingKey, memory: &SymbolicMemory, mem: MVal) {
        let op = &memory[mem].op;
        match op {
            MemoryOperation::Write8 {
                parent: id,
                address: ref addr,
                value: ref val,
            }
            | MemoryOperation::Write256 {
                parent: id,
                address: ref addr,
                value: ref val,
            } => {
                self.explore_bval(parent_key, memory, addr);
                self.explore_bval(parent_key, memory, val);
                self.explore_mval(parent_key, memory, *id);
            }
            MemoryOperation::Memset {
                parent: id,
                index: ref from,
                size: ref length,
                value: ref val,
            } => {
                self.explore_bval(parent_key, memory, from);
                self.explore_bval(parent_key, memory, val);
                self.explore_bval(parent_key, memory, length);
                self.explore_mval(parent_key, memory, *id);
            }
            MemoryOperation::MemsetUnlimited {
                parent: id,
                index: ref from,
                value: ref val,
            } => {
                self.explore_bval(parent_key, memory, from);
                self.explore_bval(parent_key, memory, val);
                self.explore_mval(parent_key, memory, *id);
            }
            MemoryOperation::Memcopy {
                parent: to,
                from,
                index: ref to_index,
                index_from: ref from_index,
                size: ref length,
            } => {
                self.explore_bval(parent_key, memory, from_index);
                self.explore_bval(parent_key, memory, to_index);
                self.explore_bval(parent_key, memory, length);
                self.explore_mval(parent_key, memory, *to);
                self.explore_mval(parent_key, memory, *from);
            }
            MemoryOperation::MemcopyUnlimited {
                parent: to,
                from,
                index: ref to_index,
                index_from: ref from_index,
            } => {
                self.explore_bval(parent_key, memory, from_index);
                self.explore_bval(parent_key, memory, to_index);
                self.explore_mval(parent_key, memory, *to);
                self.explore_mval(parent_key, memory, *from);
            }
            MemoryOperation::Init => {}
        }
    }

    fn process_bval(&mut self, parent_key: TrackingKey, memory: &SymbolicMemory, val: &BVal) {
        match val.val() {
            Val256::FAdd(ref l, ref r)
            | Val256::FSub(ref l, ref r)
            | Val256::FMul(ref l, ref r)
            | Val256::FDiv(ref l, ref r)
            | Val256::FSDiv(ref l, ref r)
            | Val256::FMod(ref l, ref r)
            | Val256::FSMod(ref l, ref r)
            | Val256::FExp(ref l, ref r)
            | Val256::FAnd(ref l, ref r)
            | Val256::FOr(ref l, ref r)
            | Val256::FXor(ref l, ref r)
            | Val256::FLt(ref l, ref r)
            | Val256::FLe(ref l, ref r)
            | Val256::FSLt(ref l, ref r)
            | Val256::FEql(ref l, ref r)
            | Val256::FNEql(ref l, ref r)
            | Val256::FImplies(ref l, ref r)
            | Val256::FByteAt(ref l, ref r)
            | Val256::FByteExtract(ref l, ref r)
            | Val256::FAShr(ref l, ref r)
            | Val256::FLShr(ref l, ref r)
            | Val256::FShl(ref l, ref r) => {
                self.explore_bval(parent_key, memory, l);
                self.explore_bval(parent_key, memory, r);
            }
            Val256::FNot(ref v) => self.explore_bval(parent_key, memory, v),
            Val256::FITE(ref c, ref t, ref e) => {
                self.explore_bval(parent_key, memory, c);
                self.explore_bval(parent_key, memory, t);
                self.explore_bval(parent_key, memory, e);
            }
            Val256::FMLoad(mem, ref addr) | Val256::FSLoad(mem, ref addr) => {
                self.explore_mval(parent_key, memory, *mem);
                self.explore_bval(parent_key, memory, addr);
            }
            Val256::FCombine32(ref loads) => {
                for load in loads {
                    self.explore_bval(parent_key, memory, load);
                }
            }
            Val256::FSHA3(mem, ref offset, ref len) => {
                self.explore_mval(parent_key, memory, *mem);
                self.explore_bval(parent_key, memory, offset);
                self.explore_bval(parent_key, memory, len);
            }
            // nothing to do here, allready added the value in the previous interation
            Val256::FConst(_) | Val256::FConst8(_) | Val256::FVarRef(_) => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::se::expr::symbolic_memory::word_write;
    use crate::test_helpers::generate_test_graph;

    #[test]
    fn record_read_test() {
        let ins = vec![
            Instr::IPush(vec![0x00]), //addr
            Instr::IMLoad,
        ];

        let g = generate_test_graph(ins);

        let state_1 = &g.get_state_by_id(1);
        let state_2 = &g.get_state_by_id(2);
        let state_3 = &g.get_state_by_id(3);
        assert_eq!(true, state_1.reads.as_ref() == state_2.reads.as_ref());
        assert_eq!(false, state_2.reads.as_ref() == state_3.reads.as_ref());
    }

    #[test]
    fn filter_simple_constraints() {
        let g = generate_test_graph(vec![]);
        let mut state = g.get_state_by_id(1).clone();
        state.push_constraint(add(&var("test_1"), &const_usize(1)));
        state.push_constraint(const_usize(1));

        assert_eq!(add(&var("test_1"), &const_usize(1)), state.constraints[0]);

        // some env constraint
        assert_eq!(1, state.constraints.len());
    }

    #[test]
    fn simple_variable_tracking_test() {
        let memory = symbolic_memory::new_memory();
        let bval_1 = add(&var("test_1"), &var("test_2"));
        let bval_2 = add(&bval_1, &const_usize(0xAA));
        let constraints = vec![Arc::clone(&bval_1), Arc::clone(&bval_2)];
        let mut splitter = ConstraintSetSplitter::from_constraints(&memory, constraints);
        let key_1 = splitter
            .mapping
            .get(&TrackingVariable::bval(&bval_1))
            .unwrap();
        let key_2 = splitter
            .mapping
            .get(&TrackingVariable::bval(&bval_2))
            .unwrap();
        assert!(splitter.ut.unioned(*key_1, *key_2));
    }

    #[test]
    fn alias_variable_tracking_test() {
        let memory = symbolic_memory::new_memory();
        let bval_1 = add(&var("test_1"), &var("test_2"));
        let bval_2 = add(&var("test_3"), &const_usize(0xAA));
        let bval_3 = add(&var("test_1"), &const_usize(0xAA));
        let mut splitter = ConstraintSetSplitter::from_constraints(
            &memory,
            vec![
                Arc::clone(&bval_1),
                Arc::clone(&bval_2),
                Arc::clone(&bval_3),
            ],
        );
        let key_1 = splitter
            .mapping
            .get(&TrackingVariable::bval(&bval_1))
            .unwrap();
        let key_2 = splitter
            .mapping
            .get(&TrackingVariable::bval(&bval_2))
            .unwrap();
        let key_3 = splitter
            .mapping
            .get(&TrackingVariable::bval(&bval_3))
            .unwrap();

        assert!(!splitter.ut.unioned(*key_1, *key_2));
        assert!(splitter.ut.unioned(*key_1, *key_3));
        assert!(!splitter.ut.unioned(*key_2, *key_3));
    }

    #[test]
    fn memory_variable_tracking_test() {
        let mut memory = symbolic_memory::new_memory();
        let mem_1 = symbolic_memory::create_new_memory(
            &mut memory,
            "test_1".to_string(),
            MemoryType::Storage,
            None,
        );
        let load_1 = sload(&memory, mem_1, &var("var_1"));
        let mem_2 = symbolic_memory::create_new_memory(
            &mut memory,
            "test_2".to_string(),
            MemoryType::Storage,
            None,
        );
        let mem_2 = word_write(&mut memory, mem_2, &load_1, &const_usize(0x0));
        let load_2 = sload(&memory, mem_2, &var("var_2"));
        let mut splitter = ConstraintSetSplitter::from_constraints(
            &memory,
            vec![Arc::clone(&load_1), Arc::clone(&load_2)],
        );

        let key_1 = splitter
            .mapping
            .get(&TrackingVariable::bval(&load_1))
            .unwrap();
        let key_2 = splitter
            .mapping
            .get(&TrackingVariable::bval(&load_2))
            .unwrap();

        assert!(splitter.ut.unioned(*key_1, *key_2));
    }

    #[test]
    fn memory_variable_tracking_complex_test() {
        let mut memory = symbolic_memory::new_memory();
        let mem_1 = symbolic_memory::create_new_memory(
            &mut memory,
            "test_1".to_string(),
            MemoryType::Storage,
            None,
        );
        let load_1 = sload(&memory, mem_1, &var("var_1"));
        let mem_2 = symbolic_memory::create_new_memory(
            &mut memory,
            "test_2".to_string(),
            MemoryType::Storage,
            None,
        );
        let mem_2 = word_write(&mut memory, mem_2, &load_1, &const_usize(0x0));
        let mem_2 = word_write(&mut memory, mem_2, &const_usize(0x0), &const_usize(0x0));
        let mem_2 = word_write(&mut memory, mem_2, &const_usize(0x1), &const_usize(0x0));
        let mem_2 = word_write(&mut memory, mem_2, &load_1, &const_usize(0x0));
        let load_2 = sload(&memory, mem_2, &var("var_2"));

        let mut splitter = ConstraintSetSplitter::from_constraints(
            &memory,
            vec![Arc::clone(&load_1), Arc::clone(&load_2)],
        );

        let key_1 = splitter
            .mapping
            .get(&TrackingVariable::bval(&load_1))
            .unwrap();
        let key_2 = splitter
            .mapping
            .get(&TrackingVariable::bval(&load_2))
            .unwrap();

        assert!(splitter.ut.unioned(*key_1, *key_2));
    }

    #[test]
    fn disjoint_sets_variable_tracking_test() {
        let memory = symbolic_memory::new_memory();
        let bval_1 = add(&var("test_1"), &var("test_2"));
        let bval_2 = add(&var("test_3"), &const_usize(0xAA));
        let bval_3 = add(&var("test_1"), &const_usize(0xAA));
        let mut splitter = ConstraintSetSplitter::from_constraints(
            &memory,
            vec![
                Arc::clone(&bval_1),
                Arc::clone(&bval_2),
                Arc::clone(&bval_3),
            ],
        );
        let correct = vec![vec![bval_2], vec![bval_1, bval_3]];
        assert_eq!(splitter.disjoint_sets(), correct);
    }
}
