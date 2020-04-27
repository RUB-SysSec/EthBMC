use std::{fmt, sync::Arc};

use crossbeam::queue::SegQueue;

use crate::se::expr::{
    boolector::BoolectorInstance, bval::BVal, formel_builder::SmtLib2Builder, yice::YiceInstance,
    z3::Z3Instance,
};

pub trait Solver: Send {
    /// Add fomula(e) to solver instance
    fn push_formula(&mut self, formula: &str);

    /// Check if the pushed formula is satisfiable
    // this also allows mutable access since this is needed to communicate with the underlying
    // process in most cases
    fn check_sat(&mut self) -> bool;

    /// Check if the pushed formula is satisfiable and return a model for the given variable
    fn get_value(&mut self, value: &str) -> Option<BVal>;

    /// Check if the pushed formula is satisfiable and return a model for the given variables
    fn get_values(&mut self, values: &[String]) -> Option<Vec<BVal>>;

    /// Reset the solver instance
    fn reset(&mut self);
}

pub struct SolverHandle<'a> {
    worker: Option<Box<dyn Solver>>,
    pool: &'a SolverPool,
}

impl<'a> SolverHandle<'a> {
    pub fn check_sat(&mut self) -> bool {
        self.as_mut().check_sat()
    }

    pub fn get_value(&mut self, value: &str) -> Option<BVal> {
        self.as_mut().get_value(value)
    }
    pub fn get_values(&mut self, values: &[String]) -> Option<Vec<BVal>> {
        self.as_mut().get_values(values)
    }

    // blocking call
    pub fn initialize_from_formel_builder(&mut self, builder: &SmtLib2Builder) {
        let worker = self.worker.as_mut().unwrap();

        for def in builder.defs() {
            worker.push_formula(def);
        }
        for assert in builder.asserts() {
            worker.push_formula(assert);
        }
    }

    fn as_mut(&mut self) -> &mut Box<dyn Solver> {
        self.worker.as_mut().unwrap()
    }
}

// When droping the handle reset z3 and add it back to the pool
impl<'a> Drop for SolverHandle<'a> {
    fn drop(&mut self) {
        let mut worker = self.worker.take().expect("Solver incorrectly closed");
        worker.reset();

        self.pool.add_worker(worker);
    }
}

pub struct SolverPool {
    queue: SegQueue<Box<dyn Solver>>,
}

impl fmt::Debug for SolverPool {
    fn fmt(&self, _f: &mut fmt::Formatter) -> fmt::Result {
        Ok(())
    }
}

pub enum Solvers {
    Initialized(Arc<SolverPool>),
    Z3 { count: usize, timeout: usize },
    Boolector { count: usize, timeout: usize },
    Yice { count: usize, timeout: usize },
}

pub fn create_pool(choice: Solvers) -> Arc<SolverPool> {
    match choice {
        Solvers::Initialized(pool) => pool,
        Solvers::Z3 { count, timeout } => Arc::new(z3_pool_with_workers(count, timeout)),
        Solvers::Boolector { count, timeout } => {
            Arc::new(boolector_pool_with_workers(count, timeout))
        }
        Solvers::Yice { count, timeout } => Arc::new(yice_pool_with_workers(count, timeout)),
    }
}

fn z3_pool_with_workers(count: usize, timeout: usize) -> SolverPool {
    let pool = SolverPool::new();

    for _ in 0..count {
        let worker = Box::new(Z3Instance::new(timeout));
        pool.add_worker(worker)
    }

    pool
}

fn boolector_pool_with_workers(count: usize, timeout: usize) -> SolverPool {
    let pool = SolverPool::new();

    for _ in 0..count {
        let worker = Box::new(BoolectorInstance::new(timeout));
        pool.add_worker(worker)
    }

    pool
}

fn yice_pool_with_workers(count: usize, timeout: usize) -> SolverPool {
    let pool = SolverPool::new();

    for _ in 0..count {
        let worker = Box::new(YiceInstance::new(timeout));
        pool.add_worker(worker)
    }

    pool
}

impl SolverPool {
    fn new() -> Self {
        let queue = SegQueue::new();
        SolverPool { queue }
    }

    fn add_worker(&self, worker: Box<dyn Solver>) {
        self.queue.push(worker)
    }

    pub fn initialize_from_formel_builder(&self, builder: &SmtLib2Builder) -> SolverHandle {
        let worker = {
            let worker;
            loop {
                match self.queue.pop() {
                    Ok(w) => {
                        worker = Some(w);
                        break;
                    }
                    Err(_) => (),
                }
            }
            worker
        };
        let mut handle = SolverHandle {
            worker: worker,
            pool: self,
        };
        handle.initialize_from_formel_builder(builder);
        handle
    }
}
