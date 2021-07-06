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

    fn retrieve_worker(&self) -> Option<Box<dyn Solver>> {
        return {
            let worker;
            loop {
                match self.queue.pop() {
                    Some(w) => {
                        worker = Some(w);
                        break;
                    }
                    None => (),
                }
            }
            worker
        };
    }

    pub fn initialize_from_formel_builder(&self, builder: &SmtLib2Builder) -> SolverHandle {
        let worker = self.retrieve_worker();

        let mut handle = SolverHandle {
            worker: worker,
            pool: self,
        };
        handle.initialize_from_formel_builder(builder);
        handle
    }

    // only available for testing
    #[cfg(test)]
    pub fn solver_handle(&self) -> SolverHandle {
        let worker = self.retrieve_worker();

        let mut handle = SolverHandle {
            worker: worker,
            pool: self,
        };
        handle
    }
}

#[cfg(test)]
mod tests {
    use super::{yice_pool_with_workers, SolverPool};

    const TEST_TIMEOUT: usize = 120;

    #[test]
    fn yice_solver_pool() {
        let f_false = String::from(
            "(declare-const a (_ BitVec 256))
        (declare-const b (_ BitVec 256))
        (assert (= a (_ bv10 256)))
        (assert (= b (_ bv11 256)))
        (assert (= a b))",
        );

        let mut pool = yice_pool_with_workers(5, TEST_TIMEOUT);
        for i in 0..10 {
            let mut handle = pool.solver_handle();
            {
                let mut yice = handle.worker.take().unwrap();
                for line in f_false.lines() {
                    yice.push_formula(line);
                }
                handle.worker.replace(yice);
            };
            assert_eq!(false, handle.check_sat());
        }
    }
}
