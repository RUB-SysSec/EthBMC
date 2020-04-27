use std::sync::Arc;

use crate::bytecode::Instr;
use crate::disasm::Disasm;
use crate::se::env::Env;
use crate::se::expr::solver::Solvers;
use crate::se::expr::symbolic_memory;
use crate::se::symbolic_analysis::{Context, CONFIG};
use crate::se::symbolic_graph::SymbolicGraph;
use crate::se::symbolic_state::SeState;

pub fn generate_test_graph(ins: Vec<Instr>) -> SymbolicGraph {
    let mut env = Env::new();
    let mut memory = symbolic_memory::new_memory();

    let attacker = env.new_attacker_account(&mut memory);
    let victim = env.new_victim_account(&mut memory, &vec![]);
    let _hijack = env.new_hijack_account(&mut memory);
    let inital_tx = env.new_attacker_tx(&mut memory, attacker, victim);

    let dasm = Disasm::new(ins);

    let config = CONFIG.read().unwrap().clone();

    let initial_storage = env.get_account(&victim).storage;
    let context = Context::new(
        config,
        dasm,
        initial_storage,
        Solvers::Yice {
            count: num_cpus::get(),
            timeout: 120_000,
        },
    );
    let state = SeState::new(
        Arc::new(context),
        Arc::new(memory),
        &Arc::new(env),
        victim,
        inital_tx,
    );
    let mut g = SymbolicGraph::new(state);

    g.analyze_graph();
    g
}

pub fn generate_test_state() -> SeState {
    let mut env = Env::new();
    let mut memory = symbolic_memory::new_memory();

    let attacker = env.new_attacker_account(&mut memory);
    let victim = env.new_victim_account(&mut memory, &vec![]);
    let _hijack = env.new_hijack_account(&mut memory);
    let inital_tx = env.new_attacker_tx(&mut memory, attacker, victim);

    let dasm = Disasm::new(vec![]);

    let config = CONFIG.read().unwrap().clone();

    let initial_storage = env.get_account(&victim).storage;
    let context = Context::new(
        config,
        dasm,
        initial_storage,
        Solvers::Yice {
            count: num_cpus::get(),
            timeout: 120_000,
        },
    );
    SeState::new(
        Arc::new(context),
        Arc::new(memory),
        &Arc::new(env),
        victim,
        inital_tx,
    )
}
