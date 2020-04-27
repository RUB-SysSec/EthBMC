#![feature(test)]
extern crate test;

#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate bitflags;
#[macro_use]
extern crate crossbeam_channel;
#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate log;

extern crate clap;
extern crate crossbeam;
extern crate ena;
extern crate ethereum_newtypes;
extern crate evmexec;
extern crate hexdecode;
extern crate num_cpus;
extern crate parity_connector;
extern crate petgraph;
extern crate rand;
extern crate rayon;
extern crate regex;
extern crate subprocess;
extern crate tiny_keccak;
extern crate uint;
extern crate yaml_rust;

mod bytecode;
mod disasm;
mod se;

#[cfg(test)]
mod test_helpers;

use std::{
    collections::HashSet,
    fmt,
    iter::FromIterator,
    sync::{Arc, Mutex},
    time::Duration,
};

use clap::{App, Arg};
use ethereum_newtypes::{Address, Bytes, WU256};
use parity_connector::BlockSelector;
use rayon::prelude::*;
use time::PreciseTime;

use crate::se::{
    env::{AccountId, GLOBAL_COVERAGE_MAP},
    expr::{bval::BitVec, formel_builder::KECCAK_STATS},
    symbolic_analysis::{Analysis, AnalysisMode},
};

pub use crate::se::{
    env::{self, Env, SeEnviroment},
    expr::solver::{create_pool, SolverPool, Solvers},
    symbolic_analysis::{Attack, AttackType, ExplorationResult, ParityInfo, SeConfig, CONFIG},
    symbolic_state::{Flags, ResultState},
};

use crate::bytecode::Instr;

#[derive(Serialize, Deserialize)]
pub struct AnalysisResult {
    pub address: Address,
    pub blocks: Vec<usize>,

    pub code_length: u32,

    pub executed: bool,
    pub copy_instructions: bool,

    pub attacks: Option<Vec<Attack>>,
    pub precompiled_contracts: Option<Vec<PrecompiledContracts>>,
    pub loaded_accounts: Option<Vec<LoadedAccount>>,
    pub analysis_time: Option<Duration>,
}

#[derive(Serialize, Deserialize)]
pub enum AnalysisSuccess {
    Success(AnalysisResult),
    Failure(String),
    Timeout,
}

#[derive(Serialize, Deserialize)]
pub struct TimeoutAnalysis {
    pub address: Address,
    pub timeout: Duration,
}

pub fn symbolic_analysis(se_env: SeEnviroment, config: SeConfig, pool: Solvers) -> AnalysisResult {
    let mut analysis_result = AnalysisResult {
        address: BitVec::as_bigint(&se_env.env.get_account(&se_env.to).addr)
            .unwrap()
            .into(),
        blocks: vec![],
        code_length: 0,
        executed: false,
        copy_instructions: false,
        precompiled_contracts: None,
        attacks: None,
        loaded_accounts: None,
        analysis_time: None,
    };
    let start = PreciseTime::now();
    update_analysis_result_from_env(&mut analysis_result, &se_env.env);
    let mut analysis = Analysis::from_se_env(se_env, config.clone(), pool);

    let attacker = analysis.from();
    let victim = analysis.to();
    let code = analysis.code_to_be_executed();

    // we double disassemble the code here but w/e
    // this call also sets all the stats we can gather statically
    if !analyze_contract_code(&code, &mut analysis_result) {
        analysis_result.analysis_time = Some(start.to(PreciseTime::now()).to_std().unwrap());
        return analysis_result;
    }

    if CONFIG.read().unwrap().dgraph {
        analysis.dump_debug_graph();
        analysis_result.analysis_time = Some(start.to(PreciseTime::now()).to_std().unwrap());
        return analysis_result;
    }
    info!("=========================================================");
    info!("Starting first round.");
    info!("=========================================================");
    analysis.symbolic_round();
    let exp_res = analysis.exploration_result();

    if exp_res.found_attacks() {
        if cfg!(feature = "stats") {
            let handle = KECCAK_STATS.lock().unwrap();
            info!("Stats at the end of the analysis: {:?}", *handle);
        }

        analysis_result.analysis_time = Some(start.to(PreciseTime::now()).to_std().unwrap());
        return update_analysis_result(analysis_result, exp_res);
    }

    let mut states;
    states = exp_res.end_states();

    let mut counter = 2; // first round done
    let results = Mutex::new(vec![]);
    while counter <= CONFIG.read().unwrap().message_bound
        && !states.is_empty()
        && results.lock().unwrap().is_empty()
    {
        // states has to be non emtpy here
        assert!(!states.is_empty());

        // update all environments, i.e., simulate block transition
        for state in &mut states {
            let new_env = Arc::new(env::Env::from_old_env(&state.env));
            state.env = new_env;
        }

        info!("=========================================================");
        info!("Starting round {}", counter);
        info!("Continue analysis with {} initial states.", states.len());
        info!("=========================================================");
        let anas = Mutex::new(vec![]);
        states.into_par_iter().for_each(|s| {
            debug!("\n\n\nRun with input:\n{:?}\n", s);
            let memory = Arc::clone(&s.memory);
            let mut ana = Analysis::from_result_state(
                &code.clone(),
                &attacker,
                &victim,
                config.clone(),
                s,
                AnalysisMode::Execution,
                memory,
            );
            ana.symbolic_round();
            anas.lock().unwrap().push(ana);
        });

        let mut new_states = Vec::new();
        for ana in anas.into_inner().unwrap() {
            let exp_res = ana.exploration_result();
            if exp_res.found_attacks() {
                results.lock().unwrap().push(exp_res);
            } else {
                new_states.append(&mut exp_res.end_states());
            }
        }
        states = new_states;
        counter += 1;
    }

    let results = results.into_inner().unwrap();

    if cfg!(feature = "stats") {
        let handle = KECCAK_STATS.lock().unwrap();
        info!("Stats at the end of the analysis: {:?}", *handle);
    }

    if results.is_empty() {
        // update coverage
        if let Some(ref mut accounts) = analysis_result.loaded_accounts {
            for acc in accounts {
                if acc.code.is_some() {
                    let coverage = Some(
                        GLOBAL_COVERAGE_MAP
                            .lock()
                            .get(&AccountId(acc.id))
                            .unwrap()
                            .coverage(),
                    );
                    acc.code_coverage = coverage;
                }
            }
        }

        analysis_result.analysis_time = Some(start.to(PreciseTime::now()).to_std().unwrap());
        return analysis_result;
    }

    // collect results
    for res in results {
        analysis_result = update_analysis_result(analysis_result, res);
    }

    analysis_result.analysis_time = Some(start.to(PreciseTime::now()).to_std().unwrap());
    analysis_result
}

pub fn arguments<'a>(app: App<'a, 'a>) -> App<'a, 'a> {
    app
        .arg(Arg::with_name("block").long("block").takes_value(true).help("The blocknumber to evaluate, defaults to latest block. Note you will need an archive node for anaylzing blocks which are not the latest."))
        .arg(Arg::with_name("loop_bound").long("loop-bound").short("b").takes_value(true).help("Set bound for loops"))
        .arg(Arg::with_name("call_bound").long("call-bound").short("c").takes_value(true).help("Set bound for calls"))
        .arg(Arg::with_name("message_bound").long("message-bound").short("m").takes_value(true).help("Set bound for message iteration"))
        .arg(Arg::with_name("solver-timeout").long("solver-timeout").takes_value(true).help("Set solver timeout in milliseconds"))
        .arg(Arg::with_name("cores").long("cores").takes_value(true).help("Set the amount of cores the se can use"))
        // Optimizations
        .arg(Arg::with_name("disable_optimizations").long("no-optimizations").help("Disable all optimizations").long_help("Disables all optimizations. This will disable support for keccak with concrete value as well as constant folding which is on by default otherwise."))
        .arg(Arg::with_name("concrete_copy").long("concrete-copy").help("Use concrete calldatacopy"))
        // Analysis
        .arg(Arg::with_name("debug_graph").short("d").long("debug-grap").help("Dump debug graph after analysis"))
        .arg(Arg::with_name("no_verify").long("no-verify").help("Skip verification phase."))
        .arg(Arg::with_name("dump-solver").long("dump-solver").help("Dump all solver queries to ./queries"))
        .arg(Arg::with_name("ip").long("ip").takes_value(true).help("The ip of a running node."))
        .arg(Arg::with_name("port").long("port").takes_value(true).help("The port of a running node."))
}

pub fn set_global_config(matches: &clap::ArgMatches) {
    // set config
    let mut config = CONFIG.write().unwrap();

    // always use thee optimizations
    config.arithmetic_simplification = true;
    config.concrete_load = true;

    if let Some(b) = matches.value_of("loop_bound") {
        config.loop_bound = b.parse().expect("Incorrect bound parameter supplied!");
    }
    if let Some(b) = matches.value_of("call_bound") {
        config.call_depth_limit = b.parse().expect("Incorrect bound parameter supplied!");
    }
    if let Some(b) = matches.value_of("message_bound") {
        config.message_bound = b.parse().expect("Incorrect bound parameter supplied!");
    }
    if let Some(b) = matches.value_of("cores") {
        config.cores = b.parse().expect("Incorrect bound parameter supplied!");
    }
    if let Some(b) = matches.value_of("solver-timeout") {
        config.solver_timeout = b.parse().expect("Incorrect solver parameter supplied!");
    } else {
        config.solver_timeout = 120_000;
    }
    if matches.is_present("concrete_copy") {
        config.concrete_copy = true;
    }
    if matches.is_present("no_verify") {
        config.no_verify = true;
    }
    if matches.is_present("debug_graph") {
        config.dgraph = true;
    }
    if matches.is_present("dump-solver") {
        config.dump_solver = true;
    }
    if matches.is_present("disable_optimizations") {
        config.disable_optimizations = true;
        config.arithmetic_simplification = false;
        config.concrete_load = false;
    }
    let blocknumber = if let Some(b) = matches.value_of("block") {
        BlockSelector::Specific(b.parse().expect("Could not parse blocknumber"))
    } else {
        BlockSelector::Latest
    };
    match (matches.value_of("ip"), matches.value_of("port")) {
        (Some(ip), Some(port)) => {
            let port = port.parse().expect("Incorrect port supplied!");
            config.parity = Some(ParityInfo(ip.to_string(), port, blocknumber));
        }
        (Some(ip), None) => {
            let port = 8545;
            config.parity = Some(ParityInfo(ip.to_string(), port, blocknumber));
        }
        _ => {}
    }
    debug!("Using {:?} for analysis", config);
}

fn update_analysis_result_from_env(ana: &mut AnalysisResult, env: &Env) {
    if let Some(ref contracts) = env.precompiled_contracts {
        ana.precompiled_contracts = Some(contracts.iter().cloned().collect());
    }
    if let Some(ref accounts) = env.loaded_accounts {
        ana.loaded_accounts = Some(
            accounts
                .iter()
                .map(|id| {
                    let acc_ref = env.get_account(id);
                    let code_coverage = if let Some(c) = GLOBAL_COVERAGE_MAP.lock().get(id) {
                        Some(c.coverage())
                    } else {
                        None
                    };
                    LoadedAccount {
                        id: acc_ref.id.0,
                        address: BitVec::as_bigint(&acc_ref.addr).unwrap().into(),
                        balance: acc_ref.initial_balance.as_ref().cloned(),
                        code: acc_ref.code().cloned().map(|v| v.into()),
                        code_length: acc_ref.get_codesize() as u32,
                        initial_storage: acc_ref
                            .initial_storage
                            .as_ref()
                            .cloned()
                            .unwrap_or_else(Vec::new),
                        code_coverage,
                    }
                })
                .collect(),
        );
    }

    for block in &env.blocks {
        if let Some(number) = block.blocknumber {
            ana.blocks.push(number);
        }
    }
}

fn update_analysis_result(mut ana: AnalysisResult, res: ExplorationResult) -> AnalysisResult {
    // update attacks
    if let Some(found_attacks) = res.result {
        if let Some(attacks) = ana.attacks {
            let set: HashSet<Attack> = HashSet::from_iter(found_attacks.into_iter());
            ana.attacks = Some(
                set.union(&HashSet::from_iter(attacks.into_iter()))
                    .cloned()
                    .collect(),
            );
        } else {
            ana.attacks = Some(found_attacks);
        }
    }
    // update precompiled_contracts
    if let Some(mut found_contracts) = res.precompiled_contracts {
        if let Some(contracts) = ana.precompiled_contracts {
            for con in contracts {
                found_contracts.insert(con);
            }
            ana.precompiled_contracts = Some(found_contracts.into_iter().collect());
        } else {
            ana.precompiled_contracts = Some(found_contracts.into_iter().collect());
        }
    }

    // update loaded accounts
    if let Some(mut found_accounts) = res.loaded_accounts {
        if let Some(accounts) = ana.loaded_accounts {
            for acc in accounts {
                found_accounts.insert(acc);
            }
        }
        ana.loaded_accounts = Some(found_accounts.into_iter().collect());

        if let Some(ref mut accounts) = ana.loaded_accounts {
            for acc in accounts {
                if acc.code.is_some() {
                    let coverage = Some(
                        GLOBAL_COVERAGE_MAP
                            .lock()
                            .get(&AccountId(acc.id))
                            .unwrap()
                            .coverage(),
                    );
                    acc.code_coverage = coverage;
                }
            }
        }
    }

    if let Some(blocks) = res.blocks {
        ana.blocks = blocks;
    }

    ana
}

fn seperators(f: &mut fmt::Formatter) -> fmt::Result {
    writeln!(
        f,
        "========================================================="
    )?;
    writeln!(
        f,
        "========================================================="
    )
}
impl fmt::Display for AnalysisResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        seperators(f)?;
        writeln!(f, "Analysis Result for account {:x}:", self.address)?;
        seperators(f)?;
        writeln!(
            f,
            "Finished analysis in {}s!",
            self.analysis_time.as_ref().unwrap().as_secs()
        )?;
        writeln!(
            f,
            "General statistics:\n\tAccount code size: {}",
            self.code_length,
        )?;
        writeln!(f, "\tAnalysis conducted at block(s): {:?}", self.blocks)?;
        if !self.executed {
            writeln!(
                f,
                "Account does not contain vulnerable instructions, did not continue analysis!"
            )?;
            return seperators(f);
        }

        if let Some(ref contracts) = self.precompiled_contracts {
            writeln!(
                f,
                "\n\tFound {} precompiled contract call(s):",
                contracts.len()
            )?;
            for c in contracts {
                writeln!(f, "\t\t- {}", c)?;
            }
        }

        if let Some(ref accounts) = self.loaded_accounts {
            writeln!(
                f,
                "\n\tLoaded {} account(s) form the blockchain:",
                accounts.len()
            )?;
            for (i, a) in accounts.iter().enumerate() {
                writeln!(f, "\t\tAccount {}", i + 1)?;
                for line in format!("{}", a).lines() {
                    writeln!(f, "\t\t{}", line)?;
                }
            }
        }
        seperators(f)?;
        if let Some(ref attacks) = self.attacks {
            writeln!(f, "Found {} attacks(s):", attacks.len())?;
            for a in attacks {
                writeln!(f, "{}", a)?;
            }
        } else {
            writeln!(f, "Could not find any attacks!")?;
        }
        seperators(f)?;
        Ok(())
    }
}

#[derive(Debug, Clone, Hash, PartialOrd, Ord, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrecompiledContracts {
    EcdsaRecover,
    Sha256,
    Ripemd160,
    Identity,
    ModularExponentiation,
    EcAddition,
    EcScalarMultiplikation,
    EcPairingEquation,
}

impl fmt::Display for PrecompiledContracts {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PrecompiledContracts::EcdsaRecover => write!(f, "ecdsa recover"),
            PrecompiledContracts::Sha256 => write!(f, "sha256"),
            PrecompiledContracts::Ripemd160 => write!(f, "ripemd160"),
            PrecompiledContracts::Identity => write!(f, "identity"),
            PrecompiledContracts::ModularExponentiation => write!(f, "modular exponentiation"),
            PrecompiledContracts::EcAddition => write!(f, "ec addition"),
            PrecompiledContracts::EcScalarMultiplikation => write!(f, "ec scalar multiplication"),
            PrecompiledContracts::EcPairingEquation => write!(f, "ec pairing equation"),
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct LoadedAccount {
    pub id: usize,
    pub address: Address,
    pub balance: Option<WU256>,

    pub code: Option<Bytes>,
    pub code_coverage: Option<f64>,
    pub code_length: u32,
    pub initial_storage: Vec<(WU256, WU256)>,
}

impl std::hash::Hash for LoadedAccount {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.address.hash(state);
        self.balance.hash(state);
        self.code.hash(state);
        self.code_length.hash(state);
        self.initial_storage.hash(state);
    }
}

impl std::cmp::Eq for LoadedAccount {}

impl std::cmp::PartialEq for LoadedAccount {
    fn eq(&self, other: &LoadedAccount) -> bool {
        self.address == other.address
            && self.balance == other.balance
            && self.code == other.code
            && self.code_length == other.code_length
            && self.initial_storage == other.initial_storage
    }
}

impl std::cmp::PartialOrd for LoadedAccount {
    fn partial_cmp(&self, other: &LoadedAccount) -> Option<std::cmp::Ordering> {
        Some(self.address.0.cmp(&other.address.0))
    }
}

impl std::cmp::Ord for LoadedAccount {
    fn cmp(&self, other: &LoadedAccount) -> std::cmp::Ordering {
        self.address.0.cmp(&other.address.0)
    }
}

impl fmt::Display for LoadedAccount {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Loaded account:\n=======\nAddress: {:x}", self.address,)?;

        if let Some(ref b) = self.balance {
            writeln!(f, "Balance: {:x}", b)?;
        }
        if let Some(ref c) = self.code {
            writeln!(f, "Code: {}\nCode length: {}", c, self.code_length,)?;
        }
        if let Some(ref cov) = self.code_coverage {
            writeln!(f, "Code covered: {:.2}%", 100.0 * cov)?;
        }
        if !self.initial_storage.is_empty() {
            writeln!(f, "Initial Storage:")?;
        }
        for (addr, value) in &self.initial_storage {
            writeln!(f, "\t{:x} : {:x}", addr, value)?;
        }
        Ok(())
    }
}

fn analyze_contract_code(code: &[u8], res: &mut AnalysisResult) -> bool {
    let disasm = disasm::Disasm::from_raw(&code);
    res.code_length = code.len() as u32;

    for op in disasm.opcodes() {
        // if we have not found any copy/vulnerable instruction keep analysing
        if !res.executed {
            res.executed = true;
        }
        if !res.copy_instructions {
            res.copy_instructions = copy_instructions(&op);
        }
    }

    res.executed
}

// codecopy and extcodecopy are also copy instructions, however we only support them in a constant
// fashion
fn copy_instructions(op: &Instr) -> bool {
    match op {
        Instr::ICallDataCopy
        | Instr::IRDataCopy
        | Instr::ICall
        | Instr::IStaticCall
        | Instr::ICallCode
        | Instr::IDelegateCall => true,
        _ => false,
    }
}
