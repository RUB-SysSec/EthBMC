use std::{
    collections::HashSet,
    fmt,
    fs::File,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, Mutex, RwLock,
    },
};

use ethereum_newtypes::{Address, Bytes, Hash, WU256};
use evmexec::{
    evm::{Evm, EvmInput},
    evmtrace::Instruction,
    genesis,
};
use num_cpus;
use parity_connector::BlockSelector;
use rayon::prelude::*;
use uint::U256;

use crate::bytecode::Instr;
use crate::disasm::Disasm;
use crate::se::{
    env::{AccountId, Env, SeEnviroment, TxId, GLOBAL_COVERAGE_MAP},
    expr::{
        bval::*,
        solver::{create_pool, SolverPool, Solvers},
        symbolic_memory::{MVal, SymbolicMemory},
    },
    symbolic_graph::SymbolicGraph,
    symbolic_state::{Flags, HaltingReason, ResultState, SeState},
};
use crate::{LoadedAccount, PrecompiledContracts};

#[cfg(test)]
use crate::se::expr::symbolic_memory::{self, MemoryType};

lazy_static! {
    pub static ref CONFIG: RwLock<SeConfig> = RwLock::new(SeConfig::new());
}

#[derive(Clone, Debug)]
pub struct SeConfig {
    /// General Config Options
    ///
    /// Sets the loop upper bound for loop unrolling. Standard is to unroll loops till the 5th
    /// iteration.
    pub loop_bound: usize,

    /// Sets the call depth upper limit for bounded call checking
    pub call_depth_limit: usize,

    /// Sets the message bound for exploration. Standard is 5 iterations.
    pub message_bound: usize,

    /// Sets the solver timeout. Standard is 2 Minutes.
    pub solver_timeout: usize,

    /// Optimizazions
    ///
    /// One can set a this flag to disable all optimizazions. This includes constant folding,
    /// otherwise constant folding is turned on by default. This will overwrite all other
    /// optimizaion flags.
    pub disable_optimizations: bool,

    /// Arithmetic simplification, i.e. rewrites like 3*x*3 = 9*x and x + 0 = x.
    pub arithmetic_simplification: bool,

    /// Concretely load values from memory if possible.
    pub concrete_load: bool,

    /// Set this flag to use a concrete load for calldatacopy
    pub concrete_copy: bool,

    /// Analysis Options
    /// Set this flag to dump the debug graph.
    pub dgraph: bool,

    /// Disable the verification phase
    pub no_verify: bool,

    /// Dump solver queries
    pub dump_solver: bool,

    /// (Optional) The ip and port of an parity instance
    pub parity: Option<ParityInfo>,

    /// The number of CPU cores to use
    pub cores: usize,
}

#[derive(Clone, Debug)]
pub struct ParityInfo(pub String, pub isize, pub BlockSelector);

impl Default for SeConfig {
    fn default() -> Self {
        SeConfig::new()
    }
}

impl SeConfig {
    pub fn new() -> Self {
        let number_cpu = if num_cpus::get() <= 4 {
            num_cpus::get()
        } else {
            // one core for orchestration
            num_cpus::get() - 1
        };

        Self {
            disable_optimizations: false,
            concrete_load: false,
            arithmetic_simplification: false,
            concrete_copy: false,
            loop_bound: 5,
            call_depth_limit: 3,
            message_bound: 5,
            dgraph: false,
            no_verify: false,
            dump_solver: false,
            solver_timeout: 120_000,
            parity: None,
            cores: number_cpu,
        }
    }
}

pub struct Context {
    /// The config for the current execution
    config: SeConfig,

    /// The pool of solver processes for the current execution
    solver_pool: Arc<SolverPool>,

    /// The generator for unique state ids
    id_generator: AtomicUsize,

    /// The disassembled code being executed
    disasm: Disasm,

    /// The initial storage for the executed account, saved in case we reach a REVERT statement
    initial_storage: MVal,
}

impl Context {
    pub fn new(config: SeConfig, disasm: Disasm, initial_storage: MVal, solvers: Solvers) -> Self {
        let solver_pool = create_pool(solvers);
        let id_generator = AtomicUsize::new(1);
        Self {
            config,
            solver_pool,
            id_generator,
            disasm,
            initial_storage,
        }
    }

    #[cfg(test)]
    pub fn test() -> Self {
        let config = SeConfig::new();
        let disasm = Disasm::new(vec![]);
        let mut memory = symbolic_memory::new_memory();
        let initial_storage = symbolic_memory::create_new_memory(
            &mut memory,
            "test".to_string(),
            MemoryType::Storage,
            None,
        );
        Self::new(
            config,
            disasm,
            initial_storage,
            Solvers::Yice {
                count: num_cpus::get(),
                timeout: 120_000,
            },
        )
    }

    pub fn config(&self) -> &SeConfig {
        &self.config
    }

    // relaxed ordering, since we only care about uniqueness not ordering
    pub fn next_id(&self) -> usize {
        self.id_generator.fetch_add(1, Ordering::Relaxed)
    }

    pub fn instruction_size(&self, pc: usize) -> Option<usize> {
        self.disasm.get_size(pc)
    }

    pub fn instruction(&self, pc: usize) -> Option<Instr> {
        self.disasm.get(pc)
    }

    pub fn is_jump_target(&self, pc: usize) -> bool {
        self.disasm.is_jump_target(pc)
    }

    pub fn jump_targets(&self) -> &HashSet<usize> {
        self.disasm.jump_targets()
    }

    pub fn initial_storage(&self) -> MVal {
        self.initial_storage
    }

    pub fn solver_pool(&self) -> Arc<SolverPool> {
        Arc::clone(&self.solver_pool)
    }
}

pub enum AnalysisMode {
    Execution,
    Call(TxId),
}

impl AnalysisMode {
    fn is_exeution(&self) -> bool {
        if let AnalysisMode::Execution = self {
            true
        } else {
            false
        }
    }

    fn is_call(&self) -> bool {
        if let AnalysisMode::Call(_) = self {
            true
        } else {
            false
        }
    }
}

pub struct Analysis {
    graph: SymbolicGraph,
    from: AccountId,
    to: AccountId,
    mode: AnalysisMode,
    end_states: Option<Vec<SeState>>,
    blocks: Option<Vec<usize>>,
}

impl Analysis {
    fn new(
        code: &[u8],
        env: Arc<Env>,
        initial_tx: &TxId,
        from: AccountId,
        to: AccountId,
        init_state: Option<ResultState>,
        config: SeConfig,
        solvers: Solvers,
        mode: AnalysisMode,
        memory: Arc<SymbolicMemory>,
    ) -> Self {
        let initial_storage = env.get_account(&to).storage;
        let blocks = env.blocknumbers.clone();
        let context = Arc::new(Context::new(
            config,
            Disasm::from_raw(code),
            initial_storage,
            solvers,
        ));
        let graph = Self::create_graph(env, initial_tx, &to, init_state, context, memory);
        let end_states = None;

        Self {
            graph,
            from,
            to,
            mode,
            end_states,
            blocks,
        }
    }

    pub fn from_se_env(se_env: SeEnviroment, config: SeConfig, solvers: Solvers) -> Self {
        let SeEnviroment {
            mut env,
            from,
            to,
            mut memory,
        } = se_env;
        let code = env.get_account(&to).code().cloned().unwrap();
        let initial_tx = env.new_attacker_tx(Arc::make_mut(&mut memory), from, to);
        Self::new(
            &code,
            Arc::new(env),
            &initial_tx,
            from,
            to,
            None,
            config,
            solvers,
            AnalysisMode::Execution,
            memory,
        )
    }

    pub fn from_result_state(
        code: &[u8],
        from: &AccountId,
        to: &AccountId,
        config: SeConfig,
        state: ResultState,
        mode: AnalysisMode,
        mut memory: Arc<SymbolicMemory>,
    ) -> Self {
        let mut env = Arc::clone(&state.env);
        let initial_tx;
        {
            let memory_ptr = Arc::make_mut(&mut memory);
            initial_tx = match &mode {
                AnalysisMode::Execution => {
                    Arc::make_mut(&mut env).new_attacker_tx(memory_ptr, *from, *to)
                }
                AnalysisMode::Call(id) => *id,
            };
        }

        let solvers = Solvers::Initialized(Arc::clone(&state.solver_pool));

        Self::new(
            code,
            env,
            &initial_tx,
            *from,
            *to,
            Some(state),
            config,
            solvers,
            mode,
            memory,
        )
    }

    pub fn symbolic_round(&mut self) {
        assert!(self.mode.is_exeution());
        self.graph.analyze_graph();

        self.end_states = Some(self.graph.end_states());
    }

    pub fn exploration_result(mut self) -> ExplorationResult {
        assert!(self.end_states.is_some());
        let end_states = self.end_states.take().unwrap();
        info!(
            "Found {} potential attack states, analyzing...",
            end_states.len()
        );
        let result = Mutex::new(vec![]);
        let precompiled_contracts = Mutex::new(vec![]);
        let loaded_accounts = Mutex::new(vec![]);
        end_states
            .into_par_iter()
            .for_each(|potential_attack_state| {
                if let Some(ref contracts) = potential_attack_state.env.precompiled_contracts {
                    precompiled_contracts
                        .lock()
                        .unwrap()
                        .push(contracts.clone());
                }
                if let Some(ref accounts) = potential_attack_state.env.loaded_accounts {
                    {
                        let mut account_lock = loaded_accounts.lock().unwrap();
                        for id in accounts {
                            let acc_ref = potential_attack_state.env.get_account(id);
                            let code_coverage = if let Some(c) = GLOBAL_COVERAGE_MAP.lock().get(id)
                            {
                                Some(c.coverage())
                            } else {
                                None
                            };
                            let acc = LoadedAccount {
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
                            };
                            account_lock.push(acc);
                        }
                    }
                }

                self.analyze_state_for_attacks(potential_attack_state, &result);
            });
        let blocks = self.blocks;

        let result = result.into_inner().unwrap();
        let result = if result.is_empty() {
            None
        } else {
            Some(result)
        };

        let loaded_accounts = loaded_accounts.into_inner().unwrap();
        let loaded_accounts = if loaded_accounts.is_empty() {
            None
        } else {
            let mut set = HashSet::new();
            for account in loaded_accounts {
                set.insert(account);
            }
            Some(set)
        };

        let precompiled_contracts = precompiled_contracts.into_inner().unwrap();
        let precompiled_contracts = if precompiled_contracts.is_empty() {
            None
        } else {
            let mut set = HashSet::new();
            for contracts in precompiled_contracts {
                for c in contracts {
                    set.insert(c);
                }
            }
            Some(set)
        };

        let new_states = self
            .graph
            .end_states_storage()
            .iter()
            .map(|state| state.as_result_state())
            .collect();
        ExplorationResult {
            new_states,
            result,
            loaded_accounts,
            precompiled_contracts,
            blocks,
        }
    }

    pub fn execute_call(mut self) -> Vec<ResultState> {
        assert!(self.mode.is_call());
        self.graph.analyze_graph();
        self.graph
            .end_states()
            .iter()
            .map(|s| s.as_result_state())
            .collect()
    }

    fn analyze_state_for_attacks(
        &self,
        mut potential_attack_state: SeState,
        result: &Mutex<Vec<Attack>>,
    ) {
        let initial_state = &self.graph.initial_state();
        let attacker = &self.from;
        // if we know the owner variable of the vicitm account check if we changed it
        if let Some(ref index) = potential_attack_state.account().owner {
            {
                let mut check = potential_attack_state.clone();
                let initial_owner = sload(&check.memory, initial_state.account().storage, index);
                let final_owner = sload(&check.memory, check.account().storage, index);

                // find path were these are not equal
                check.push_constraint(neql(&initial_owner, &final_owner));

                if check.check_sat() {
                    if let Some(data) = self.generate_tx_datas(&check) {
                        if self
                            .verify_tx_owner(&check, &data, FVal::as_bigint(index).unwrap().into())
                            .is_some()
                        {
                            let attack = Attack {
                                txs: data,
                                attack_type: AttackType::CanChangeOwner,
                            };
                            result.lock().unwrap().push(attack);
                        }
                    } else {
                        debug!(
                            "Found attack, {}, but could not generate tx data!",
                            AttackType::CanChangeOwner
                        );
                    }
                }
            }
        }
        // check if we can suicide the contract
        if let Some(HaltingReason::Selfdestruct) = potential_attack_state.halting_reason {
            if let Some(data) = self.generate_tx_datas(&potential_attack_state) {
                if self
                    .verify_tx_suicide(&potential_attack_state, &data)
                    .is_some()
                {
                    let attack = Attack {
                        txs: data,
                        attack_type: AttackType::DeleteContract,
                    };
                    result.lock().unwrap().push(attack);
                }
            } else {
                debug!(
                    "Found attack, {}, but could not generate tx data!",
                    AttackType::DeleteContract
                );
            }
        }
        // check if we can hijack control flow
        if potential_attack_state
            .flags
            .contains(Flags::HIJACK_CONTROL_FLOW)
        {
            if let Some(data) = self.generate_tx_datas(&potential_attack_state) {
                if self
                    .verify_tx_hijack_control_flow(&potential_attack_state, &data)
                    .is_some()
                {
                    let attack = Attack {
                        txs: data,
                        attack_type: AttackType::HijackControlFlow,
                    };
                    result.lock().unwrap().push(attack);
                }
            } else {
                debug!(
                    "Found attack, {}, but could not generate tx data!",
                    AttackType::HijackControlFlow
                );
            }
        }
        // check if we can steal money
        let balance = Arc::clone(&potential_attack_state.env.get_account(attacker).balance);
        potential_attack_state.push_constraint(lt(
            &Arc::clone(
                initial_state
                    .env
                    .get_account(attacker)
                    .initial_attacker_balance
                    .as_ref()
                    .unwrap(),
            ),
            &balance,
        ));

        if potential_attack_state.check_sat() {
            if let Some(data) = self.generate_tx_datas(&potential_attack_state) {
                if self
                    .verify_tx_value_transfer(&potential_attack_state, &data)
                    .is_some()
                {
                    let attack = Attack {
                        txs: data,
                        attack_type: AttackType::StealMoney,
                    };
                    result.lock().unwrap().push(attack);
                } else {
                    debug!("Found a potential attack state, but could not verify it!");
                }
            } else {
                debug!(
                    "Found attack, {}, but could not generate tx data!",
                    AttackType::StealMoney
                );
            }
        }
    }

    fn create_graph(
        env: Arc<Env>,
        initial_tx: &TxId,
        victim: &AccountId,
        init_state: Option<ResultState>,
        context: Arc<Context>,
        memory: Arc<SymbolicMemory>,
    ) -> SymbolicGraph {
        let state = match init_state {
            Some(s) => SeState::from_result_state(
                s,
                Arc::clone(&context),
                memory,
                &env,
                *victim,
                *initial_tx,
            ),
            None => SeState::new(Arc::clone(&context), memory, &env, *victim, *initial_tx),
        };
        SymbolicGraph::new(state)
    }

    fn generate_tx_datas(&self, state: &SeState) -> Option<Vec<TxData>> {
        if let Some(data) = self.generate_tx_data(state) {
            return Some(data);
        }
        debug!("Could not generate tx data!");
        None
    }

    fn generate_tx_data(&self, state: &SeState) -> Option<Vec<TxData>> {
        let mut attack_data = vec![];
        for tx in &state.previous_tx {
            attack_data.push(self.concrete_input_data_for_tx(&state, &tx)?);
        }
        attack_data.push(self.concrete_input_data_for_tx(&state, &state.input_tx)?);
        Some(attack_data)
    }

    fn execute_concrete_evm(
        &self,
        state: &SeState,
        attack_data: &[TxData],
    ) -> Option<evmexec::evm::Execution> {
        let genesis: genesis::Genesis = (*state.env).clone().into();
        let mut evm: Evm = genesis.into();
        let sender: Address = BitVec::as_bigint(&state.env.get_account(&self.from).addr)
            .unwrap()
            .into();
        let receiver: Address = BitVec::as_bigint(&state.env.get_account(&self.to).addr)
            .unwrap()
            .into();

        let mut execution;
        for (
            i,
            TxData {
                balance,
                input_data,
            },
        ) in attack_data.iter().enumerate()
        {
            // update block when in concrete mode
            if state.env.blocks[i].blocknumber.is_some() {
                let block = &state.env.blocks[i];
                evm.genesis.difficulty = BitVec::as_bigint(&block.difficulty).unwrap().into();
                evm.genesis.coinbase = BitVec::as_bigint(&block.coinbase).unwrap().into();
                evm.genesis.timestamp = BitVec::as_bigint(&block.timestamp).unwrap().into();
                evm.genesis.number = BitVec::as_bigint(&block.number).unwrap().into();
                evm.genesis.gas_limit = BitVec::as_bigint(&block.gas_limit).unwrap().into();
            }

            let input = EvmInput {
                input_data: convert_data_to_bytes(input_data.clone()),
                sender: sender.clone(),
                receiver: receiver.clone(),
                gas: 100_000_000,
                value: balance.clone(),
            };
            execution = evm.execute(input);
            if i == attack_data.len() - 1 {
                return Some(execution);
            }
            evm = match execution.into_evm_updated() {
                Ok(res) => res,
                Err(e) => {
                    error!("Error during transactions execution: {:?}", e);
                    return None;
                }
            };
        }
        None
    }

    fn verify_tx_value_transfer(&self, state: &SeState, attack_data: &[TxData]) -> Option<()> {
        if state.context.config().no_verify {
            return Some(());
        }

        let sender: Address = BitVec::as_bigint(&state.env.get_account(&self.from).addr)
            .unwrap()
            .into();
        let evm = self
            .execute_concrete_evm(state, attack_data)?
            .into_evm_updated()
            .ok()?;
        if evm.genesis.alloc[&sender].balance.0 > 10_000_000_000_000_000_000u64.into() {
            Some(())
        } else {
            None
        }
    }

    fn verify_tx_hijack_control_flow(&self, state: &SeState, attack_data: &[TxData]) -> Option<()> {
        if state.context.config().no_verify {
            return Some(());
        }

        let evm = self.execute_concrete_evm(state, attack_data)?;
        let hijack_address = U256::from_dec_str(crate::se::config::HIJACK_ADDR).unwrap();
        for ins in evm.result.ok()?.trace {
            match ins.instruction {
                Instruction::DelegateCall { code_from, .. }
                | Instruction::CallCode { code_from, .. } => {
                    if code_from == hijack_address.into() {
                        return Some(());
                    }
                }
                _ => {}
            }
        }
        None
    }

    fn verify_tx_suicide(&self, state: &SeState, attack_data: &[TxData]) -> Option<()> {
        if state.context.config().no_verify {
            return Some(());
        }

        let evm = self.execute_concrete_evm(state, attack_data)?;
        for ins in evm.result.ok()?.trace {
            if let Instruction::Selfdestruct { .. } = ins.instruction {
                return Some(());
            }
        }
        None
    }

    fn verify_tx_owner(&self, state: &SeState, attack_data: &[TxData], index: WU256) -> Option<()> {
        if state.context.config().no_verify {
            return Some(());
        }

        let evm = self.execute_concrete_evm(state, attack_data)?;
        for ins in evm.result.ok()?.trace {
            if let Instruction::SStore { addr, .. } = ins.instruction {
                if addr == index {
                    return Some(());
                }
            }
        }
        None
    }

    fn concrete_input_data_for_tx(&self, s: &SeState, tx: &TxId) -> Option<TxData> {
        let mut load_state = s.clone();
        let mut loads = Vec::with_capacity(5);
        let data = s.env.get_tx(tx).data;
        for i in 0..5 {
            let load = mload(&s.memory, data, &const_usize(i * 32));
            loads.push(Arc::clone(&load));
            load_state.record_read(&load);

            load_state.push_constraint(load);
        }
        let res = load_state.get_values_for_array(loads.as_slice())?;
        let balance = load_state.get_value(&load_state.env.get_tx(tx).callvalue)?;
        tx_data_from_bval_vec(balance, res)
    }

    pub fn dump_debug_graph(mut self) {
        self.graph.analyze_graph();
        info!("Dumping debug graph!");
        self.graph
            .to_dot(
                &mut File::create("output/se_graph/se_graph.dot")
                    .expect("Could not create file for SE graph"),
            )
            .expect("Could not dump SE graph");
    }

    pub fn from(&self) -> AccountId {
        self.from
    }

    pub fn to(&self) -> AccountId {
        self.to
    }

    /// This is the initial code executed, this might be different from all the code executed
    pub fn code_to_be_executed(&self) -> Vec<u8> {
        self.graph
            .initial_state()
            .account()
            .code()
            .unwrap()
            .to_vec()
    }
}

pub struct ExplorationResult {
    pub new_states: Vec<ResultState>,
    pub result: Option<Vec<Attack>>,
    pub loaded_accounts: Option<HashSet<LoadedAccount>>,
    pub precompiled_contracts: Option<HashSet<PrecompiledContracts>>,
    pub blocks: Option<Vec<usize>>,
}

impl ExplorationResult {
    pub fn found_attacks(&self) -> bool {
        self.result.is_some()
    }

    pub fn attacks(self) -> Option<Vec<Attack>> {
        self.result
    }

    pub fn end_states(self) -> Vec<ResultState> {
        self.new_states
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct Attack {
    pub txs: Vec<TxData>,
    pub attack_type: AttackType,
}

impl fmt::Display for Attack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(
            f,
            "========================================================="
        )?;
        writeln!(f, "Found attack, {}", self.attack_type)?;
        writeln!(
            f,
            "========================================================="
        )?;
        for (i, tx) in self.txs.iter().enumerate() {
            writeln!(f, "\nDumping tx {}:\n{}", i + 1, tx)?;
            writeln!(
                f,
                "========================================================="
            )?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TxData {
    pub balance: WU256,
    pub input_data: Vec<Hash>,
}

fn convert_data_to_bytes(data: Vec<Hash>) -> Bytes {
    let mut vec = Vec::with_capacity(32 * data.len());
    for u256 in data {
        let array: [u8; 32] = u256.0.into();
        for i in 0..32 {
            vec.push(array[i]);
        }
    }
    vec.into()
}

fn tx_data_from_bval_vec(balance: BVal, data: Vec<BVal>) -> Option<TxData> {
    let balance = FVal::as_bigint(&balance)?.into();
    let mut res = Vec::with_capacity(data.len());
    for val in data {
        res.push(FVal::as_bigint(&val)?.into());
    }
    Some(TxData {
        balance,
        input_data: res,
    })
}

impl fmt::Display for TxData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Balance: {:x}", self.balance)?;
        for (i, v) in self.input_data.iter().enumerate() {
            writeln!(f, "0x{:08X}:\t{:16x}", i * 32, v)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub enum AttackType {
    StealMoney,
    DeleteContract,
    HijackControlFlow,
    Reentrancy,
    CanChangeOwner,
}

impl fmt::Display for AttackType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AttackType::StealMoney => {
                write!(f, "can transfer funds to attacker controlled account")
            }
            AttackType::DeleteContract => write!(f, "can trigger contract suicide"),
            AttackType::HijackControlFlow => {
                write!(f, "can hijack control flow to attacker controlled contract")
            }
            AttackType::Reentrancy => write!(f, "can trigger reentrancy"),
            AttackType::CanChangeOwner => write!(f, "can change owner variable as attacker"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::se::expr::symbolic_memory::memcopy;
    use std::sync::Arc;
    use std::thread;
    use yaml_rust::YamlLoader;

    static YAML: &str = "
state:
    0xaad62f08b3b9f0ecc7251befbeff80c9bb488fe9:
        balance: 0x100000
        nonce: 0x1000000
        code: 60606040526004361061004c576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680632f432c081461005157806341c0e1b514610066575b600080fd5b341561005c57600080fd5b61006461007b565b005b341561007157600080fd5b6100796100bd565b005b336000806101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff160217905550565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff1614151561011557fe5b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16ff00a165627a7a72305820f3144583596e67d998d568c2e75c63dd961472f8f27d9fb5bad677c80d5d3dd30029
        storage:
            0x0: 0xaad62f08b3b9f0ecc7251befbeff80c9bb488fe9


victim: 0xaad62f08b3b9f0ecc7251befbeff80c9bb488fe9
";
    static CODE: [u8; 379] = [
        0x60, 0x60, 0x60, 0x40, 0x52, 0x60, 0x04, 0x36, 0x10, 0x61, 0x00, 0x4c, 0x57, 0x60, 0x00,
        0x35, 0x7c, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x90, 0x04, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x80, 0x63, 0x2f, 0x43, 0x2c, 0x08,
        0x14, 0x61, 0x00, 0x51, 0x57, 0x80, 0x63, 0x41, 0xc0, 0xe1, 0xb5, 0x14, 0x61, 0x00, 0x66,
        0x57, 0x5b, 0x60, 0x00, 0x80, 0xfd, 0x5b, 0x34, 0x15, 0x61, 0x00, 0x5c, 0x57, 0x60, 0x00,
        0x80, 0xfd, 0x5b, 0x61, 0x00, 0x64, 0x61, 0x00, 0x7b, 0x56, 0x5b, 0x00, 0x5b, 0x34, 0x15,
        0x61, 0x00, 0x71, 0x57, 0x60, 0x00, 0x80, 0xfd, 0x5b, 0x61, 0x00, 0x79, 0x61, 0x00, 0xbd,
        0x56, 0x5b, 0x00, 0x5b, 0x33, 0x60, 0x00, 0x80, 0x61, 0x01, 0x00, 0x0a, 0x81, 0x54, 0x81,
        0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x02, 0x19, 0x16, 0x90, 0x83, 0x73, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0x16, 0x02, 0x17, 0x90, 0x55, 0x50, 0x56, 0x5b, 0x60, 0x00, 0x80, 0x90, 0x54,
        0x90, 0x61, 0x01, 0x00, 0x0a, 0x90, 0x04, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x14,
        0x15, 0x15, 0x61, 0x01, 0x15, 0x57, 0xfe, 0x5b, 0x60, 0x00, 0x80, 0x90, 0x54, 0x90, 0x61,
        0x01, 0x00, 0x0a, 0x90, 0x04, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0x16, 0xff, 0x00, 0xa1, 0x65, 0x62, 0x7a, 0x7a, 0x72, 0x30, 0x58, 0x20,
        0xf3, 0x14, 0x45, 0x83, 0x59, 0x6e, 0x67, 0xd9, 0x98, 0xd5, 0x68, 0xc2, 0xe7, 0x5c, 0x63,
        0xdd, 0x96, 0x14, 0x72, 0xf8, 0xf2, 0x7d, 0x9f, 0xb5, 0xba, 0xd6, 0x77, 0xc8, 0x0d, 0x5d,
        0x3d, 0xd3, 0x00, 0x29,
    ];

    #[test]
    fn from_se_env_test() {
        let yaml = &YamlLoader::load_from_str(YAML).unwrap()[0];
        let config = CONFIG.read().unwrap().clone();
        let env = SeEnviroment::from_yaml(yaml);

        let correct_from = env.from.clone();
        let correct_to = env.to.clone();

        let ana = Analysis::from_se_env(
            env,
            config,
            Solvers::Yice {
                count: num_cpus::get(),
                timeout: 120_000,
            },
        );
        assert_eq!(correct_from, ana.from);
        assert_eq!(correct_to, ana.to);
        assert_eq!(CODE.to_vec(), ana.code_to_be_executed());
    }

    #[test]
    fn initialize_call_test() {
        let yaml = &YamlLoader::load_from_str(YAML).unwrap()[0];
        let config = CONFIG.read().unwrap().clone();
        let env = SeEnviroment::from_yaml(yaml);

        let ana = Analysis::from_se_env(
            env,
            config,
            Solvers::Yice {
                count: num_cpus::get(),
                timeout: 120_000,
            },
        );
        let mut state = ana.graph.get_state_by_id(1).clone();
        let code = ana.code_to_be_executed();
        let from = ana.from;
        let to = ana.to;
        let config = state.context.config().clone();

        let tx;
        {
            let env = Arc::make_mut(&mut state.env);
            let mut memory = Arc::make_mut(&mut state.memory);
            tx = env.new_attacker_tx(&mut memory, from, to);
            let data = env.get_tx(&tx).data;
            env.get_tx_mut(&tx).data = memcopy(
                &mut memory,
                data,
                state.mem,
                &const_usize(0),
                &const_usize(0x0),
                &const_usize(0x0),
            );
        }

        let mode = AnalysisMode::Call(tx);
        let memory = Arc::clone(&state.memory);
        let new_ana = Analysis::from_result_state(
            &code,
            &from,
            &to,
            config,
            state.as_result_state(),
            mode,
            memory,
        );
        let first_state = &new_ana.graph.get_state_by_id(1);
        assert_eq!(first_state.input_tx().id, tx);
    }

    #[test]
    fn id_generator_test() {
        let context = Arc::new(Context::test());
        let mut threads = vec![];
        for _ in 0..50 {
            let context_clone = context.clone();
            let thread = thread::spawn(move || {
                let mut ids = vec![];
                for _ in 0..100_000 {
                    ids.push(context_clone.next_id());
                }
                ids
            });
            threads.push(thread);
        }

        let mut ids = vec![];
        for thread in threads {
            match thread.join() {
                Ok(res) => ids.push(res),
                Err(panic) => panic!("Thread had an error: {:?}", panic),
            }
        }
        let mut ids = ids
            .iter()
            .flat_map(|inner| inner.iter())
            .collect::<Vec<_>>();
        ids.sort();
        for i in 1..ids.len() {
            assert_ne!(ids[i], ids[i - 1]);
            assert_eq!(ids[i] - 1, *ids[i - 1]);
        }
    }
}
