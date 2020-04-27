use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

use ethereum_newtypes::WU256;
use evmexec::genesis;
use hexdecode;
use lazy_static::lazy_static;
use parity_connector::{BlockSelector, ParityConnector};
use parking_lot::Mutex;
use rand::distributions::Standard;
use rand::{thread_rng, Rng};
use tiny_keccak::Keccak;
use uint::U256;
use yaml_rust::Yaml;

lazy_static! {
    pub static ref GLOBAL_COVERAGE_MAP: Mutex<HashMap<AccountId, CodeCoverage>> =
        { Mutex::new(HashMap::new()) };
}

use crate::disasm::CodeCoverage;
use crate::se::{
    config::*,
    expr::{
        bval::*,
        symbolic_memory::{self, word_write, MVal, MemoryType, SymbolicMemory},
    },
    symbolic_analysis::CONFIG,
};
use crate::PrecompiledContracts;

fn generate_random_vec() -> [u8; 32] {
    let mut rng = thread_rng();
    let input: Vec<u8> = rng.sample_iter(&Standard).take(32).collect();
    let mut keccak = Keccak::new_keccak256();
    keccak.update(&input);
    let mut res: [u8; 32] = [0; 32];
    keccak.finalize(&mut res);
    res
}

fn generate_random_hash() -> BVal {
    const_vec(&generate_random_vec())
}

fn generate_random_address() -> BVal {
    const_vec(&generate_random_vec()[..20])
}

lazy_static! {
    static ref GLOBAL_COUNTER: Mutex<Counter> = Mutex::new(Counter::new());
}

pub fn fresh_var_name(name: &str) -> String {
    GLOBAL_COUNTER.lock().fresh_var_name(name)
}

fn fresh_account_name(name: &str) -> String {
    GLOBAL_COUNTER.lock().fresh_account_name(name)
}

fn fresh_tx_name(name: &str) -> String {
    GLOBAL_COUNTER.lock().fresh_tx_name(name)
}

// consider using storing actual references to variables to access later
#[derive(Debug)]
struct Counter {
    tx_counters: HashMap<String, usize>,
    acc_counters: HashMap<String, usize>,
    var_counters: HashMap<String, usize>,
}

impl Counter {
    fn new() -> Self {
        let tx_counters = HashMap::new();
        let acc_counters = HashMap::new();
        let var_counters = HashMap::new();
        Counter {
            tx_counters,
            acc_counters,
            var_counters,
        }
    }

    fn fresh_var_name(&mut self, name: &str) -> String {
        let entry = self.var_counters.entry(name.into()).or_insert(0);
        *entry += 1;
        format!("{}_{}", name, *entry)
    }

    fn fresh_account_name(&mut self, name: &str) -> String {
        let entry = self.acc_counters.entry(name.into()).or_insert(0);
        *entry += 1;
        format!("{}_{}", name, *entry)
    }

    fn fresh_tx_name(&mut self, name: &str) -> String {
        let entry = self.tx_counters.entry(name.into()).or_insert(0);
        *entry += 1;
        format!("{}_{}", name, *entry)
    }
}

#[derive(Debug, Clone)]
pub struct SeEnviroment {
    pub env: Env,
    pub from: AccountId,
    pub to: AccountId,
    pub memory: Arc<SymbolicMemory>,
}

fn parse_yaml_value(val: &Yaml) -> BVal {
    match val {
        Yaml::String(s) => {
            if s.starts_with("0x") {
                const_vec(&hexdecode::decode(&s[2..].as_bytes()).unwrap())
            } else {
                const_vec(&hexdecode::decode(&s.as_bytes()).unwrap())
            }
        }
        Yaml::Integer(i) => const_usize(*i as usize),
        _ => unreachable!("{:?}", val),
    }
}

impl SeEnviroment {
    pub fn from_chain(addr: &str) -> Option<Self> {
        if CONFIG.read().unwrap().parity.is_none() {
            return None;
        }
        let mut env = Env::from_chain();
        let mut memory = symbolic_memory::new_memory();

        // create env
        let attacker = env.new_attacker_account(&mut memory);
        let _hijack = env.new_hijack_account(&mut memory);

        let addr_vec = hexdecode::decode(addr.as_bytes()).unwrap();
        let account_addr = const_vec(addr_vec.as_slice());
        let victim = env.try_load_account_from_chain(&mut memory, &account_addr)?;

        {
            let vic = env.get_account_mut(&victim);
            if vic.code.is_none() {
                return None;
            }
            if FVal::as_bigint(&vic.balance).unwrap() == U256::zero() {
                warn!("Account has zero balance on chain, using 10 Ether as substitute for detecting attacks.");
                vic.balance = const_usize(10_000_000_000_000_000_000);
                vic.initial_balance = Some(10_000_000_000_000_000_000usize.into());
            }
        }
        let memory = Arc::new(memory);

        Some(SeEnviroment {
            env,
            from: attacker,
            to: victim,
            memory,
        })
    }

    pub fn from_yaml(yaml: &Yaml) -> Self {
        let mut env = if CONFIG.read().unwrap().parity.is_some() {
            Env::from_chain()
        } else {
            Env::new()
        };
        let mut memory = symbolic_memory::new_memory();
        let attacker = env.new_attacker_account(&mut memory);
        let _hijack = env.new_hijack_account(&mut memory);
        let mut victim = AccountId(0);
        let mut id;

        let victim_addr =
            const_vec(&hexdecode::decode(yaml["victim"].as_str().unwrap().as_bytes()).unwrap());
        let state = &yaml["state"];

        // BTreeMap
        for (addr, s) in state.as_hash().unwrap() {
            let account_addr =
                const_vec(&hexdecode::decode(addr.as_str().unwrap().as_bytes()).unwrap());
            let account_balance = parse_yaml_value(&s["balance"]);

            let name = if account_addr == victim_addr {
                "victim"
            } else {
                "other"
            };

            if s.as_hash()
                .unwrap()
                .contains_key(&Yaml::String(String::from("code")))
            {
                let code = hexdecode::decode(s["code"].as_str().unwrap().as_bytes()).unwrap();
                id = env.new_account(
                    &mut memory,
                    &name,
                    &account_addr,
                    Some(code),
                    &account_balance,
                );

                // parse storage
                if !s["storage"].is_badvalue() {
                    let mut initial_storage = Vec::new();
                    let mut account = env.get_account_mut(&id);
                    for (addr, val) in s["storage"].as_hash().unwrap() {
                        let addr = parse_yaml_value(&addr);
                        let val = parse_yaml_value(&val);

                        initial_storage.push((
                            BitVec::as_bigint(&addr).unwrap().into(),
                            BitVec::as_bigint(&val).unwrap().into(),
                        ));

                        account.storage = word_write(&mut memory, account.storage, &addr, &val);
                    }
                    account.initial_storage = Some(initial_storage);
                }

                // check if owner index is suplied
                if !s["owner"].is_badvalue() {
                    let index = parse_yaml_value(&s["owner"]);
                    let mut account = env.get_account_mut(&id);
                    account.owner = Some(index);
                }
            } else {
                id = env.new_account(&mut memory, &name, &account_addr, None, &account_balance);
            }

            env.get_account_mut(&id).initial_balance =
                Some(BitVec::as_bigint(&account_balance).unwrap().into());

            // save id
            let mut loaded_accounts = env.loaded_accounts.unwrap_or_else(Vec::new);
            loaded_accounts.push(id);
            env.loaded_accounts = Some(loaded_accounts);

            if account_addr == victim_addr {
                victim = id;
            }
        }
        let memory = Arc::new(memory);

        SeEnviroment {
            env,
            from: attacker,
            to: victim,
            memory,
        }
    }
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub struct AccountId(pub usize);

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub struct TxId(usize);

#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub gasprice: BVal,
    pub mem_size: BVal,
    pub gas_limit: BVal,
    pub difficulty: BVal,
    pub number: BVal,
    pub timestamp: BVal,
    pub coinbase: BVal,
    pub blockhash: BVal,

    /// If this is a real block and not one we created, this is set
    pub blocknumber: Option<usize>,
}

impl Block {
    /// Create a fully symbolic block
    fn new() -> Self {
        let gasprice = fresh_var("gasprice");
        let mem_size = fresh_var("mem_size");
        let gas_limit = fresh_var("gas_limit");
        let difficulty = fresh_var("difficulty");
        let number = fresh_var("number");
        let timestamp = fresh_var("timestamp");
        let coinbase = fresh_var("coinbase");
        let blockhash = fresh_var("blockhash");
        let blocknumber = None;
        Self {
            gasprice,
            mem_size,
            gas_limit,
            difficulty,
            number,
            timestamp,
            coinbase,
            blockhash,
            blocknumber,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Env {
    pub blocknumbers: Option<Vec<usize>>,
    /// The block present in the execution
    pub blocks: Vec<Block>,
    pub loaded_accounts: Option<Vec<AccountId>>,
    pub precompiled_contracts: Option<Vec<PrecompiledContracts>>,

    /// The last 256 block hashes, when executing in concrete mode
    pub blockhashes: Option<VecDeque<BVal>>,

    /// Accounts present in the enviroment
    accounts: HashMap<AccountId, Account>,
    acc_counter: usize,

    addresses: HashMap<BVal, AccountId>,

    /// Transactions present in the enviroment
    transactions: HashMap<TxId, Transaction>,
    tx_counter: usize,
    constraints: Vec<BVal>,
}

impl Default for Env {
    fn default() -> Self {
        Self::new()
    }
}

impl Env {
    pub fn new() -> Self {
        let blocknumbers = None;
        let loaded_accounts = None;
        let precompiled_contracts = None;

        // account relatid
        let addresses = HashMap::new();
        let accounts = HashMap::new();
        let acc_counter = 0;

        let transactions = HashMap::new();
        let tx_counter = 0;
        let block = Block::new();

        let constraints = vec![
            lt(&block.gasprice, &const256(MAX_GASPRICE)),
            lt(&block.gas_limit, &const256(GAS_LIMIT)),
            lt(&block.mem_size, &const_usize(100_000)),
            lt(&block.difficulty, &const256(MAX_DIFFICULTY)),
            lt(&block.number, &const256(MAX_NUMBER)),
            lt(&block.timestamp, &const256(MAX_TIMESTAMP)),
            eql(&block.coinbase, &const256(COINBASE)),
            eql(&block.blockhash, &const256(BLOCKHASH)),
        ];
        let blocks = vec![block];
        let blockhashes = None;
        Env {
            accounts,
            transactions,
            acc_counter,
            tx_counter,
            addresses,
            constraints,
            blocknumbers,
            loaded_accounts,
            precompiled_contracts,
            blocks,
            blockhashes,
        }
    }

    pub fn from_chain() -> Self {
        let (mut client, block) = create_parity_client();
        let initial_block = client.block_by_number(block);
        let analysis_depth = CONFIG.read().unwrap().message_bound;
        let start_block = initial_block.number().0 - analysis_depth;
        let block = client.block_by_number(BlockSelector::Specific(start_block.as_usize()));

        let mut blockhashes: VecDeque<BVal> = VecDeque::with_capacity(256);
        blockhashes.push_back(const_usize(0));
        for i in 1..256 {
            blockhashes.push_back(const_u256(
                client
                    .block_by_number(BlockSelector::Specific(start_block.as_usize() - i))
                    .hash()
                    .0,
            ));
        }
        assert!(blockhashes.len() == 256, "Len: {}", blockhashes.len()); // assert we didn't off by one

        let mut env = Env::new();
        env.blockhashes = Some(blockhashes);
        env.blocknumbers = Some(vec![start_block.as_usize()]);
        env.latest_block_mut().blocknumber = Some(start_block.as_usize());
        env.latest_block_mut().gas_limit = const_u256(block.gas_limit().0);
        env.latest_block_mut().difficulty = const_u256(block.difficulty().0);
        env.latest_block_mut().number = const_u256(block.number().0);
        env.latest_block_mut().timestamp = const_u256(block.timestamp().0);
        env.latest_block_mut().coinbase = const_u256(block.miner().0);
        env.latest_block_mut().blockhash = const_u256(block.hash().0);
        env.constraints = vec![
            lt(&env.latest_block().gasprice, &const256(MAX_GASPRICE)),
            lt(&env.latest_block().mem_size, &const_usize(100_000)),
        ];
        debug!(
            "Successfully loaded initial block parameter: {:?}",
            env.constraints
        );
        env
    }

    // this function is a disgrace, but it works, soooo ehh..?
    pub fn from_old_env(old_env: &Self) -> Self {
        let mut env = old_env.clone();
        let block = Block::new();
        env.blocks.push(block);

        env.latest_block_mut().gasprice = fresh_var("gasprice");
        env.latest_block_mut().mem_size = fresh_var("mem_size");
        let mut constraints = vec![
            lt(&env.latest_block().gasprice, &const256(MAX_GASPRICE)),
            lt(&env.latest_block().mem_size, &const_usize(100_000)),
        ];

        if let Some(number) = old_env.latest_block().blocknumber {
            let (mut client, _) = create_parity_client();
            let block = client.block_by_number(BlockSelector::Specific(number + 1));
            env.latest_block_mut().gas_limit = const_u256(block.gas_limit().0);
            env.latest_block_mut().difficulty = const_u256(block.difficulty().0);
            env.latest_block_mut().number = const_u256(block.number().0);
            env.latest_block_mut().timestamp = const_u256(block.timestamp().0);
            env.latest_block_mut().coinbase = const_u256(block.miner().0);
            env.latest_block_mut().blockhash = const_u256(block.hash().0);
            env.latest_block_mut().blocknumber = Some(number + 1);
            env.blocknumbers.as_mut().unwrap().push(number + 1);

            // update blockhashes
            let mut hashes = env.blockhashes.take().unwrap();

            // first pop last block in time
            hashes.pop_back();
            // add newest blockhash to front
            hashes.push_front(const_u256(block.hash().0));
            assert!(hashes.len() == 256);

            //write back
            env.blockhashes = Some(hashes);
        } else {
            env.latest_block_mut().gasprice = fresh_var("gasprice");
            env.latest_block_mut().mem_size = fresh_var("mem_size");
            env.latest_block_mut().gas_limit = fresh_var("gas_limit");
            env.latest_block_mut().difficulty = fresh_var("difficulty");
            env.latest_block_mut().number = fresh_var("number");
            env.latest_block_mut().timestamp = fresh_var("timestamp");
            env.latest_block_mut().coinbase = fresh_var("coinbase");
            env.latest_block_mut().blockhash = fresh_var("blockhash");

            constraints.push(lt(&env.latest_block().gasprice, &const256(MAX_GASPRICE)));
            constraints.push(lt(&env.latest_block().gas_limit, &const256(GAS_LIMIT)));
            constraints.push(lt(&env.latest_block().mem_size, &const_usize(100_000)));
            constraints.push(lt(
                &env.latest_block().difficulty,
                &const256(MAX_DIFFICULTY),
            ));
            constraints.push(lt(
                &old_env.latest_block().number,
                &env.latest_block().number,
            ));
            constraints.push(lt(
                &old_env.latest_block().timestamp,
                &env.latest_block().timestamp,
            ));
            constraints.push(eql(
                &env.latest_block().coinbase,
                &generate_random_address(),
            ));
            constraints.push(eql(&env.latest_block().blockhash, &generate_random_hash()));
        }
        env.constraints.append(&mut constraints);
        env
    }

    pub fn latest_block(&self) -> &Block {
        &self.blocks[self.blocks.len() - 1]
    }

    pub fn latest_block_mut(&mut self) -> &mut Block {
        let len = self.blocks.len() - 1;
        &mut self.blocks[len]
    }

    fn add_contract(&mut self, contract: PrecompiledContracts) {
        if let Some(ref mut vec) = self.precompiled_contracts {
            vec.push(contract);
        } else {
            self.precompiled_contracts = Some(vec![contract]);
        }
    }

    pub fn try_load_account_from_chain(
        &mut self,
        memory: &mut SymbolicMemory,
        addr: &BVal,
    ) -> Option<AccountId> {
        if CONFIG.read().unwrap().parity.is_none() {
            debug!("Could not dynamically load account from chain, parity client missing!");
            return None;
        }

        let addr_c = FVal::as_bigint(addr)?;

        // precompiled contracts not supported atm and uninnitialized storage filter
        if addr_c.is_zero() {
            return None;
        } else if addr_c == 0x1.into() {
            self.add_contract(PrecompiledContracts::EcdsaRecover);
            return None;
        } else if addr_c == 0x2.into() {
            self.add_contract(PrecompiledContracts::Sha256);
            return None;
        } else if addr_c == 0x3.into() {
            self.add_contract(PrecompiledContracts::Ripemd160);
            return None;
        } else if addr_c == 0x4.into() {
            self.add_contract(PrecompiledContracts::Identity);
            return None;
        } else if addr_c == 0x5.into() {
            self.add_contract(PrecompiledContracts::ModularExponentiation);
            return None;
        } else if addr_c == 0x6.into() {
            self.add_contract(PrecompiledContracts::EcAddition);
            return None;
        } else if addr_c == 0x7.into() {
            self.add_contract(PrecompiledContracts::EcScalarMultiplikation);
            return None;
        } else if addr_c == 0x8.into() {
            self.add_contract(PrecompiledContracts::EcPairingEquation);
            return None;
        }
        // check if potential address
        if addr_c.bits() > 160 {
            debug!("Non valid address supplied to dynamic loader");
            return None;
        }

        let (mut client, block) = create_parity_client();

        // fetch code
        let code = client.code(addr_c, block);

        // fetch code
        let chain_balance = client.balance(addr_c, block);
        let account_balance = const_u256(chain_balance);
        let account_addr = Arc::clone(addr);

        debug!(
            "Dynamically loaded code for account {:?}: {:x?}",
            account_addr, code
        );

        let code = if code.is_empty() { None } else { Some(code) };

        let id = self.new_account(
            memory,
            &fresh_var_name("loaded_account"),
            &account_addr,
            code,
            &account_balance,
        );

        self.get_account_mut(&id).initial_balance = Some(chain_balance.into());

        self.try_load_storage_for_account(memory, &id);
        if let Some(ref mut vec) = self.loaded_accounts {
            vec.push(id);
        } else {
            self.loaded_accounts = Some(vec![id]);
        }

        Some(id)
    }

    fn try_load_storage_for_account(&mut self, memory: &mut SymbolicMemory, id: &AccountId) {
        let (mut client, block) = create_parity_client();

        let acc = self.get_account_mut(id);
        let stor = if let Some(s) = client.storage(FVal::as_bigint(&acc.addr).unwrap(), block) {
            s
        } else {
            warn!(
                "Could not load storage for account: {:?}, using 0 initialized storage",
                acc.addr
            );
            return;
        };
        let mut initial_storage: Vec<(WU256, WU256)> = vec![];
        for (addr, val) in stor.into_iter() {
            acc.storage = word_write(memory, acc.storage, &const_u256(addr), &const_u256(val));
            initial_storage.push((addr.into(), val.into()));
        }
        acc.initial_storage = Some(initial_storage);
        debug!(
            "Loaded Storage for account {:?}: {}",
            acc.addr,
            symbolic_memory::pretty_print(memory, acc.storage)
        );
    }

    pub fn get_memories(&self) -> Vec<MVal> {
        let mut mems = vec![];
        for acc in self.accounts.values() {
            for map in acc.mappings.values() {
                mems.push(*map);
            }
            mems.push(acc.storage);
        }
        for tx in self.transactions.values() {
            mems.push(tx.data);
        }
        mems
    }

    pub fn get_constraints(&self) -> Vec<BVal> {
        let mut constraints = vec![];
        for acc in self.accounts.values() {
            constraints.append(&mut acc.get_constraints());
        }

        for tx in self.transactions.values() {
            constraints.append(&mut tx.get_constraints());
        }
        constraints.append(&mut self.constraints.clone());
        constraints
    }

    fn new_tx_id(&mut self) -> TxId {
        self.tx_counter += 1;
        TxId(self.tx_counter)
    }

    pub fn new_attacker_tx(
        &mut self,
        memory: &mut SymbolicMemory,
        attacker: AccountId,
        victim: AccountId,
    ) -> TxId {
        let attacker_addr = self.accounts[&attacker].addr.clone();
        let victim_addr = self.accounts[&victim].addr.clone();
        let tx_id = self.new_tx_id();

        let tx = Transaction::with_sender_receiver(
            memory,
            tx_id,
            &fresh_tx_name("initial"),
            &attacker_addr,
            &victim_addr,
        );
        self.update_env_for_tx(&attacker, &victim, tx, tx_id)
    }

    fn update_env_for_tx(
        &mut self,
        from: &AccountId,
        to: &AccountId,
        tx: Transaction,
        tx_id: TxId,
    ) -> TxId {
        {
            let from = self.get_account_mut(from);
            let from_balance = Arc::clone(&from.balance);
            from.constraints.push(le(&tx.callvalue, &from_balance)); // cannot send more then I own
            from.balance = sub(&from_balance, &tx.callvalue);
        }
        {
            let to = self.get_account_mut(to);
            let to_balance = Arc::clone(&to.balance);
            to.balance = add(&to_balance, &tx.callvalue);
        }
        self.transactions.insert(tx_id, tx);
        tx_id
    }

    #[cfg_attr(feature = "cargo-clippy", allow(clippy::too_many_arguments))]
    pub fn new_output_tx(
        &mut self,
        memory: &mut SymbolicMemory,
        name: &str,
        caller: &AccountId,
        origin: &BVal,
        addr: &AccountId,
        gas: &BVal,
        callvalue: &BVal,
        calldata_size: &BVal,
        returndata_size: &BVal,
    ) -> TxId {
        let caller_addr = Arc::clone(&self.get_account(caller).addr);
        let addr_addr = Arc::clone(&self.get_account(addr).addr);

        let tx_id = self.new_tx_id();
        let tx = Transaction::new_outgoing(
            memory,
            tx_id,
            &fresh_tx_name(&format!("{}_output", name)),
            &caller_addr,
            &origin,
            &addr_addr,
            gas,
            callvalue,
            calldata_size,
            returndata_size,
        );

        self.update_env_for_tx(caller, addr, tx, tx_id)
    }

    fn new_acc_id(&mut self) -> AccountId {
        self.acc_counter += 1;
        AccountId(self.acc_counter)
    }

    pub fn new_hijack_account(&mut self, memory: &mut SymbolicMemory) -> AccountId {
        let id = self.new_acc_id();
        let acc = Account::with_addr(
            memory,
            id,
            &fresh_account_name("hijack"),
            &const256(HIJACK_ADDR),
        );
        self.accounts.insert(id, acc);
        self.addresses.insert(const256(HIJACK_ADDR), id);
        id
    }

    pub fn new_attacker_account(&mut self, memory: &mut SymbolicMemory) -> AccountId {
        let id = self.new_acc_id();
        let mut acc = Account::with_addr(
            memory,
            id,
            &fresh_account_name("attacker"),
            &const256(ORIGIN),
        );
        acc.initial_attacker_balance = Some(Arc::clone(&acc.balance));
        self.accounts.insert(id, acc);
        self.addresses.insert(const256(ORIGIN), id);
        id
    }

    pub fn new_victim_account(&mut self, memory: &mut SymbolicMemory, code: &[u8]) -> AccountId {
        let id = self.new_acc_id();
        let coverage = CodeCoverage::from_raw(code);
        GLOBAL_COVERAGE_MAP.lock().insert(id, coverage);
        let vic = Account::with_addr_and_code(
            memory,
            id,
            &fresh_account_name("victim"),
            &const256(TARGET_ADDR),
            Some(code.into()),
        );
        self.accounts.insert(id, vic);
        self.addresses.insert(const256(TARGET_ADDR), id);
        id
    }

    pub fn new_account(
        &mut self,
        memory: &mut SymbolicMemory,
        name: &str,
        addr: &BVal,
        code: Option<Vec<u8>>,
        balance: &BVal,
    ) -> AccountId {
        let id = self.new_acc_id();
        if let Some(ref c) = code {
            let coverage = CodeCoverage::from_raw(c);
            GLOBAL_COVERAGE_MAP.lock().insert(id, coverage);
        }
        let acc = Account::with_addr_code_balance(
            memory,
            id,
            &fresh_account_name(name),
            addr,
            code,
            balance,
        );
        self.accounts.insert(id, acc);
        self.addresses.insert(Arc::clone(addr), id);
        id
    }

    pub fn get_addresses_except(&self, id: &AccountId) -> Vec<(BVal, AccountId)> {
        self.addresses
            .iter()
            .filter(|(_, v)| *v != id)
            .map(|(k, v)| (k.clone(), *v))
            .collect()
    }
    pub fn get_addresses(&self) -> Vec<(BVal, AccountId)> {
        self.addresses
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect()
    }

    pub fn try_get_account(&self, id: &AccountId) -> Option<&Account> {
        self.accounts.get(id)
    }

    pub fn try_get_account_id_by_addr(&self, addr: &BVal) -> Option<&AccountId> {
        self.addresses.get(addr)
    }

    pub fn try_get_account_by_addr(&self, addr: &BVal) -> Option<&Account> {
        let id = self.try_get_account_id_by_addr(addr)?;
        self.try_get_account(&id)
    }

    pub fn get_account(&self, id: &AccountId) -> &Account {
        &self.accounts[id]
    }

    pub fn try_get_account_mut(&mut self, id: &AccountId) -> Option<&mut Account> {
        self.accounts.get_mut(id)
    }

    pub fn get_account_mut(&mut self, id: &AccountId) -> &mut Account {
        self.accounts.get_mut(id).unwrap()
    }

    pub fn get_tx(&self, id: &TxId) -> &Transaction {
        &self.transactions[id]
    }

    pub fn get_tx_mut(&mut self, id: &TxId) -> &mut Transaction {
        self.transactions.get_mut(id).unwrap()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Transaction {
    pub id: TxId,
    pub name: String,
    pub caller: BVal,
    pub origin: BVal, // from
    pub addr: BVal,   // to
    pub gas: BVal,
    pub data: MVal,
    pub callvalue: BVal,
    pub calldata_size: BVal,
    constraints: Vec<BVal>,
}

impl Transaction {
    fn new(memory: &mut SymbolicMemory, id: TxId, name: &str) -> Self {
        let name = String::from(name);
        let caller = fresh_var(&format!("{}_caller", name));
        let origin = fresh_var(&format!("{}_origin", name));
        let addr = fresh_var(&format!("{}_target", name));
        let gas = fresh_var(&format!("{}_gas", name));
        let callvalue = fresh_var(&format!("{}_value", name));
        let calldata_size = fresh_var(&format!("{}_calldata_size", name));
        let data = symbolic_memory::create_new_memory(
            memory,
            format!("{}_data", name),
            MemoryType::Data,
            Some(calldata_size.clone()),
        );
        let constraints = vec![];
        Transaction {
            id,
            name,
            caller,
            origin,
            addr,
            gas,
            data,
            callvalue,
            calldata_size,
            constraints,
        }
    }

    #[cfg_attr(feature = "cargo-clippy", allow(clippy::too_many_arguments))]
    fn new_outgoing(
        memory: &mut SymbolicMemory,
        id: TxId,
        name: &str,
        caller: &BVal,
        origin: &BVal,
        addr: &BVal,
        gas: &BVal,
        callvalue: &BVal,
        calldata_size: &BVal,
        returndata_size: &BVal,
    ) -> Self {
        let mut tx = Transaction::new(memory, id, name);

        tx.caller = Arc::clone(caller);
        tx.origin = Arc::clone(origin);
        tx.addr = Arc::clone(addr);
        tx.gas = Arc::clone(gas);
        tx.callvalue = Arc::clone(callvalue);
        tx.calldata_size = Arc::clone(calldata_size);

        let return_size = fresh_var(&format!("{}_returndata_size", name));
        let constraints = vec![eql(&returndata_size, &return_size)];

        tx.constraints = constraints;

        tx
    }

    fn with_sender_receiver(
        memory: &mut SymbolicMemory,
        id: TxId,
        name: &str,
        caller: &BVal,
        addr: &BVal,
    ) -> Self {
        let mut tx = Transaction::new(memory, id, name);
        let constraints = vec![
            lt(&tx.gas, &const256(MAX_GAS)),
            lt(&tx.callvalue, &const256(MAX_CALLVAL)),
            lt(&tx.calldata_size, &const256(MAX_CALLDATA_SIZE)),
        ];
        tx.constraints = constraints;
        tx.origin = Arc::clone(caller);
        tx.caller = Arc::clone(caller);
        tx.addr = Arc::clone(addr);
        tx
    }

    fn get_constraints(&self) -> Vec<BVal> {
        if self.constraints.is_empty() {
            return self.get_standard_constraints();
        }
        self.constraints.clone()
    }
    fn get_standard_constraints(&self) -> Vec<BVal> {
        vec![
            lt(&self.gas, &const256(MAX_GAS)),
            lt(&self.callvalue, &const256(MAX_CALLVAL)),
            lt(&self.calldata_size, &const256(MAX_CALLDATA_SIZE)),
        ]
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Account {
    pub id: AccountId,

    pub name: String,
    pub addr: BVal, // former our_addr
    pub balance: BVal,
    pub storage: MVal,
    pub mappings: Arc<HashMap<BVal, MVal>>,
    pub selfdestruct: bool,
    pub owner: Option<BVal>, // index for owner variable
    pub initial_storage: Option<Vec<(WU256, WU256)>>,
    pub initial_balance: Option<WU256>,
    pub initial_attacker_balance: Option<BVal>,
    code: Option<Vec<u8>>,
    codesize: usize,

    constraints: Vec<BVal>,
}

impl Account {
    fn new(memory: &mut SymbolicMemory, id: AccountId, name: &str, code: Option<Vec<u8>>) -> Self {
        let name = String::from(name);
        let addr = fresh_var(&format!("{}_account_addr", name));
        let balance = fresh_var(&format!("{}_account_balance", name));
        let storage = symbolic_memory::create_new_memory(
            memory,
            format!("{}_storage", name),
            MemoryType::Storage,
            None,
        );
        let constraints = vec![];
        let selfdestruct = false;
        let codesize = match code.clone() {
            Some(v) => v.len(),
            None => 0,
        };
        let owner = None;
        let mappings = Arc::new(HashMap::new());
        let initial_storage = None;
        let initial_balance = None;
        let initial_attacker_balance = None;

        Account {
            id,
            name,
            addr,
            balance,
            storage,
            constraints,
            selfdestruct,
            code,
            codesize,
            owner,
            mappings,
            initial_storage,
            initial_balance,
            initial_attacker_balance,
        }
    }

    // this panics on out of bound reads
    pub fn get_code_byte(&self, offset: usize) -> Option<u8> {
        self.code.as_ref().and_then(|b| Some(b[offset]))
    }

    pub fn code(&self) -> Option<&Vec<u8>> {
        self.code.as_ref()
    }

    pub fn get_codesize(&self) -> usize {
        self.codesize
    }

    fn with_addr(memory: &mut SymbolicMemory, id: AccountId, name: &str, addr: &BVal) -> Self {
        let mut acc = Account::new(memory, id, name, None);
        acc.addr = Arc::clone(addr);

        acc
    }

    fn with_addr_and_code(
        memory: &mut SymbolicMemory,
        id: AccountId,
        name: &str,
        addr: &BVal,
        code: Option<Vec<u8>>,
    ) -> Self {
        let mut acc = Account::new(memory, id, name, code);
        acc.addr = Arc::clone(addr);

        acc
    }

    fn with_addr_code_balance(
        memory: &mut SymbolicMemory,
        id: AccountId,
        name: &str,
        addr: &BVal,
        code: Option<Vec<u8>>,
        balance: &BVal,
    ) -> Self {
        let mut acc = Account::with_addr_and_code(memory, id, name, addr, code);
        acc.balance = Arc::clone(balance);

        acc
    }

    fn get_constraints(&self) -> Vec<BVal> {
        if self.constraints.is_empty() {
            return self.get_standard_constraints();
        }
        self.constraints.clone()
    }

    fn get_standard_constraints(&self) -> Vec<BVal> {
        vec![]
    }
}

fn create_parity_client() -> (ParityConnector, BlockSelector) {
    let handle = CONFIG.read().unwrap();
    let parity = handle
        .parity
        .as_ref()
        .expect("Could not create parity client");
    (ParityConnector::new(&parity.0, parity.1), parity.2)
}

impl Into<genesis::Genesis> for Env {
    fn into(self) -> genesis::Genesis {
        let mut g = genesis::Genesis::new();

        for (_, account) in self.accounts {
            g.add_account(
                BitVec::as_bigint(&account.addr).unwrap().into(),
                account.into(),
            );
        }

        g
    }
}

impl Into<genesis::Account> for Account {
    fn into(self) -> genesis::Account {
        let storage = if let Some(stor) = self.initial_storage {
            let mut s = HashMap::new();
            for (addr, value) in stor {
                s.insert(addr, value);
            }
            s
        } else {
            HashMap::new()
        };
        genesis::Account::new(
            self.initial_balance
                .unwrap_or_else(|| 10_000_000_000_000_000_000u64.into()), // pre initialize accounts with 10 ether
            self.code.map(|c| c.into()),
            0.into(), // nonce does not matter since we do not model account creation
            Some(storage),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::se::symbolic_analysis::ParityInfo;
    use std::env;

    use yaml_rust::YamlLoader;

    #[test]
    fn from_yaml_test() {
        let input = "
state:
    0x60588a9980aba5bb035cf298ea5bbf9d0c984259:
        balance: 0x10000
        nonce: 0x3
    0x780771f6a176a937e45d491d180df424d9e15fa6:
        balance: 0x10000000
        nonce: 0x1
        code_hash: 0x29164acf9a06c22bbe9da20100d94116c6ef93f44a5b58ebd6e1954c3bf436df
        code: 606060405260e060020a6000350463f5537ede8114601c575b6002565b3460025760f06004356024356044356000805433600160a060020a039081169116141560ea5783905080600160a060020a031663a9059cbb84846000604051602001526040518360e060020a0281526004018083600160a060020a0316815260200182815260200192505050602060405180830381600087803b1560025760325a03f1156002575050604080518481529051600160a060020a0386811693508716917fd0ed88a3f042c6bbb1e3ea406079b5f2b4b198afccaa535d837f4c63abbc4de6919081900360200190a35b50505050565b00
        storage_root: 0x665081a76be9ad792eec7ba0b7819e48a97cd6ab5210cae849c1ea4777ba9b6a
        storage: 
            0x0000000000000000000000000000000000000000000000000000000000000000: 0x000000000000000000000000cf40d0d2b44f2b66e07cace1372ca42b73cf21a3
            0x0000000000000000000000000000000000000000000000000000000000000001: 0x000000000000000000000000cf40d0d2b44f2b66e07cace1372ca42b73cf21a3

victim: 0x780771f6a176a937e45d491d180df424d9e15fa6";

        let yaml = YamlLoader::load_from_str(input).unwrap();
        let se_env = SeEnviroment::from_yaml(&yaml[0]);

        let vic = se_env.env.get_account(&se_env.to);

        let mut memory = symbolic_memory::new_memory();
        let mut storage = symbolic_memory::create_new_memory(
            &mut memory,
            format!("{}_storage", vic.name.clone()),
            MemoryType::Storage,
            None,
        );
        storage = word_write(
            &mut memory,
            storage,
            &const_usize(0x0),
            &const256("1183206528307683711913168901138667112513338810787"),
        );
        let other_stor = se_env.memory[vic.storage].parent();
        assert!(
            symbolic_memory::memory_info_equal(&memory[storage], &se_env.memory[other_stor]),
            "\tleft: {:?}\n\tright: {:?}",
            &memory[storage],
            &se_env.memory[vic.storage],
        );

        storage = word_write(
            &mut memory,
            storage,
            &const_usize(0x1),
            &const256("1183206528307683711913168901138667112513338810787"),
        );

        assert!(se_env.env.accounts.len() == 4);
        assert!(symbolic_memory::memory_info_equal(
            &memory[storage],
            &se_env.memory[vic.storage],
        ));
    }

    // this test needs a parity id set in env vars
    #[test]
    #[ignore]
    fn parity_load_from_blockchain_test() {
        let ip = env::var("PARITY_IP").unwrap();
        let code: Vec<u8> = vec![
            0x60, 0x60, 0x60, 0x40, 0x52, 0x36, 0x15, 0x60, 0x27, 0x57, 0x60, 0xe0, 0x60, 0x02,
            0x0a, 0x60, 0x00, 0x35, 0x04, 0x63, 0x71, 0x8d, 0xa7, 0xee, 0x81, 0x14, 0x60, 0x5b,
            0x57, 0x80, 0x63, 0xf7, 0x26, 0x0d, 0x3e, 0x14, 0x60, 0x7f, 0x57, 0x5b, 0x60, 0x7d,
            0x60, 0x00, 0x80, 0x54, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x90, 0x81, 0x16,
            0x91, 0x90, 0x30, 0x16, 0x31, 0x60, 0x60, 0x82, 0x81, 0x81, 0x81, 0x85, 0x88, 0x83,
            0xf1, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56, 0x5b, 0x60, 0x00, 0x80, 0x54, 0x73, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0x19, 0x16, 0x60, 0x04, 0x35, 0x17, 0x90, 0x55, 0x5b,
            0x00, 0x5b, 0x60, 0x9d, 0x60, 0x00, 0x54, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0x16, 0x81, 0x56, 0x5b, 0x60, 0x60, 0x90, 0x81, 0x52, 0x60, 0x20, 0x90, 0xf3,
        ];
        let balance = const_usize(0);

        // init global config with parity
        let parity = ParityInfo(ip, 8545, BlockSelector::Specific(6281955));
        CONFIG.write().unwrap().parity = Some(parity);
        let mut env = Env::new();
        let mut memory = symbolic_memory::new_memory();

        // 0x9051bF7a07B65352e3646D0e54fc2fd3CDb87c16
        let addr = U256::from_dec_str("823917711331026886531467843090272541820287745046").unwrap();
        let id = env
            .try_load_account_from_chain(&mut memory, &const_u256(addr))
            .unwrap();
        {
            let acc = env.get_account(&id);

            assert_eq!(&code, acc.code.as_ref().unwrap());
            assert_eq!(balance, acc.balance);
        }

        // 0x281055Afc982d96fAB65b3a49cAc8b878184Cb16
        let balance = const_u256(U256::from_dec_str("1538423056629367645420298").unwrap());
        let addr = U256::from_dec_str("228723907117702717599418931794880362350572260118").unwrap();
        let id = env
            .try_load_account_from_chain(&mut memory, &const_u256(addr))
            .unwrap();
        {
            let acc = env.get_account(&id);

            assert_eq!(None, acc.code.as_ref());
            assert_eq!(balance, acc.balance);
        }

        // "incorrect address"
        let balance = const_usize(0);
        let addr = U256::from_dec_str("12345").unwrap();
        let id = env
            .try_load_account_from_chain(&mut memory, &const_u256(addr))
            .unwrap();

        let acc = env.get_account(&id);

        assert_eq!(None, acc.code.as_ref());
        assert_eq!(balance, acc.balance);

        CONFIG.write().unwrap().parity = None;
    }

    #[test]
    fn update_env_for_tx_test() {
        let mut env = Env::new();
        let mut memory = symbolic_memory::new_memory();
        let from = env.new_attacker_account(&mut memory);
        let to = env.new_attacker_account(&mut memory);
        let tx_id = env.new_tx_id();
        let tx = Transaction::new(&mut memory, tx_id, "test");

        let correct_constraint;
        let correct_from_balance;
        let correct_to_balance;
        {
            // correct
            let from_acc = env.get_account(&from);
            let to_acc = env.get_account(&to);

            correct_constraint = le(&tx.callvalue, &from_acc.balance);
            correct_from_balance = sub(&from_acc.balance, &tx.callvalue);
            correct_to_balance = add(&to_acc.balance, &tx.callvalue);
        }

        env.update_env_for_tx(&from, &to, tx, tx_id);
        let from = env.get_account(&from);
        let to = env.get_account(&to);

        assert_eq!(&correct_constraint, &from.constraints[0]);
        assert_eq!(correct_from_balance, from.balance);
        assert_eq!(correct_to_balance, to.balance);
    }

    #[test]
    fn generate_address_test() {
        for _ in 0..1000 {
            let addr = FVal::as_bigint(&generate_random_address()).unwrap();
            assert!(addr.bits() <= 160);
        }
    }
}
