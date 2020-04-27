use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::sync::{Arc, Mutex};

use lazy_static::lazy_static;
use regex::Regex;

use crate::se::{
    env::fresh_var_name,
    expr::{bval::*, symbolic_memory::*},
    symbolic_state::ReadTracker,
};

lazy_static! {
    pub static ref KECCAK_STATS: Mutex<KeccakStats> = Mutex::new(KeccakStats::new());
}

pub struct KeccakStats {
    known: HashSet<(Keccak, Keccak)>,
    sophisticated: usize,
    ackerman: usize,
}

impl fmt::Debug for KeccakStats {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Sophisticated: {}; Ackerman: {}",
            self.sophisticated, self.ackerman
        )
    }
}

impl KeccakStats {
    fn new() -> Self {
        let known = HashSet::new();
        let sophisticated = 0;
        let ackerman = 0;
        Self {
            known,
            sophisticated,
            ackerman,
        }
    }

    fn sophisticated(&mut self, pair: (Keccak, Keccak)) {
        if !self.known.contains(&pair) {
            self.known.insert(pair);
            self.sophisticated += 1;
        }
    }

    fn ackerman(&mut self, pair: (Keccak, Keccak)) {
        if !self.known.contains(&pair) {
            self.known.insert(pair);
            self.ackerman += 1;
        }
    }
}

#[derive(Debug)]
pub struct SmtLib2Builder<'a> {
    subexpr: HashMap<BVal, String>,
    known_vars: BTreeSet<String>,
    constraints: &'a [BVal],
    memories: HashSet<MVal>,
    defs: BTreeSet<String>,
    asserts: BTreeSet<String>,
    subexpr_id: usize,
    reads: &'a ReadTracker,
    memory: &'a SymbolicMemory,
    read_cache: &'a mut HashMap<MVal, HashSet<BVal>>,
    keccaks: HashSet<Keccak>,
}

#[derive(Hash, Clone, Eq, PartialEq, Debug)]
struct Keccak {
    val: BVal,
    memory: MVal,
    offset: BVal,
    len: BVal,
}

impl<'a> SmtLib2Builder<'a> {
    fn new(
        reads: &'a ReadTracker,
        memory: &'a SymbolicMemory,
        read_cache: &'a mut HashMap<MVal, HashSet<BVal>>,
        constraints: &'a [BVal],
    ) -> Self {
        let subexpr = HashMap::new();
        let known_vars = BTreeSet::new();
        let memories = HashSet::new();
        let defs = BTreeSet::new();
        let asserts = BTreeSet::new();
        let subexpr_id = 0;
        let keccaks = HashSet::new();
        Self {
            subexpr,
            known_vars,
            constraints,
            memories,
            defs,
            asserts,
            subexpr_id,
            reads,
            memory,
            keccaks,
            read_cache,
        }
    }

    pub fn initialize_from_constraints(
        reads: &'a ReadTracker,
        memory: &'a SymbolicMemory,
        read_cache: &'a mut HashMap<MVal, HashSet<BVal>>,
        constraints: &'a [BVal],
    ) -> Self {
        let mut g = SmtLib2Builder::new(reads, memory, read_cache, constraints);
        g.process_constrains();
        g
    }

    pub fn defs(&self) -> &BTreeSet<String> {
        &self.defs
    }

    pub fn asserts(&self) -> &BTreeSet<String> {
        &self.asserts
    }

    pub fn process_constrains(&mut self) {
        self.constraints
            .iter()
            .for_each(|val| self.assert_bval(val));

        let mut len = self.memories.len();
        loop {
            for mem in self.memories.clone() {
                self.assert_memory_versions(mem);
            }

            // did not discover new memories during processing
            if self.memories.len() == len {
                break;
            }
            len = self.memories.len();
        }
        if cfg!(feature = "keccak") {
            self.encode_keccak();
        }
    }

    fn encode_keccak(&mut self) {
        for i in self.keccaks.clone().iter() {
            for j in self.keccaks.clone().iter() {
                if i == j {
                    continue;
                } else if let SymbolicTruth::True = FVal::check_truth(&neql(&i.len, &j.len)) {
                    // if we can trivially disprove that two keccak could be the same value, encode
                    // them as unequal
                    let encoded =
                        format!("(distinct {} {})", self.to_smt(&i.val), self.to_smt(&j.val));
                    self.assert(&encoded);

                    if cfg!(feature = "stats") {
                        let mut handle = KECCAK_STATS.lock().unwrap();
                        handle.sophisticated((i.clone(), j.clone()));
                    }
                } else if let SymbolicTruth::False = FVal::check_truth(&neql(&i.len, &j.len)) {
                    // if we can prove the that the length is equal, both values have to be
                    // constant, however since we could obviously not compute the values in earlier
                    // optimization passes, at least one memory value must be symbolic
                    if let Some(ite) = self.construct_ite_keccak_encoding(&i, &j) {
                        self.assert(&ite);
                    } else {
                        let encoded =
                            format!("(distinct {} {})", self.to_smt(&i.val), self.to_smt(&j.val));
                        self.assert(&encoded);
                    }
                    if cfg!(feature = "stats") {
                        let mut handle = KECCAK_STATS.lock().unwrap();
                        handle.sophisticated((i.clone(), j.clone()));
                    }
                } else {
                    // (=> (= i_len j_len) (= i j) )
                    let l = eql(&i.len, &j.len);
                    let r = eql(&i.val, &j.val);
                    let imp = implies(&l, &r);
                    let encoded = self.to_smt(&imp);
                    self.assert(&encoded);

                    // (=> (distinct i_len j_len (distinct i j) )
                    let l = neql(&i.len, &j.len);
                    let r = neql(&i.val, &j.val);
                    let imp = implies(&l, &r);
                    let encoded = self.to_smt(&imp);
                    self.assert(&encoded);
                    if cfg!(feature = "stats") {
                        let mut handle = KECCAK_STATS.lock().unwrap();
                        handle.ackerman((i.clone(), j.clone()));
                    }
                }
            }
        }
    }

    // we have to do the concat in strings, because I'm way to lazy to implement this properly
    fn construct_ite_keccak_encoding(&mut self, a: &Keccak, b: &Keccak) -> Option<String> {
        let (a_len, b_len) = (
            FVal::as_usize(&a.len).unwrap(),
            FVal::as_usize(&a.len).unwrap(),
        );
        assert!(a_len == b_len);
        let mut last = format!("(= {} {})", self.to_smt(&a.val), self.to_smt(&b.val));
        let abort = format!("(distinct {} {})", self.to_smt(&a.val), self.to_smt(&b.val));
        for i in 0..a_len {
            let a_load = mload8(&self.memory, a.memory, &add(&a.offset, &const_usize(i)));
            let b_load = mload8(&self.memory, b.memory, &add(&b.offset, &const_usize(i)));
            let condition = eql(&a_load, &b_load);

            // if we can disprove one memory location we can conclude the hashes to be different
            if let SymbolicTruth::False = FVal::check_truth(&condition) {
                return None;
            }
            // lift condition to bv256
            let condition = format!(
                "(= (concat (_ bv0 248) {}) (concat (_ bv0 248) {}) )",
                self.to_smt(&a_load),
                self.to_smt(&b_load)
            );
            last = format!("(ite {} {} {})", condition, last, abort);
        }

        Some(last)
    }

    fn push_memory(&mut self, mem: MVal) {
        if self.memories.contains(&mem) {
            return;
        }
        self.memories.insert(mem);
    }

    fn assert_bval(&mut self, val: &BVal) {
        // if we can trivially prove correctness do not consider
        if let SymbolicTruth::True = FVal::check_truth(val) {
            return;
        }
        let b = self.to_bool(val, bval_size(val));
        self.assert(&b);
    }

    #[cfg_attr(feature = "cargo-clippy", allow(clippy::wrong_self_convention))]
    fn to_bool(&mut self, v: &BVal, size: usize) -> String {
        optimize_bool_conversion(format!("(distinct {} (_ bv0 {}))", self.to_smt(v), size))
    }

    #[cfg_attr(feature = "cargo-clippy", allow(clippy::wrong_self_convention))]
    fn from_bool(&mut self, val: &str, size: usize) -> String {
        format!("(ite {} (_ bv1 {}) (_ bv0 {}))", val, size, size)
    }

    fn assert(&mut self, val: &str) {
        self.asserts.insert(format!("(assert {} )", val));
    }

    fn var(&mut self, name: &str, size: usize) -> String {
        if !self.known_vars.contains(name) {
            self.defs
                .insert(format!("(declare-const {} (_ BitVec {}))", name, size));
            self.known_vars.insert(name.into());
        }
        name.into()
    }

    #[cfg_attr(feature = "cargo-clippy", allow(clippy::wrong_self_convention))]
    pub fn to_smt(&mut self, val: &BVal) -> String {
        if let Some(str) = self.subexpr.get(val) {
            return str.clone();
        }
        let mut res = self.smtlib2_encoding(val);
        if Arc::strong_count(val) > 1 && val.can_be_subexpr() {
            let var = format!("sub_{}", self.get_subexpr_id());
            self.var(&var, FVal::get_size(val));
            self.assert(&format!("(= {} {})", var, res));
            self.subexpr.insert(val.clone(), var.clone());
            res = var;
        }
        res
    }

    fn bin_op(&mut self, name: &str, l: &BVal, r: &BVal) -> String {
        format!("({} {} {})", name, self.to_smt(l), self.to_smt(r))
    }

    fn get_subexpr_id(&mut self) -> usize {
        self.subexpr_id += 1;
        self.subexpr_id
    }

    fn def_array(&mut self, name: &str, size: usize) {
        self.defs.insert(format!(
            "(declare-const {} (Array (_ BitVec 256) (_ BitVec {})))",
            name, size
        ));
    }

    pub fn debug_output(&self) -> String {
        let mut debug_ouput = String::new();
        let mut line_counter = 0;

        let numbered_output = |ctr: &mut usize, s: String| {
            let mut output = String::new();
            for line in s.lines() {
                output.push_str(&format!("{}:\t{}\n", *ctr, line));
                *ctr += 1;
            }
            output
        };

        let defs = self
            .defs
            .iter()
            .cloned()
            .collect::<Vec<String>>()
            .join("\n");
        let asserts = self
            .asserts
            .iter()
            .cloned()
            .collect::<Vec<String>>()
            .join("\n");

        debug_ouput.push_str(&numbered_output(&mut line_counter, defs));
        debug_ouput.push_str(&numbered_output(&mut line_counter, asserts));
        format!("Generated SMTLib Formula:\n{}", debug_ouput)
    }

    fn assert_memory_versions(&mut self, node: MVal) {
        if self.memory[node].memory_type == MemoryType::Storage {
            return self.assert_storage_versions(node);
        }
        self.assert_memory(node);
    }

    fn assert_storage_versions(&mut self, node: MVal) {
        self.memories.insert(node);
        let op = self.memory[node].op.clone();
        let name = self.memory[node].name();
        match op {
            MemoryOperation::Write256 {
                parent: par,
                address: ref waddr,
                value: ref val,
            } => {
                // recursively collect prior updates
                self.assert_storage_versions(par);

                let assert = &format!(
                    "(= {} (store {} {} {}))",
                    &name,
                    self.memory[par].name(),
                    self.to_smt(waddr),
                    self.to_smt(val)
                );
                self.assert(assert);
                self.def_array(&name, 256);
            }
            MemoryOperation::Init => {
                self.def_array(&name, 256);
            }
            MemoryOperation::MemsetUnlimited {
                parent: par,
                index: ref waddr,
                value: ref val,
            } => {
                // recursively collect prior updates
                self.assert_storage_versions(par);

                let reads =
                    get_needed_read_indices_cached(self.reads, self.memory, par, self.read_cache);

                for r in reads {
                    let load = self.to_smt(&sload(self.memory, node, &r));
                    let ite_load = sload(self.memory, par, &r);
                    let ite = self.to_smt(&ite(&le(waddr, &r), val, &ite_load));

                    self.assert(&format!("(= {} {})", &load, &ite));
                }

                self.def_array(&name, 256);
            }
            _ => unreachable!(),
        }
    }

    fn assert_memory(&mut self, node: MVal) {
        self.memories.insert(node);
        let op = self.memory[node].op.clone();
        let name = self.memory[node].name();
        match op {
            MemoryOperation::Write8 {
                parent: par,
                address: ref waddr,
                value: ref val,
            } => {
                // recursively collect prior updates
                self.assert_memory(par);

                let assert = &format!(
                    "(= {} (store {} {} ((_ extract 7 0) {} ) ) )",
                    name,
                    self.memory[par].name(),
                    self.to_smt(waddr),
                    self.to_smt(val)
                );
                self.assert(assert);
                self.def_array(&name, 8);
            }
            MemoryOperation::Write256 {
                parent: par,
                address: ref waddr,
                value: ref val,
            } => {
                // recursively collect prior updates
                self.assert_memory(par);

                let mut store_string = self.memory[par].name();
                for offset in 0..32 {
                    // try to get constant addr
                    let addr = match FVal::as_usize(&add(waddr, &const_usize(offset))) {
                        Some(a) => self.to_smt(&const_usize(a)),
                        None => self.to_smt(&add(waddr, &const_usize(offset))),
                    };

                    let val = format!(
                        "((_ extract {} {}) {})",
                        (((31 - offset) + 1) * 8) - 1,
                        (31 - offset) * 8,
                        self.to_smt(val)
                    );
                    store_string = format!("(store {} {} {} ) ", store_string, addr, val);
                }
                self.assert(&format!("(= {} {})", store_string, name));
                self.def_array(&name, 8);
            }
            MemoryOperation::Init => {
                self.def_array(&name, 8);
            }
            MemoryOperation::Memset {
                parent: par,
                index: ref waddr,
                value: ref val,
                ref size,
            } => {
                // recursively collect prior updates
                self.assert_memory(par);

                let reads =
                    get_needed_read_indices_cached(self.reads, self.memory, node, self.read_cache);

                for r in reads {
                    // encode complete range
                    let load = self.to_smt(&mload8(self.memory, node, &r));
                    let ite_load = mload8(self.memory, par, &r);

                    let ite = self.to_smt(&ite(
                        &and(&le(waddr, &r), &lt(&r, &add(waddr, size))),
                        &byte_extract(val, &zero()),
                        &ite_load,
                    ));

                    self.assert(&format!("(= {} {})", &load, &ite));
                }

                self.def_array(&name, 8);
            }
            MemoryOperation::MemsetUnlimited {
                parent: par,
                index: ref waddr,
                value: ref val,
            } => {
                // recursively collect prior updates
                self.assert_memory(par);

                let reads =
                    get_needed_read_indices_cached(self.reads, self.memory, node, self.read_cache);

                for r in reads {
                    let load = self.to_smt(&mload8(self.memory, node, &r));
                    let ite_load = mload8(self.memory, par, &r);
                    let ite =
                        self.to_smt(&ite(&le(waddr, &r), &byte_extract(val, &zero()), &ite_load));

                    self.assert(&format!("(= {} {})", &load, &ite));
                }

                self.def_array(&name, 8);
            }
            MemoryOperation::Memcopy {
                parent: par,
                from,
                index: ref waddr,
                index_from: ref from_addr,
                ref size,
            } => {
                // recursively collect prior updates
                self.assert_memory(par);
                self.assert_memory(from);

                let reads =
                    get_needed_read_indices_cached(self.reads, self.memory, node, self.read_cache);

                for r in reads {
                    let load = self.to_smt(&mload8(self.memory, node, &r));
                    let ite_load_lhs = mload8(self.memory, par, &r);
                    let ite_load_rhs = mload8(self.memory, from, &add(from_addr, &sub(&r, waddr)));
                    let ite = self.to_smt(&ite(
                        &and(&le(waddr, &r), &lt(&r, &add(waddr, size))),
                        &ite_load_rhs,
                        &ite_load_lhs,
                    ));

                    self.assert(&format!("(= {} {})", &load, &ite));
                }

                self.def_array(&name, 8);
            }
            _ => panic!("Not supported memory assertion"),
        }
    }

    fn smtlib2_encoding(&mut self, val: &BVal) -> String {
        match val.val() {
            Val256::FAdd(ref l, ref r) => self.bin_op("bvadd", l, r),
            Val256::FSub(ref l, ref r) => self.bin_op("bvsub", l, r),
            Val256::FMul(ref l, ref r) => self.bin_op("bvmul", l, r),
            Val256::FDiv(ref l, ref r) => self.bin_op("bvudiv", l, r),
            Val256::FSDiv(ref l, ref r) => self.bin_op("bvsdiv", l, r),
            Val256::FMod(ref l, ref r) => self.bin_op("bvurem", l, r),
            Val256::FSMod(ref l, ref r) => self.bin_op("bvsmod", l, r),
            Val256::FExp(ref l, ref r) => {
                debug_assert!(FVal::as_usize(&l).unwrap() == 2);
                self.bin_op("bvshl", l, &sub(r, &const_usize(1)))
            }
            Val256::FITE(ref c, ref t, ref e) => format!(
                "(ite {} {} {})",
                self.to_bool(c, bval_size(c)),
                self.to_smt(t),
                self.to_smt(e)
            ),
            Val256::FAnd(ref l, ref r) => self.bin_op("bvand", l, r),
            Val256::FOr(ref l, ref r) => self.bin_op("bvor", l, r),
            Val256::FXor(ref l, ref r) => self.bin_op("bvxor", l, r),
            Val256::FNot(ref v) => format!("(bvnot {})", self.to_smt(v)),
            Val256::FConst(ref string) | Val256::FConst8(ref string) => {
                format!("(_ bv{} {})", string, FVal::get_size(val))
            }
            Val256::FVarRef(ref name) => self.var(name, 256),
            Val256::FLt(ref l, ref r) => {
                debug_assert!(
                    FVal::get_size(l) == FVal::get_size(r),
                    "Comparing two different sized variables: {:?} {:?}",
                    l,
                    r
                );
                let bv = format!("(bvult {} {})", self.to_smt(l), self.to_smt(r));
                self.from_bool(&bv, FVal::get_size(l))
            }
            Val256::FLe(ref l, ref r) => {
                debug_assert!(
                    FVal::get_size(l) == FVal::get_size(r),
                    "Comparing two different sized variables: {:?} {:?}",
                    l,
                    r
                );
                let bv = format!("(bvule {} {})", self.to_smt(l), self.to_smt(r));
                self.from_bool(&bv, FVal::get_size(l))
            }
            Val256::FSLt(ref l, ref r) => {
                debug_assert!(
                    FVal::get_size(l) == FVal::get_size(r),
                    "Comparing two different sized variables: {:?} {:?}",
                    l,
                    r
                );
                let bv = format!("(bvslt {} {})", self.to_smt(l), self.to_smt(r));
                self.from_bool(&bv, FVal::get_size(l))
            }
            Val256::FEql(ref l, ref r) => {
                debug_assert!(
                    FVal::get_size(l) == FVal::get_size(r),
                    "Comparing two different sized variables: {:?} {:?}",
                    l,
                    r
                );
                let bv = format!("(= {} {})", self.to_smt(l), self.to_smt(r));
                self.from_bool(&bv, FVal::get_size(l))
            }
            Val256::FNEql(ref l, ref r) => {
                debug_assert!(
                    FVal::get_size(l) == FVal::get_size(r),
                    "Comparing two different sized variables: {:?} {:?}",
                    l,
                    r
                );
                let bv = format!("(distinct {} {})", self.to_smt(l), self.to_smt(r));
                self.from_bool(&bv, FVal::get_size(l))
            }
            Val256::FImplies(ref l, ref r) => format!(
                "(=> {} {})",
                self.to_bool(l, FVal::get_size(l)),
                self.to_bool(r, FVal::get_size(r))
            ),
            Val256::FMLoad(mem, ref addr) | Val256::FSLoad(mem, ref addr) => {
                self.push_memory(*mem);
                format!(
                    "(select {} {} )",
                    self.memory[*mem].name(),
                    self.to_smt(addr)
                )
            }
            Val256::FByteAt(ref val, ref offset) => {
                let o = self.to_smt(&mul(offset, &const_usize(8)));
                format!(
                    "(concat (_ bv0 248) ((_ extract 7 0) (bvlshr {} (bvmul {} (_ bv8 256) )) ))",
                    self.to_smt(val),
                    o
                )
            }
            Val256::FByteExtract(ref val, ref offset) => {
                let o = self.to_smt(&mul(offset, &const_usize(8)));
                format!(
                    "((_ extract 7 0) (bvlshr {} (bvmul {} (_ bv8 256) )) )",
                    self.to_smt(val),
                    o
                )
            }
            Val256::FAShr(ref val, ref size) => {
                format!("(bvashr {} {})", self.to_smt(val), self.to_smt(size))
            }
            Val256::FLShr(ref val, ref size) => {
                format!("(bvlshr {} {})", self.to_smt(val), self.to_smt(size))
            }
            Val256::FShl(ref val, ref size) => {
                format!("(bvshl {} {})", self.to_smt(val), self.to_smt(size))
            }
            Val256::FCombine32(ref loads) => {
                debug_assert!(loads.len() == 32);
                let mut concat = String::from("(concat ");
                for load in loads {
                    concat.push_str(&format!(" {} ", &self.to_smt(load)));
                }
                concat.push_str(")");
                concat
            }
            Val256::FSHA3(mem, ref offset, ref len) => {
                self.push_memory(*mem);
                let kec = Keccak {
                    val: Arc::clone(val),
                    memory: *mem,
                    offset: Arc::clone(offset),
                    len: Arc::clone(len),
                };
                self.keccaks.insert(kec);
                self.var(&fresh_var_name("sha3_res"), 256)
            }
        }
    }
}

lazy_static! {
    static ref RE: Regex =
        Regex::new(r"\(distinct \(ite (.*) \(_ bv1 256\) \(_ bv0 256\)\) \(_ bv0 256\)\)").unwrap();
}

fn optimize_bool_conversion(s: String) -> String {
    if let Some(cap) = RE.captures(&s) {
        return cap[1].into();
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::iter::FromIterator;
    use std::sync::Arc;

    use crate::bytecode::Instr;
    use crate::se::expr::symbolic_memory::{self, word_write};
    use crate::CONFIG;

    use crate::test_helpers::generate_test_graph;

    #[test]
    fn assert_memory_versions_normal_test() {
        let ins = vec![];

        let g = generate_test_graph(ins);
        let mut state = g.get_state_by_id(1).clone();

        let mem_init = symbolic_memory::create_new_memory(
            Arc::make_mut(&mut state.memory),
            "test_memory".to_string(),
            MemoryType::Memory,
            None,
        );
        let mem = word_write(
            Arc::make_mut(&mut state.memory),
            mem_init,
            &const_usize(10),
            &const_usize(5),
        );
        let constraints = vec![];
        let mut read_cache = HashMap::new();
        let mut smt2 =
            SmtLib2Builder::new(&state.reads, &state.memory, &mut read_cache, &constraints);
        smt2.assert_memory_versions(mem);

        let memory = symbolic_memory::new_memory();
        let mut read_cache_2 = HashMap::new();
        let mut smt2_correct =
            SmtLib2Builder::new(&state.reads, &memory, &mut read_cache_2, &constraints);
        smt2_correct.def_array("test_memory_0", 8);
        smt2_correct.def_array("test_memory_1", 8);
        smt2_correct.def_array("test_memory_2", 8);
        smt2_correct.assert("(= (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store test_memory_1 (_ bv10 256) ((_ extract 255 248) (_ bv5 256)) )  (_ bv11 256) ((_ extract 247 240) (_ bv5 256)) )  (_ bv12 256) ((_ extract 239 232) (_ bv5 256)) )  (_ bv13 256) ((_ extract 231 224) (_ bv5 256)) )  (_ bv14 256) ((_ extract 223 216) (_ bv5 256)) )  (_ bv15 256) ((_ extract 215 208) (_ bv5 256)) )  (_ bv16 256) ((_ extract 207 200) (_ bv5 256)) )  (_ bv17 256) ((_ extract 199 192) (_ bv5 256)) )  (_ bv18 256) ((_ extract 191 184) (_ bv5 256)) )  (_ bv19 256) ((_ extract 183 176) (_ bv5 256)) )  (_ bv20 256) ((_ extract 175 168) (_ bv5 256)) )  (_ bv21 256) ((_ extract 167 160) (_ bv5 256)) )  (_ bv22 256) ((_ extract 159 152) (_ bv5 256)) )  (_ bv23 256) ((_ extract 151 144) (_ bv5 256)) )  (_ bv24 256) ((_ extract 143 136) (_ bv5 256)) )  (_ bv25 256) ((_ extract 135 128) (_ bv5 256)) )  (_ bv26 256) ((_ extract 127 120) (_ bv5 256)) )  (_ bv27 256) ((_ extract 119 112) (_ bv5 256)) )  (_ bv28 256) ((_ extract 111 104) (_ bv5 256)) )  (_ bv29 256) ((_ extract 103 96) (_ bv5 256)) )  (_ bv30 256) ((_ extract 95 88) (_ bv5 256)) )  (_ bv31 256) ((_ extract 87 80) (_ bv5 256)) )  (_ bv32 256) ((_ extract 79 72) (_ bv5 256)) )  (_ bv33 256) ((_ extract 71 64) (_ bv5 256)) )  (_ bv34 256) ((_ extract 63 56) (_ bv5 256)) )  (_ bv35 256) ((_ extract 55 48) (_ bv5 256)) )  (_ bv36 256) ((_ extract 47 40) (_ bv5 256)) )  (_ bv37 256) ((_ extract 39 32) (_ bv5 256)) )  (_ bv38 256) ((_ extract 31 24) (_ bv5 256)) )  (_ bv39 256) ((_ extract 23 16) (_ bv5 256)) )  (_ bv40 256) ((_ extract 15 8) (_ bv5 256)) )  (_ bv41 256) ((_ extract 7 0) (_ bv5 256)) )  test_memory_2)");

        assert_eq!(smt2_correct.asserts(), smt2.asserts());
        assert_eq!(smt2_correct.defs(), smt2.defs());
    }

    #[test]
    fn assert_memory_memcopy() {
        let ins = vec![];

        let g = generate_test_graph(ins);
        let mut state = g.get_state_by_id(1).clone();
        let mem;
        {
            let mem_ = state.mem;
            let data_ = state.input_tx().data;
            let memory_ptr = Arc::make_mut(&mut state.memory);

            mem = memcopy(
                memory_ptr,
                mem_,
                data_,
                &const_usize(0),
                &const_usize(0),  // index data
                &const_usize(32), // size
            );
        }

        let load = mload(&state.memory, mem, &const_usize(0));
        state.record_read(&load);
        state.mem = mem;

        assert_eq!(true, state.check_sat());

        let input_tx = state.input_tx().clone();
        let load = mload(&state.memory, input_tx.data, &const_usize(0));
        state.push_constraint(eql(&load, &const_usize(5)));
        let mem = state.mem;
        let load = mload(&state.memory, mem, &const_usize(0));
        state.push_constraint(neql(&load, &const_usize(5)));

        assert_eq!(false, state.check_sat());
    }

    #[test]
    fn load_encode_test() {
        let ins = vec![Instr::IPush(vec![0x00]), Instr::IMLoad];
        let g = generate_test_graph(ins);
        let state = &g.get_state_by_id(3);

        let constraints = vec![];
        let mut read_cache = HashMap::new();
        let mut smt2 =
            SmtLib2Builder::new(&state.reads, &state.memory, &mut read_cache, &constraints);
        smt2.assert_memory_versions(state.mem);

        let name = state.account().name.clone();

        let correct = BTreeSet::from_iter(vec![
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv0 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv1 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv2 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv3 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv4 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv5 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv6 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv7 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv8 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv9 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv10 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv11 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv12 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv13 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv14 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv15 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv16 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv17 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv18 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv19 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv20 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv21 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv22 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv23 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv24 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv25 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv26 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv27 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv28 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv29 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv30 256) ) (_ bv0 8)) )",
                name
            ),
            format!(
                "(assert (= (select {}_mem_1_1 (_ bv31 256) ) (_ bv0 8)) )",
                name
            ),
        ]);
        assert_eq!(correct, *smt2.asserts());
    }

    #[test]
    fn storage_encode_test() {
        let ins = vec![
            Instr::IPush(vec![0x00]),
            Instr::ISLoad,
            Instr::IPush(vec![0x01]),
            Instr::IPush(vec![0x10]),
            Instr::ISStore,
            Instr::IPush(vec![0x10]),
            Instr::ISLoad,
        ];
        let g = generate_test_graph(ins);
        let state = &g.get_state_by_id(8);

        let constraints = vec![];
        let mut read_cache = HashMap::new();
        let mut smt2 =
            SmtLib2Builder::new(&state.reads, &state.memory, &mut read_cache, &constraints);
        smt2.assert_memory_versions(state.account().storage);

        let correct = vec![
            format!(
                "(assert (= (select {}_storage_1 (_ bv16 256) ) (_ bv0 256)) )",
                state.account().name
            ),
            format!(
                "(assert (= (select {}_storage_1 (_ bv0 256) ) (_ bv0 256)) )",
                state.account().name
            ),
            format!(
                "(assert (= {}_storage_2 (store {}_storage_1 (_ bv16 256) (_ bv1 256))) )",
                state.account().name,
                state.account().name
            ),
        ];

        assert_eq!(BTreeSet::from_iter(correct), *smt2.asserts());
    }

    #[test]
    fn byte_at_to_smt_test() {
        let ins = vec![];
        CONFIG.write().unwrap().disable_optimizations = true;
        let g = generate_test_graph(ins);
        let state = &g.get_state_by_id(1);
        let mut read_cache = HashMap::new();
        let constraints = vec![];
        let mut smt2 =
            SmtLib2Builder::new(&state.reads, &state.memory, &mut read_cache, &constraints);

        let val = byte_at(&const_usize(0x41414141), &const_usize(2));
        let corr = "(concat (_ bv0 248) ((_ extract 7 0) (bvlshr (_ bv1094795585 256) (bvmul (bvmul (_ bv2 256) (_ bv8 256)) (_ bv8 256) )) ))";
        assert_eq!(corr, smt2.smtlib2_encoding(&val));
        CONFIG.write().unwrap().disable_optimizations = false;
    }
}
