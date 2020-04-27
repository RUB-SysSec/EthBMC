use std::collections::hash_map::DefaultHasher;
use std::fmt;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::{BitAnd, BitOr, BitXor};
use std::sync::{Arc, RwLock};

use tiny_keccak::keccak256;
use uint::U256;

use crate::se::env::fresh_var_name;
use crate::se::expr::symbolic_memory::{MVal, MemoryOperation, MemoryType, SymbolicMemory};
use crate::se::symbolic_analysis::CONFIG;

#[macro_export]
macro_rules! matches {
    ($e:expr, $p:pat) => {
        match $e.val() {
            $p => true,
            _ => false,
        }
    };
}

#[cfg(test)]
pub fn compare_bval(a: &BVal, b: &BVal) -> bool {
    match (&a.val, &b.val) {
        (Val256::FMLoad(_, ref addr_a), Val256::FMLoad(_, ref addr_b))
        | (Val256::FSLoad(_, ref addr_a), Val256::FSLoad(_, ref addr_b)) => addr_a == addr_b,
        (Val256::FSHA3(_, ref addr_a, ref val_a), Val256::FSHA3(_, ref addr_b, ref val_b)) => {
            addr_a == addr_b && val_a == val_b
        }
        (Val256::FCombine32(ref v_a), Val256::FCombine32(ref v_b)) => {
            for i in 0..32 {
                if !compare_bval(&v_a[i], &v_b[i]) {
                    return false;
                }
            }
            true
        }
        _ => a == b,
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Val256 {
    FAdd(BVal, BVal),
    FSub(BVal, BVal),
    FMul(BVal, BVal),
    FDiv(BVal, BVal),
    FSDiv(BVal, BVal),
    FMod(BVal, BVal),
    FSMod(BVal, BVal),
    FExp(BVal, BVal),
    FITE(BVal, BVal, BVal),
    FLt(BVal, BVal),
    FSLt(BVal, BVal),
    FLe(BVal, BVal),
    FEql(BVal, BVal),
    FNEql(BVal, BVal),
    FImplies(BVal, BVal),
    FAnd(BVal, BVal),
    FOr(BVal, BVal),
    FXor(BVal, BVal),
    FNot(BVal),
    FByteAt(BVal, BVal),
    FByteExtract(BVal, BVal),
    FShl(BVal, BVal),
    FAShr(BVal, BVal),
    FLShr(BVal, BVal),
    FConst(U256),
    FConst8(U256),
    FVarRef(String),
    FMLoad(MVal, BVal),
    FSLoad(MVal, BVal),
    FSHA3(MVal, BVal, BVal),
    FCombine32(Vec<BVal>),
}

pub trait BitVec {
    fn val(&self) -> &Val256;

    fn get_size(_: &Arc<Self>) -> usize;
    fn as_bigint(_: &Arc<Self>) -> Option<U256>;
    fn as_const8(_: &Arc<Self>) -> Option<BVal>;

    fn simplified(_: &Arc<Self>) -> Arc<Self>;

    fn can_be_subexpr(&self) -> bool {
        match self.val() {
            Val256::FVarRef(_) | Val256::FConst8(_) | Val256::FConst(_) => false,
            _ => true,
        }
    }

    fn as_usize(val: &Arc<Self>) -> Option<usize> {
        BitVec::as_bigint(val).and_then(|bi| {
            if bi.bits() <= 64 {
                Some(bi.as_u64() as usize)
            } else {
                None
            }
        })
    }

    fn is_tautology(val: &Arc<Self>) -> bool {
        match BitVec::check_truth(val) {
            SymbolicTruth::True => true,
            _ => false,
        }
    }
    fn check_truth(val: &Arc<Self>) -> SymbolicTruth {
        if let Some(v) = BitVec::as_bigint(val) {
            if v != U256::zero() {
                return SymbolicTruth::True;
            }
            return SymbolicTruth::False;
        }
        SymbolicTruth::Maybe
    }

    fn is_constant(val: &Arc<Self>) -> bool {
        if BitVec::as_bigint(val).is_some() {
            return true;
        }
        false
    }
}

pub type BVal = Arc<FVal>;

#[derive(Clone)]
pub struct FVal {
    val: Val256,
    cached_hash: Arc<RwLock<Option<u64>>>,
}

// implement Hash, PartialEq and Eq by hand only for val, since simpl does only store the result of
// the simpl query and does not actually determine these properties
impl Hash for FVal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // compute hash first and in subsequent runs compute hash(hash) which is still unique for
        // second-preimage resistant hash functions
        if self.cached_hash.read().unwrap().is_none() {
            let mut hasher = DefaultHasher::new();
            self.val.hash(&mut hasher);
            let hash = hasher.finish();
            *self.cached_hash.write().unwrap() = Some(hash);
            return hash.hash(state);
        }
        self.cached_hash.read().unwrap().unwrap().hash(state)
    }
}

impl PartialEq for FVal {
    fn eq(&self, other: &FVal) -> bool {
        let mut hasher_1 = DefaultHasher::new();
        let mut hasher_2 = DefaultHasher::new();

        self.hash(&mut hasher_1);
        other.hash(&mut hasher_2);
        hasher_1.finish() == hasher_2.finish()
    }
}

// marker trait
impl Eq for FVal {}

impl BitVec for FVal {
    fn val(&self) -> &Val256 {
        &self.val
    }

    fn get_size(val: &BVal) -> usize {
        match val.val {
            Val256::FMLoad(..) | Val256::FConst8(..) | Val256::FByteExtract(..) => 8,
            _ => 256,
        }
    }

    fn as_bigint(val: &BVal) -> Option<U256> {
        match FVal::simplified(val).val {
            Val256::FConst(ref uint) | Val256::FConst8(ref uint) => Some(*uint),
            _ => None,
        }
    }

    fn as_const8(val: &BVal) -> Option<BVal> {
        let v = FVal::simplified(val);
        if let Val256::FConst8(_) = v.val {
            return Some(v);
        }
        if let Val256::FConst(ref v) = v.val {
            if v.bits() <= 8 {
                return Some(Arc::new(FVal::new(Val256::FConst8(*v))));
            }
        }
        None
    }

    fn simplified(val: &BVal) -> BVal {
        if val.memory_val() {
            Arc::clone(val)
        } else {
            simpl(val)
        }
    }
}

impl FVal {
    fn new(val: Val256) -> Self {
        let cached_hash = Arc::new(RwLock::new(None));
        Self { val, cached_hash }
    }

    fn memory_val(&self) -> bool {
        match self.val {
            Val256::FMLoad(..)
            | Val256::FSLoad(..)
            | Val256::FSHA3(..)
            | Val256::FCombine32(..) => true,
            _ => false,
        }
    }
}

impl Debug for FVal {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match self.val {
            Val256::FAdd(ref a, ref b) => write!(f, "( {:?} + {:?} )", a, b),
            Val256::FSub(ref a, ref b) => write!(f, "( {:?} - {:?} )", a, b),
            Val256::FMul(ref a, ref b) => write!(f, "( {:?} * {:?} )", a, b),
            Val256::FDiv(ref a, ref b) => write!(f, "( {:?} / {:?} )", a, b),
            Val256::FSDiv(ref a, ref b) => write!(f, "( {:?} s/ {:?} )", a, b),
            Val256::FMod(ref a, ref b) => write!(f, "( {:?} % {:?} )", a, b),
            Val256::FSMod(ref a, ref b) => write!(f, "( {:?} s% {:?} )", a, b),
            Val256::FExp(ref a, ref b) => write!(f, "( {:?} ** {:?} )", a, b),
            Val256::FITE(ref cond, ref thenv, ref elsev) => {
                write!(f, "if {:?} then {:?} else {:?}", cond, thenv, elsev)
            }
            Val256::FLt(ref a, ref b) => write!(f, "( {:?} < {:?} )", a, b),
            Val256::FSLt(ref a, ref b) => write!(f, "( {:?} s< {:?} )", a, b),
            Val256::FLe(ref a, ref b) => write!(f, "( {:?} <= {:?} )", a, b),
            Val256::FEql(ref a, ref b) => write!(f, "( {:?} == {:?} )", a, b),
            Val256::FNEql(ref a, ref b) => write!(f, "( {:?} != {:?} )", a, b),
            Val256::FImplies(ref a, ref b) => write!(f, "( {:?} -> {:?} )", a, b),
            Val256::FAnd(ref a, ref b) => write!(f, "( {:?} & {:?} )", a, b),
            Val256::FOr(ref a, ref b) => write!(f, "( {:?} | {:?} )", a, b),
            Val256::FXor(ref a, ref b) => write!(f, "( {:?} ^ {:?} )", a, b),
            Val256::FNot(ref a) => write!(f, "!{:?}", a),
            Val256::FByteAt(ref a, ref b) => write!(f, "byte({:?} at:{:?})", a, b),
            Val256::FByteExtract(ref a, ref b) => write!(f, "byte_extract({:?} at:{:?})", a, b),
            Val256::FShl(ref a, ref b) => write!(f, "( {:?} << {:?}", a, b),
            Val256::FAShr(ref a, ref b) => write!(f, "( {:?} >> {:?}", a, b),
            Val256::FLShr(ref a, ref b) => write!(f, "( {:?} a>> {:?}", a, b),
            Val256::FSHA3(mem, ref offset, ref len) => {
                write!(f, "sha3(at:{:?} len:{:?} on {})", offset, len, mem.index())
            }
            Val256::FConst(ref v) | Val256::FConst8(ref v) => write!(f, "{:x}", v),
            Val256::FVarRef(ref name) => write!(f, "{}", name),
            Val256::FMLoad(mem, ref a) => write!(f, "mload({}, at:{:?})", mem.index(), a),
            Val256::FSLoad(mem, ref a) => write!(f, "sload({}, at:{:?})", mem.index(), a),
            Val256::FCombine32(ref vec) => write!(f, "Combine({:?})", vec[0]),
        }
    }
}

pub enum SymbolicTruth {
    True,
    False,
    Maybe,
}

fn try_load_concrete_storage(memory: &SymbolicMemory, mem: MVal, addr: &BVal) -> Option<BVal> {
    if !FVal::is_constant(addr) {
        return None;
    }
    debug_assert!({
        let mem = &memory[mem];
        mem.memory_type == MemoryType::Storage
    });

    lookup_storage_recursive(memory, mem, addr)
}

fn lookup_storage_recursive(memory: &SymbolicMemory, node: MVal, addr: &BVal) -> Option<BVal> {
    let mem = &memory[node];
    debug_assert!({ mem.memory_type == MemoryType::Storage });

    match mem.op {
        MemoryOperation::Init => Some(zero()),
        MemoryOperation::Write256 {
            parent,
            address: ref old_addr,
            value: ref old_val,
        } => {
            if !FVal::is_constant(old_addr) {
                return None;
            }
            match FVal::check_truth(&eql(old_addr, addr)) {
                SymbolicTruth::True => Some(Arc::clone(old_val)),
                SymbolicTruth::False => lookup_storage_recursive(memory, parent, addr),
                _ => unreachable!(),
            }
        }
        MemoryOperation::MemsetUnlimited {
            parent,
            index: ref old_addr,
            value: ref old_val,
        } => {
            if !FVal::is_constant(old_addr) {
                return None;
            }
            match FVal::check_truth(&le(old_addr, addr)) {
                SymbolicTruth::True => Some(Arc::clone(old_val)),
                SymbolicTruth::False => lookup_storage_recursive(memory, parent, addr),
                _ => unreachable!(),
            }
        }
        _ => unreachable!(),
    }
}

fn try_load_concrete(memory: &SymbolicMemory, node: MVal, addr: &BVal) -> Option<BVal> {
    if !FVal::is_constant(addr) {
        return None;
    }
    debug_assert!({
        let mem = &memory[node];
        mem.memory_type == MemoryType::Data || mem.memory_type == MemoryType::Memory
    });

    lookup_mem_recursive(memory, node, addr)
}

// this function exists because solidity does quite often load what it just wrote to memory
// also so we can actually resolve nested keccak computations
// we check the latest memory update if the addresses perfectly align we can simply return the
// writen value since there can be no newer version
fn peak_memory(memory: &SymbolicMemory, node: MVal, addr: &BVal) -> Option<BVal> {
    let mem = &memory[node];

    if let MemoryOperation::Write256 {
        parent: par,
        address: ref old_addr,
        value: ref old_val,
    } = mem.op
    {
        if let SymbolicTruth::True = FVal::check_truth(&eql(addr, old_addr)) {
            return Some(Arc::clone(old_val));
        }
        // if we can prove that nothing got overwritten, proceed to backtrack
        if prove_not_in_range(addr, old_addr, &const_usize(256)) {
            return peak_memory(memory, par, addr);
        }
    }
    None
}

fn lookup_mem_recursive(memory: &SymbolicMemory, node: MVal, addr: &BVal) -> Option<BVal> {
    let mem = &memory[node];
    debug_assert!({ mem.memory_type == MemoryType::Data || mem.memory_type == MemoryType::Memory });

    match mem.op {
        MemoryOperation::Init => {
            if mem.memory_type != MemoryType::Memory {
                return None;
            }
            Some(zero())
        }
        MemoryOperation::Write8 {
            parent: par,
            address: ref old_addr,
            value: ref old_val,
        } => {
            if !(FVal::is_constant(old_addr) && FVal::is_constant(old_val)) {
                return None;
            }
            match FVal::check_truth(&eql(old_addr, addr)) {
                SymbolicTruth::True => Some(Arc::clone(old_val)),
                SymbolicTruth::False => lookup_mem_recursive(memory, par, addr),
                _ => unreachable!(),
            }
        }
        MemoryOperation::Write256 {
            parent: par,
            address: ref old_addr,
            value: ref old_val,
        } => {
            if !(FVal::is_constant(old_addr) && FVal::is_constant(old_val)) {
                return None;
            }

            for i in -31..=0 {
                match FVal::check_truth(&eql(old_addr, &add(addr, &const_i32(i)))) {
                    SymbolicTruth::True => {
                        let offset = (31 + i) as usize;
                        debug_assert!(offset <= 31);

                        return Some(byte_at(old_val, &const_usize(offset)));
                    }
                    SymbolicTruth::False => {}
                    _ => unreachable!(),
                }
            }
            lookup_mem_recursive(memory, par, addr)
        }
        MemoryOperation::MemsetUnlimited {
            parent: par,
            index: ref old_addr,
            value: ref old_val,
        } => {
            if !(FVal::is_constant(old_addr) && FVal::is_constant(old_val)) {
                return None;
            }
            match FVal::check_truth(&le(old_addr, addr)) {
                SymbolicTruth::True => Some(Arc::clone(old_val)),
                SymbolicTruth::False => lookup_mem_recursive(memory, par, addr),
                _ => unreachable!(),
            }
        }

        _ => None,
    }
}

// prove that a is not in range [b,len]
fn prove_not_in_range(a: &BVal, b: &BVal, len: &BVal) -> bool {
    let lower = b;
    let upper = add(b, len);
    match (
        FVal::check_truth(&lt(a, &lower)),
        FVal::check_truth(&lt(&upper, a)),
    ) {
        (SymbolicTruth::True, SymbolicTruth::False)
        | (SymbolicTruth::False, SymbolicTruth::True) => true,
        _ => false,
    }
}

pub fn bval_size(v: &BVal) -> usize {
    match v.val {
        Val256::FMLoad(..) | Val256::FConst8(..) => 8,
        _ => 256,
    }
}

fn mem_op<F>(memory: &SymbolicMemory, mem: MVal, addr: &BVal, len: &BVal, f: F) -> Option<BVal>
where
    F: Fn(Vec<u8>) -> U256,
{
    let mut result = vec![];
    let offset = add(addr, len);
    let mut load_addr = Arc::clone(addr);

    loop {
        if let SymbolicTruth::True = FVal::check_truth(&eql(&offset, &load_addr)) {
            break;
        }

        match lookup_mem_recursive(memory, mem, &load_addr) {
            Some(res) => result.push(res),
            None => return None, // hit symbolic value
        };
        load_addr = add(&load_addr, &const_usize(0x1));
    }

    let mut hash_input = vec![];
    for res in result {
        if let Val256::FConst(u) = FVal::simplified(&res).val {
            hash_input.push(u.byte(0));
        } else {
            panic!("Did not properly detect sym memory read for keccak calculation");
        }
    }

    Some(Arc::new(FVal::new(Val256::FConst(f(hash_input)))))
}

fn new_bval(val: Val256) -> BVal {
    debug_assert!(match val {
        Val256::FMLoad(..) | Val256::FSLoad(..) | Val256::FSHA3(..) | Val256::FCombine32(..) => {
            false
        }
        _ => true,
    });
    let fval = FVal::new(val);
    simpl(&Arc::new(fval))
}

fn new_memory_bval(memory: &SymbolicMemory, val: Val256) -> BVal {
    debug_assert!(match val {
        Val256::FMLoad(..) | Val256::FSLoad(..) | Val256::FSHA3(..) | Val256::FCombine32(..) => {
            true
        }
        _ => false,
    });
    let fval = FVal::new(val);
    simpl_mem(memory, &Arc::new(fval))
}

pub fn add(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FAdd(Arc::clone(a), Arc::clone(b)))
}
pub fn sub(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FSub(Arc::clone(a), Arc::clone(b)))
}
pub fn mul(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FMul(Arc::clone(a), Arc::clone(b)))
}
pub fn div(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FDiv(Arc::clone(a), Arc::clone(b)))
}
pub fn sdiv(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FSDiv(Arc::clone(a), Arc::clone(b)))
}
pub fn umod(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FMod(Arc::clone(a), Arc::clone(b)))
}
pub fn smod(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FSMod(Arc::clone(a), Arc::clone(b)))
}
pub fn exp(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FExp(Arc::clone(a), Arc::clone(b)))
}
pub fn ite(a: &BVal, b: &BVal, c: &BVal) -> BVal {
    new_bval(Val256::FITE(Arc::clone(a), Arc::clone(b), Arc::clone(c)))
}
pub fn lt(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FLt(Arc::clone(a), Arc::clone(b)))
}
pub fn slt(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FSLt(Arc::clone(a), Arc::clone(b)))
}
pub fn le(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FLe(Arc::clone(a), Arc::clone(b)))
}
pub fn and(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FAnd(Arc::clone(a), Arc::clone(b)))
}
pub fn or(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FOr(Arc::clone(a), Arc::clone(b)))
}
pub fn xor(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FXor(Arc::clone(a), Arc::clone(b)))
}
pub fn eql(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FEql(Arc::clone(a), Arc::clone(b)))
}
pub fn neql(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FNEql(Arc::clone(a), Arc::clone(b)))
}
pub fn implies(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FImplies(Arc::clone(a), Arc::clone(b)))
}
pub fn sha3(memory: &SymbolicMemory, mem: MVal, a: &BVal, b: &BVal) -> BVal {
    new_memory_bval(memory, Val256::FSHA3(mem, Arc::clone(a), Arc::clone(b)))
}
pub fn not(a: &BVal) -> BVal {
    new_bval(Val256::FNot(Arc::clone(a)))
}
pub fn mload(memory: &SymbolicMemory, mem: MVal, addr: &BVal) -> BVal {
    let mut loads = Vec::with_capacity(32);
    for i in 0..32 {
        loads.push(mload8(memory, mem, &add(&const_usize(i), addr)));
    }
    new_memory_bval(memory, Val256::FCombine32(loads))
}
pub fn mload8(memory: &SymbolicMemory, mem: MVal, addr: &BVal) -> BVal {
    new_memory_bval(memory, Val256::FMLoad(mem, Arc::clone(addr)))
}
pub fn sload(memory: &SymbolicMemory, mem: MVal, addr: &BVal) -> BVal {
    new_memory_bval(memory, Val256::FSLoad(mem, Arc::clone(addr)))
}
pub fn byte_at(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FByteAt(Arc::clone(a), Arc::clone(b)))
}
pub fn byte_extract(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FByteExtract(Arc::clone(a), Arc::clone(b)))
}
pub fn ashr(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FAShr(Arc::clone(a), Arc::clone(b)))
}
pub fn lshr(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FLShr(Arc::clone(a), Arc::clone(b)))
}
pub fn shl(a: &BVal, b: &BVal) -> BVal {
    new_bval(Val256::FShl(Arc::clone(a), Arc::clone(b)))
}
pub fn const256(a: &str) -> BVal {
    new_bval(Val256::FConst(U256::from_dec_str(a).unwrap()))
}
pub fn const_u256(a: U256) -> BVal {
    new_bval(Val256::FConst(a))
}
#[allow(dead_code)]
pub fn const_8(a: usize) -> BVal {
    assert!(a <= 256);
    new_bval(Val256::FConst8(a.into()))
}
pub fn const_usize(a: usize) -> BVal {
    new_bval(Val256::FConst(a.into()))
}
pub fn const_i32(a: i32) -> BVal {
    if a >= 0 {
        return new_bval(Val256::FConst(a.abs().into()));
    }
    let (val, _) = U256::zero().overflowing_sub(a.abs().into());
    new_bval(Val256::FConst(val))
}
pub fn const_vec(a: &[u8]) -> BVal {
    new_bval(Val256::FConst(a[..].into()))
}
pub fn zero() -> BVal {
    const_usize(0)
}
pub fn one() -> BVal {
    const_usize(1)
}
pub fn max() -> BVal {
    new_bval(Val256::FConst(U256::max_value()))
}
#[cfg(test)]
pub fn var(a: &str) -> BVal {
    new_bval(Val256::FVarRef(a.into()))
}
pub fn fresh_var(a: &str) -> BVal {
    new_bval(Val256::FVarRef(fresh_var_name(a)))
}

fn const_op2<F>(orig: &BVal, a: &BVal, b: &BVal, f: F) -> BVal
where
    F: Fn(U256, U256) -> U256,
{
    if let (Some(av), Some(bv)) = (FVal::as_bigint(a), FVal::as_bigint(b)) {
        return Arc::new(FVal::new(Val256::FConst(f(av, bv))));
    }
    Arc::clone(orig)
}

fn simpl_mem(memory: &SymbolicMemory, val: &BVal) -> BVal {
    if CONFIG.read().unwrap().disable_optimizations {
        return Arc::clone(val);
    }
    match val.val {
        Val256::FSHA3(mem, ref offset, ref len) => {
            /*
             * constant folding
             */
            if FVal::is_constant(offset)
                && FVal::is_constant(len)
                && CONFIG.read().unwrap().concrete_load
                && cfg!(feature = "keccak")
            {
                match mem_op(memory, mem, offset, len, |data| keccak256(&data).into()) {
                    None => {}
                    Some(v) => return v,
                }
            }
            Arc::clone(val)
        }
        Val256::FMLoad(mem, ref addr) => {
            /*
             * Load constants from memory
             */
            if CONFIG.read().unwrap().concrete_load {
                match try_load_concrete(memory, mem, addr) {
                    None => {} // could not load concrete, proceed normally
                    Some(v) => {
                        // actually store simplified constant result as simpl value
                        if let Some(val) = FVal::as_const8(&v) {
                            return val;
                        }
                        return v;
                    }
                }
            }
            Arc::clone(val)
        }
        Val256::FSLoad(stor, ref addr) => {
            if CONFIG.read().unwrap().concrete_load {
                if let Some(peak) = peak_memory(memory, stor, addr) {
                    return peak;
                }

                match try_load_concrete_storage(memory, stor, addr) {
                    None => {}
                    Some(v) => return v,
                }
            }
            Arc::clone(val)
        }
        Val256::FCombine32(ref vec) => {
            assert!(vec.len() == 32);
            if !CONFIG.read().unwrap().concrete_load {
                return Arc::clone(val);
            }
            // since we only use it to concat mload atm try to load the entire variable
            if let Val256::FMLoad(mem, addr) = vec[0].val() {
                if let Some(peak) = peak_memory(memory, *mem, addr) {
                    return peak;
                }
            }
            let mut res = const_usize(0);
            for cur_byte in vec {
                match cur_byte.val {
                    Val256::FConst8(ref v) | Val256::FConst(ref v) => {
                        assert!(v.bits() <= 8);
                        res = or(
                            &mul(&res, &const_usize(256)),
                            &and(&cur_byte, &const_usize(255)),
                        );
                    }
                    _ => return Arc::clone(val),
                }
            }
            res
        }
        _ => unreachable!(),
    }
}

fn simpl(val: &BVal) -> BVal {
    if CONFIG.read().unwrap().disable_optimizations {
        return Arc::clone(val);
    }
    match val.val {
        Val256::FAdd(ref a, ref b) => {
            /*
             * arithmetic rewriting
             */
            if CONFIG.read().unwrap().arithmetic_simplification {
                // 0 + x => x
                if let Some(d) = FVal::as_bigint(&a) {
                    if d.is_zero() {
                        return Arc::clone(b);
                    }
                }
                // x + 0 => x
                if let Some(d) = FVal::as_bigint(&b) {
                    if d.is_zero() {
                        return Arc::clone(a);
                    }
                }
            }

            /*
             * constant folding
             */
            const_op2(val, &a, &b, |av, bv| av.overflowing_add(bv).0)
        }
        Val256::FSub(ref a, ref b) => {
            /*
             * arithmetic rewriting
             */
            if CONFIG.read().unwrap().arithmetic_simplification {
                // 0 - x => x
                if let Some(d) = FVal::as_bigint(&a) {
                    if d.is_zero() {
                        return Arc::clone(b);
                    }
                }
                // x - 0 => x
                if let Some(d) = FVal::as_bigint(&b) {
                    if d.is_zero() {
                        return Arc::clone(a);
                    }
                }
                /*
                 * (a + b) - b  ==> a
                 * (b + a) - b  ==> a
                 */
                match (&a.val, &b.val) {
                    (Val256::FAdd(ref l, ref r), Val256::FVarRef(_)) => {
                        if l == b {
                            return Arc::clone(r);
                        }
                        if r == b {
                            return Arc::clone(l);
                        }
                    }
                    (Val256::FVarRef(_), Val256::FAdd(ref l, ref r)) => {
                        if l == b {
                            return Arc::clone(r);
                        }
                        if r == b {
                            return Arc::clone(l);
                        }
                    }
                    _ => {}
                }
            }
            /*
             * constant folding
             */
            const_op2(val, &a, &b, |av, bv| av.overflowing_sub(bv).0)
        }
        Val256::FMul(ref a, ref b) => {
            if CONFIG.read().unwrap().arithmetic_simplification {
                match (&a.val, &b.val) {
                    (_, Val256::FConst(ref c)) | (_, Val256::FConst8(ref c)) => {
                        // a * 0 => 0
                        if c.is_zero() {
                            return zero();
                        }
                        // a * 1 => a
                        if *c == U256::one() {
                            return Arc::clone(a);
                        }
                    }
                    (Val256::FConst(ref c), _) | (Val256::FConst8(ref c), _) => {
                        // 0 * b => 0
                        if c.is_zero() {
                            return zero();
                        }
                        // 1 * b => b
                        if *c == U256::one() {
                            return Arc::clone(b);
                        }
                    }
                    _ => {}
                }
            }

            /*
             * constant folding
             */
            const_op2(val, &a, &b, |av, bv| av.overflowing_mul(bv).0)
        }
        Val256::FDiv(ref a, ref b) => {
            /*
             * constant folding
             */
            const_op2(val, &a, &b, |av, bv| {
                if bv.is_zero() {
                    U256::zero()
                } else {
                    av / bv
                }
            })
        }
        Val256::FExp(ref a, ref b) => {
            /*
             * constant folding
             */
            const_op2(val, &a, &b, |av, bv| {
                let (v, _) = av.overflowing_pow(bv);
                v
            })
        }
        Val256::FSDiv(..) => Arc::clone(val),
        Val256::FMod(ref a, ref b) => {
            /*
             * constant folding
             */
            const_op2(val, &a, &b, |av, bv| {
                if bv.is_zero() {
                    U256::zero()
                } else {
                    av % bv
                }
            })
        }
        Val256::FSMod(..) => Arc::clone(val),
        Val256::FITE(ref cond, ref thenv, ref elsev) => {
            /*
             * constant folding
             */
            if let Some(c) = FVal::as_bigint(&cond) {
                if c.is_zero() {
                    return Arc::clone(elsev);
                } else {
                    return Arc::clone(thenv);
                }
            }
            Arc::clone(val)
        }
        Val256::FLt(ref a, ref b) => {
            /*
             * constant folding
             */
            const_op2(&val, &a, &b, |av, bv| {
                if av < bv {
                    U256::one()
                } else {
                    U256::zero()
                }
            })
        }
        Val256::FLe(ref a, ref b) => {
            /*
             * constant folding
             */
            const_op2(&val, &a, &b, |av, bv| {
                if av <= bv {
                    U256::one()
                } else {
                    U256::zero()
                }
            })
        }
        Val256::FSLt(..) => Arc::clone(val),
        Val256::FEql(ref a, ref b) => {
            /*
             * special keccak handling
             */
            match (a.val(), b.val()) {
                // if we compare keccak to a constant value, we know we cannot compute it or we
                // would assume a collision
                (Val256::FConst(..), Val256::FSHA3(..))
                | (Val256::FSHA3(..), Val256::FConst(..))
                    if cfg!(feature = "keccak") =>
                {
                    return zero();
                }
                _ => {}
            }

            /*
             * constant folding
             */
            const_op2(&val, &a, &b, |av, bv| {
                if av == bv {
                    U256::one()
                } else {
                    U256::zero()
                }
            })
        }
        Val256::FNEql(ref a, ref b) => {
            /*
             * constant folding
             */
            const_op2(&val, &a, &b, |av, bv| {
                if av != bv {
                    U256::one()
                } else {
                    U256::zero()
                }
            })
        }
        Val256::FImplies(ref a, ref b) => {
            /*
             * constant folding
             */
            if let (Some(av), Some(bv)) = (FVal::as_bigint(a), FVal::as_bigint(b)) {
                if !(av == U256::one() || av == U256::zero()) {
                    return Arc::clone(val);
                }
                if !(bv == U256::one() || bv == U256::zero()) {
                    return Arc::clone(val);
                }
                return match (av.is_zero(), bv.is_zero()) {
                    // F, F
                    (true, true) => one(),
                    // T, T
                    (false, false) => one(),
                    // F, T
                    (true, false) => one(),
                    // T, F
                    (false, true) => zero(),
                };
            }
            Arc::clone(val)
        }
        Val256::FAnd(ref a, ref b) => {
            if CONFIG.read().unwrap().arithmetic_simplification {
                match (&a.val, &b.val) {
                    (_, Val256::FConst(ref c)) | (_, Val256::FConst8(ref c)) => {
                        // a & 0 => a
                        if c.is_zero() {
                            return zero();
                        }
                        // a & ffffff => ffffff
                        if *c == U256::max_value() {
                            return Arc::clone(b);
                        }
                    }
                    (Val256::FConst(ref c), _) | (Val256::FConst8(ref c), _) => {
                        // 0 & b => 0
                        if c.is_zero() {
                            return zero();
                        }
                        // ffffff & b => b
                        if *c == U256::max_value() {
                            return Arc::clone(b);
                        }
                    }
                    _ => {}
                }
            }
            /*
             * constant folding
             */
            const_op2(&val, &a, &b, |av, bv| av.bitand(bv))
        }
        Val256::FOr(ref a, ref b) => {
            if CONFIG.read().unwrap().arithmetic_simplification {
                match (&a.val, &b.val) {
                    (_, Val256::FConst(ref c)) | (_, Val256::FConst8(ref c)) => {
                        // a | 0 => a
                        if c.is_zero() {
                            return Arc::clone(a);
                        }
                        // a | ffffff => ffffff
                        if *c == U256::max_value() {
                            return max();
                        }
                    }
                    (Val256::FConst(ref c), _) | (Val256::FConst8(ref c), _) => {
                        // 0 | b => b
                        if c.is_zero() {
                            return Arc::clone(b);
                        }
                        // ffffff | b => ffffff
                        if *c == U256::max_value() {
                            return max();
                        }
                    }
                    _ => {}
                }
            }
            /*
             * constant folding
             */
            const_op2(&val, &a, &b, |av, bv| av.bitor(bv))
        }
        Val256::FXor(ref a, ref b) => {
            /*
             * constant folding
             */
            const_op2(&val, &a, &b, |av, bv| av.bitxor(bv))
        }
        Val256::FNot(ref a) => {
            if CONFIG.read().unwrap().arithmetic_simplification {
                if let Val256::FNot(ref v) = &a.val {
                    // -(-(a)) = a
                    return Arc::clone(v);
                }
            }
            /*
             * constant folding
             */
            if let Some(av) = FVal::as_bigint(&a) {
                Arc::new(FVal::new(Val256::FConst(!av)))
            } else {
                Arc::clone(val)
            }
        }
        Val256::FByteAt(ref a, ref b) => {
            /*
             * constant folding
             */
            const_op2(&val, &a, &b, |av, _| {
                if let Some(bv) = FVal::as_usize(&b) {
                    return av.byte(bv).into();
                }
                U256::zero()
            })
        }
        Val256::FByteExtract(ref a, ref b) => {
            /*
             * constant folding
             */
            FVal::as_const8(&const_op2(&val, &a, &b, |av, _| {
                if let Some(bv) = FVal::as_usize(&b) {
                    return av.byte(bv).into();
                }
                U256::zero()
            }))
            .unwrap()
        }
        Val256::FAShr(ref a, ref b) => {
            /*
             * constant folding
             */
            if let (Some(av), Some(bv)) = (FVal::as_bigint(a), FVal::as_bigint(b)) {
                const CONST_256: U256 = U256([256, 0, 0, 0]);
                const CONST_HIBIT: U256 = U256([0, 0, 0, 0x8000_0000_0000_0000]);
                let sign = av & CONST_HIBIT != U256::zero();

                return const_u256(if bv >= CONST_256 {
                    if sign {
                        U256::max_value()
                    } else {
                        U256::zero()
                    }
                } else {
                    let shift = bv.as_u32() as usize;
                    let mut shifted = av >> shift;
                    if sign {
                        shifted = shifted | (U256::max_value() << (256 - shift));
                    }
                    shifted
                });
            }
            Arc::clone(val)
        }
        Val256::FLShr(ref a, ref b) => {
            /*
             * constant folding
             */
            if let (Some(av), Some(bv)) = (FVal::as_bigint(a), FVal::as_bigint(b)) {
                const CONST_256: U256 = U256([256, 0, 0, 0]);

                return const_u256(if bv >= CONST_256 {
                    U256::zero()
                } else {
                    av >> (bv.as_u32() as usize)
                });
            }
            Arc::clone(val)
        }
        Val256::FShl(ref a, ref b) => {
            /*
             * constant folding
             */
            if let (Some(av), Some(bv)) = (FVal::as_bigint(a), FVal::as_bigint(b)) {
                const CONST_256: U256 = U256([256, 0, 0, 0]);

                return const_u256(if bv >= CONST_256 {
                    U256::zero()
                } else {
                    av << (bv.as_u32() as usize)
                });
            }
            Arc::clone(val)
        }
        Val256::FConst8(_) | Val256::FConst(_) | Val256::FVarRef(_) => Arc::clone(val),
        _ => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;

    use tiny_keccak;

    use crate::CONFIG;

    use crate::bytecode::Instr;
    use crate::se::expr::symbolic_memory::*;
    use crate::test_helpers::generate_test_graph;

    #[test]
    fn combine32_mem_test() {
        CONFIG.write().unwrap().concrete_load = true;
        let g = generate_test_graph(vec![]);
        let mut state = g.get_state_by_id(1).clone();

        let mut mem = state.mem;
        {
            let memory = Arc::make_mut(&mut state.memory);
            mem = word_write(memory, mem, &const_usize(0), &const_usize(0xAABBCCDD));
        }
        let load = mload(&state.memory, mem, &const_usize(0x0));
        assert_eq!(const_usize(0xAABBCCDD), FVal::simplified(&load));
        CONFIG.write().unwrap().concrete_load = false;
    }

    #[test]
    fn constant_memload_test() {
        CONFIG.write().unwrap().concrete_load = true;
        let g = generate_test_graph(vec![]);
        let mut state = g.get_state_by_id(1).clone();

        let mut mem = state.mem;
        for i in 0..32 {
            assert_eq!(
                FVal::as_usize(&const_usize(0)).unwrap(),
                FVal::as_usize(&mload8(
                    &state.memory,
                    mem,
                    &add(&const_usize(0x100), &const_usize(i))
                ))
                .unwrap()
            );
        }

        {
            let memory = Arc::make_mut(&mut state.memory);
            mem = byte_write(memory, mem, &const_usize(0x100), &const_usize(0xAA));
        }
        assert_eq!(
            const_8(0xAA),
            FVal::simplified(&mload8(&state.memory, mem, &const_usize(0x100)))
        );
        assert_eq!(
            const_usize(0xAA),
            FVal::simplified(&mload(&state.memory, mem, &const_usize(0xE1)))
        );
        assert_eq!(
            const_usize(0xAA00),
            FVal::simplified(&mload(&state.memory, mem, &const_usize(0xE2)))
        );

        {
            let memory = Arc::make_mut(&mut state.memory);
            mem = word_write(memory, mem, &const_usize(0x100), &const_usize(0xAA));
        }
        assert_eq!(
            const_8(0xAA),
            FVal::simplified(&mload8(&state.memory, mem, &const_usize(0x11F)))
        );
        assert_eq!(
            const_usize(0xAA),
            FVal::simplified(&mload(&state.memory, mem, &const_usize(0x100)))
        );
        assert_eq!(
            const_usize(0xAA00),
            FVal::simplified(&mload(&state.memory, mem, &const_usize(0x101)))
        );

        {
            let memory = Arc::make_mut(&mut state.memory);
            mem = word_write(memory, mem, &const_usize(0xFF), &const_usize(0xBB));
        }
        assert_eq!(
            const_8(0xBB),
            FVal::simplified(&mload8(&state.memory, mem, &const_usize(0x11E)))
        );
        assert_eq!(
            const_usize(0xBBAA),
            FVal::simplified(&mload(&state.memory, mem, &const_usize(0x100)))
        );
        assert_eq!(
            const_usize(0xBBAA00),
            FVal::simplified(&mload(&state.memory, mem, &const_usize(0x101)))
        );

        {
            let memory = Arc::make_mut(&mut state.memory);
            mem = word_write(
                memory,
                mem,
                &const_usize(0x80),
                &const_vec(&vec![
                    0x78, 0xcd, 0x8c, 0x33, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
                    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
                    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
                ]),
            );
            mem = word_write(
                memory,
                mem,
                &const_usize(0x84),
                &const_vec(&vec![
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                ]),
            );
        }

        assert_eq!(
            const_usize(0x78cd8c330000),
            FVal::simplified(&mload(&state.memory, mem, &const_usize(0x66)))
        );

        {
            let memory = Arc::make_mut(&mut state.memory);
            mem = word_write(
                memory,
                mem,
                &const_usize(0x80),
                &const_vec(&vec![
                    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
                    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
                    0xaa, 0xaa, 0x78, 0xcd, 0x8c, 0x33,
                ]),
            );
            mem = word_write(
                memory,
                mem,
                &const_usize(0x7C),
                &const_vec(&vec![
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                ]),
            );
        }

        assert_eq!(
            const_usize(0x78cd8c33),
            FVal::simplified(&mload(&state.memory, mem, &const_usize(0x80)))
        );
        CONFIG.write().unwrap().concrete_load = false;
    }

    // This test soley exist because in an earlier version we were not properly forwarding
    // simplify calls, resulting in crashing the system due to a stack overflow
    #[test]
    fn simpl_big_chains() {
        let mut res = const_usize(0);
        for i in 0..32 {
            let cur_byte = byte_at(&const_usize(0xfa11fa22), &const_usize(i));
            res = or(
                &mul(&res, &const_usize(256)),
                &and(&cur_byte, &const_usize(255)),
            );
        }
        simpl(&res);
    }

    #[test]
    fn simpl_rewrite() {
        CONFIG.write().unwrap().arithmetic_simplification = true;
        let tests = vec![
            // forward 0
            (var("x"), add(&var("x"), &const_usize(0))),
            (var("x"), add(&const_usize(0), &var("x"))),
            (var("x"), sub(&var("x"), &const_usize(0))),
            (var("x"), sub(&const_usize(0), &var("x"))),
            // a * 0 = 0
            (const_usize(0), mul(&var("x"), &const_usize(0))),
            (const_usize(0), mul(&const_usize(0), &var("x"))),
            // a * 1 = a
            (var("x"), mul(&var("x"), &const_usize(1))),
            (var("x"), mul(&const_usize(1), &var("x"))),
            // rewrite sub
            (var("a"), sub(&add(&var("a"), &var("b")), &var("b"))),
            (
                sub(&add(&var("a"), &var("b")), &var("c")),
                sub(&add(&var("a"), &var("b")), &var("c")),
            ),
            (
                sub(&add(&var("a"), &var("b")), &var("c")),
                sub(&add(&var("a"), &var("b")), &var("c")),
            ),
            (sub(&add(&var("a"), &var("b")), &var("b")), var("a")),
        ];

        for (i, (corr, test)) in tests.iter().enumerate() {
            println!("{:2} Testing: {:?} : {:?}", i + 1, corr, test);
            assert_eq!(*corr, FVal::simplified(&test));
        }
        CONFIG.write().unwrap().arithmetic_simplification = false;
    }

    // since we edit simpl heavily we test most cases specificly so we do not break
    // anything in later iterations, thus these tests might seem kinda redundant / unnecessary
    #[test]
    fn simpl_constant_folding_test() {
        let g = generate_test_graph(vec![]);
        let s = &g.get_state_by_id(1);

        let tests = vec![
            // ============ forwarding ===========
            // add
            (
                add(&var("x"), &const_usize(6)),
                add(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // sub
            (
                sub(&var("x"), &const_usize(6)),
                sub(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // mul
            (
                mul(&var("x"), &const_usize(6)),
                mul(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // div
            (
                div(&var("x"), &const_usize(6)),
                div(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // sdiv
            (
                sdiv(&var("x"), &const_usize(6)),
                sdiv(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // mod
            (
                umod(&var("x"), &const_usize(6)),
                umod(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // smod
            (
                smod(&var("x"), &const_usize(6)),
                smod(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // exp
            (
                exp(&var("x"), &const_usize(6)),
                exp(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // ite
            (
                ite(&var("x"), &const_usize(6), &const_usize(6)),
                ite(
                    &var("x"),
                    &add(&const_usize(3), &const_usize(3)),
                    &add(&const_usize(3), &const_usize(3)),
                ),
            ),
            // lt
            (
                lt(&var("x"), &const_usize(6)),
                lt(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // slt
            (
                slt(&var("x"), &const_usize(6)),
                slt(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // le
            (
                le(&var("x"), &const_usize(6)),
                le(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // eql
            (
                eql(&var("x"), &const_usize(6)),
                eql(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // neql
            (
                neql(&var("x"), &const_usize(6)),
                neql(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // and
            (
                and(&var("x"), &const_usize(6)),
                and(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // or
            (
                or(&var("x"), &const_usize(6)),
                or(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // xor
            (
                xor(&var("x"), &const_usize(6)),
                xor(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // not
            (
                not(&add(&var("x"), &const_usize(6))),
                not(&add(&var("x"), &add(&const_usize(3), &const_usize(3)))),
            ),
            // byte_at
            (
                byte_at(&var("x"), &const_usize(6)),
                byte_at(&var("x"), &add(&const_usize(3), &const_usize(3))),
            ),
            // sload
            (
                sload(&s.memory, s.account().storage, &const_usize(6)),
                sload(
                    &s.memory,
                    s.account().storage,
                    &add(&const_usize(3), &const_usize(3)),
                ),
            ),
            // ========== forwarding end =========
            // add
            (const_usize(10), add(&const_usize(5), &const_usize(5))),
            // sub
            (const_usize(5), sub(&const_usize(10), &const_usize(5))),
            // mul
            (const_usize(15), mul(&const_usize(3), &const_usize(5))),
            // div
            (const_usize(3), div(&const_usize(9), &const_usize(3))),
            // div - div by 0
            (const_usize(0), div(&const_usize(3), &const_usize(0))),
            // exp
            (const_usize(9), exp(&const_usize(3), &const_usize(2))),
            // mod
            (const_usize(3), umod(&const_usize(15), &const_usize(4))),
            // mod
            (const_usize(0), umod(&const_usize(15), &const_usize(0))),
            // ite
            (
                const_usize(1),
                ite(&one(), &const_usize(1), &const_usize(2)),
            ),
            // ite
            (
                const_usize(2),
                ite(&zero(), &const_usize(1), &const_usize(2)),
            ),
            // lt
            (const_usize(1), lt(&const_usize(3), &const_usize(4))),
            // lt
            (const_usize(0), lt(&const_usize(4), &const_usize(4))),
            // le
            (const_usize(1), le(&const_usize(4), &const_usize(4))),
            // le
            (const_usize(0), le(&const_usize(5), &const_usize(4))),
            // eql
            (const_usize(1), eql(&const_usize(3), &const_usize(3))),
            // eql
            (const_usize(0), eql(&const_usize(4), &const_usize(3))),
            // neql
            (const_usize(1), neql(&const_usize(4), &const_usize(3))),
            // neql
            (const_usize(0), neql(&const_usize(4), &const_usize(4))),
            // and
            (const_usize(1), and(&const_usize(1), &const_usize(1))),
            // and
            (const_usize(0), and(&const_usize(0), &const_usize(1))),
            // or
            (const_usize(1), or(&const_usize(0), &const_usize(1))),
            // xor
            (const_usize(1), xor(&const_usize(0), &const_usize(1))),
            // byte_at
            (
                const_usize(0xAA),
                byte_at(&const_usize(0xFFFFFFFFFFFFAA), &const_usize(0)),
            ),
        ];

        for (i, (corr, test)) in tests.iter().enumerate() {
            println!("{} Testing: {:?} : {:?}", i, corr, test);
            assert_eq!(*corr, FVal::simplified(&test));
        }
    }

    #[test]
    fn keccak() {
        let v = tiny_keccak::keccak256("testing".as_bytes());
        let hash = [
            95, 22, 244, 199, 241, 73, 172, 79, 149, 16, 217, 207, 140, 243, 132, 3, 138, 211, 72,
            179, 188, 220, 1, 145, 95, 149, 222, 18, 223, 157, 27, 2,
        ];
        assert_eq!(v, hash);
    }

    #[test]
    fn keccak_with_constant_load() {
        let ins = vec![
            // taken from simple toy contract
            // stack and memory when jumped to hashing part:
            Instr::IPush(vec![0x0e, 0x38, 0x68, 0x16]),
            Instr::IPush(vec![0x76]),
            Instr::IPush(vec![0xaa, 0xbb]),
            Instr::IPush(vec![0xcc, 0xdd]),
            Instr::IPush(vec![0x80]),
            Instr::IPush(vec![0x40]),
            Instr::IMStore,
            // taken from contract trace
            Instr::IPush(vec![0x00]),
            Instr::IDup(3),
            Instr::IDup(3),
            Instr::IPush(vec![0x40]),
            Instr::IMLoad,
            Instr::IDup(1),
            Instr::IDup(4),
            Instr::IDup(2),
            Instr::IMStore,
            Instr::IPush(vec![0x20]),
            Instr::IAdd,
            Instr::IDup(3),
            Instr::IDup(2),
            Instr::IMStore,
            Instr::IPush(vec![0x20]),
            Instr::IAdd,
            Instr::ISwap(3),
            Instr::IPop,
            Instr::IPop,
            Instr::IPop,
            Instr::IPush(vec![0x40]),
            Instr::IMLoad,
            Instr::IDup(1),
            Instr::ISwap(2),
            Instr::ISub,
            Instr::ISwap(1),
            Instr::ISHA3,
        ];

        CONFIG.write().unwrap().concrete_load = true;
        let g = generate_test_graph(ins);
        let correct_hash = const256(
            "86542036592187563642472694756521917565721712402534782107550407302586609544071",
        );
        let state = &g.get_state_by_id(35);
        assert_eq!(correct_hash, FVal::simplified(&state.stack[5]));
        CONFIG.write().unwrap().concrete_load = false;
    }

    #[test]
    fn memory_access() {
        let ins = vec![
            Instr::IPush(vec![0xaa, 0xaa, 0xbb, 0xbb]), //value
            Instr::IPush(vec![0x80]),                   //addr
            Instr::IMStore,
            Instr::IPush(vec![0x80]), //addr
            Instr::IMLoad,
            Instr::IPop,
            Instr::IPush(vec![0xcc, 0xcc, 0xdd, 0xdd]), //value
            Instr::IPush(vec![0x7E]),                   //addr
            Instr::IMStore,
            Instr::IPush(vec![0x7E]), //addr
            Instr::IMLoad,
            Instr::IPop,
            Instr::IPush(vec![0x80]), //addr
            Instr::IMLoad,
        ];

        CONFIG.write().unwrap().concrete_load = true;
        let g = generate_test_graph(ins);

        let state = &g.get_state_by_id(6);
        assert_eq!(FVal::as_usize(&state.stack[0]).unwrap(), 0xaaaabbbb);
        let state = &g.get_state_by_id(12);
        assert_eq!(FVal::as_usize(&state.stack[0]).unwrap(), 0xccccdddd);
        let state = &g.get_state_by_id(15);
        assert_eq!(FVal::as_usize(&state.stack[0]).unwrap(), 0xccccddddbbbb);
        CONFIG.write().unwrap().concrete_load = false;
    }

    #[test]
    fn memory_store_in_range() {
        let ins = vec![
            Instr::IPush(vec![
                0x78, 0xcd, 0x8c, 0x33, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
                0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
                0xaa, 0xaa, 0xaa, 0xaa,
            ]), //value
            Instr::IPush(vec![0x80]), //addr
            Instr::IMStore,
            Instr::IPush(vec![
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00,
            ]), //value
            Instr::IPush(vec![0x84]), //addr
            Instr::IMStore,
            Instr::IPush(vec![0x66]), //addr
            Instr::IMLoad,
            Instr::IPush(vec![
                0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
                0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
                0x78, 0xcd, 0x8c, 0x33,
            ]), //value
            Instr::IPush(vec![0x80]), //addr
            Instr::IMStore,
            Instr::IPush(vec![
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00,
            ]), //value
            Instr::IPush(vec![0x7C]), //addr
            Instr::IMStore,
            Instr::IPop,
            Instr::IPush(vec![0x80]), //addr
            Instr::IMLoad,
        ];
        CONFIG.write().unwrap().concrete_load = true;
        let g = generate_test_graph(ins);

        let state = &g.get_state_by_id(9);
        assert_eq!(FVal::as_usize(&state.stack[0]).unwrap(), 0x78cd8c330000);

        let state = &g.get_state_by_id(18);
        assert_eq!(FVal::as_usize(&state.stack[0]).unwrap(), 0x78cd8c33);
        CONFIG.write().unwrap().concrete_load = false;
    }

    #[test]
    fn memory_update() {
        let ins = vec![
            Instr::IPush(vec![0xfa, 0x11, 0xfa, 0x22]), //value
            Instr::IPush(vec![0xad, 0xd1]),             //addr
            Instr::IMStore,
            Instr::IPush(vec![0xaa, 0xaa, 0xaa, 0xaa]), //value
            Instr::IPush(vec![0xad, 0xd1]),             //addr
            Instr::IMStore,
            Instr::IPush(vec![0xad, 0xd1]), //addr
            Instr::IMLoad,
        ];
        CONFIG.write().unwrap().concrete_load = true;
        let g = generate_test_graph(ins);

        let state = &g.get_state_by_id(9);
        assert_eq!(FVal::as_usize(&state.stack[0]).unwrap(), 0xaaaaaaaa);
        CONFIG.write().unwrap().concrete_load = false;
    }

    #[test]
    fn memory_update8() {
        let ins = vec![
            Instr::IPush(vec![0xfa, 0x11, 0xfa, 0x22]), //value
            Instr::IPush(vec![0xad, 0xd1]),             //addr
            Instr::IMStore,
            Instr::IPush(vec![0xbb]),       //value
            Instr::IPush(vec![0xad, 0xef]), //addr
            Instr::IMStore8,
            Instr::IPush(vec![0xad, 0xd1]), //addr
            Instr::IMLoad,
        ];
        CONFIG.write().unwrap().concrete_load = true;
        let g = generate_test_graph(ins);

        let state = &g.get_state_by_id(9);
        assert_eq!(FVal::as_usize(&state.stack[0]).unwrap(), 0xfa11bb22);
        CONFIG.write().unwrap().concrete_load = false;
    }

    #[test]
    fn memory_access_symbolic() {
        let ins = vec![
            Instr::IPush(vec![0xfa, 0x11, 0xfa, 0x22]), // value for store
            Instr::ICaller,                             // create sym value
            Instr::IMStore,
            Instr::IPush(vec![0xad, 0xd1]), //addr
            Instr::IMLoad,
        ];
        CONFIG.write().unwrap().concrete_load = true;
        let g = generate_test_graph(ins);

        let state = &g.get_state_by_id(6);
        assert_eq!(
            state.stack[0],
            mload(&state.memory, state.mem, &const_usize(0xadd1))
        );
        CONFIG.write().unwrap().concrete_load = false;
    }

    #[test]
    fn storage_constant_load_test() {
        let ins = vec![
            Instr::IPush(vec![0xfa, 0x11, 0xfa, 0x22]), //value
            Instr::IPush(vec![0xad, 0xd1]),             //addr
            Instr::ISStore,
            Instr::IPush(vec![0xaa, 0xaa, 0xaa, 0xaa]), //value
            Instr::IPush(vec![0xad, 0xd1]),             //addr
            Instr::ISStore,
            Instr::IPush(vec![0xad, 0xd1]), //addr
            Instr::ISLoad,
        ];
        CONFIG.write().unwrap().concrete_load = true;
        let g = generate_test_graph(ins);

        let state = &g.get_state_by_id(9);
        assert_eq!(FVal::as_usize(&state.stack[0]).unwrap(), 0xaaaaaaaa);
        CONFIG.write().unwrap().concrete_load = false;
    }

    #[test]
    fn bval_hash() {
        let mut hasher_1 = DefaultHasher::new();
        let mut hasher_2 = DefaultHasher::new();

        let g = generate_test_graph(vec![]);
        let state = &g.get_state_by_id(1);

        let load = mload(&state.memory, state.mem, &const_usize(0x0));

        load.hash(&mut hasher_1);
        load.hash(&mut hasher_2);
        assert_eq!(hasher_1.finish(), hasher_2.finish());
    }

    use rand::{thread_rng, Rng};
    use std::u32;

    #[test]
    fn prove_not_in_range_test() {
        let mut rng = thread_rng();

        for _ in 0..1000 {
            let a: u32 = rng.gen::<u32>() % ((u32::MAX / 2) + 1);
            let b: u32 = rng.gen::<u32>() % ((u32::MAX / 2) + 1);
            let len: u32 = rng.gen::<u32>() % ((u32::MAX / 2) + 1);

            let correct = a < b || a > (b + len);
            let a = const_usize(a as usize);
            let b = const_usize(b as usize);
            let len = const_usize(len as usize);
            assert_eq!(prove_not_in_range(&a, &b, &len), correct);
        }
    }

    // =========================================
    // Benchmarks
    // =========================================
    use test::{black_box, Bencher};

    #[bench]
    fn bval_partial_eq_bench(b: &mut Bencher) {
        let g = generate_test_graph(vec![]);
        let state = &g.get_state_by_id(1);

        let mut load = mload(&state.memory, state.mem, &const_usize(0x0));
        let mut load_2 = mload(&state.memory, state.mem, &const_usize(0x1));

        for _ in 0..100 {
            load = mload(&state.memory, state.mem, &load);
            load_2 = mload(&state.memory, state.mem, &load_2);
        }

        b.iter(|| {
            black_box(load.eq(&load_2));
        });
    }

    #[bench]
    fn bval_hash_bench(b: &mut Bencher) {
        let g = generate_test_graph(vec![]);
        let state = &g.get_state_by_id(1);
        let mut load = mload(&state.memory, state.mem, &const_usize(0x0));

        for _ in 0..100 {
            load = mload(&state.memory, state.mem, &load);
        }

        b.iter(|| {
            let mut hasher = DefaultHasher::new();
            black_box(load.hash(&mut hasher));
            hasher.finish();
        });
    }
}
