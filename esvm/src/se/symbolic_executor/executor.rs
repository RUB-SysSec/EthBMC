use crate::bytecode::Instr;
use crate::se::{
    expr::bval::*,
    symbolic_edge::*,
    symbolic_executor::{call_ops::*, memory_ops::*, stack_ops::*},
    symbolic_state::{Flags, SeState},
};

fn fail_unknown(i: &Instr) -> Vec<(SeState, EdgeType)> {
    warn!("encountered unknown instruction {:?}, droping path", i);
    vec![]
}

pub fn expensive_computation(s: &SeState) -> bool {
    let ins = s.get_instruction();
    if ins.is_none() {
        return true;
    }
    match ins.unwrap() {
        Instr::IExtCodeSize
        | Instr::IBalance
        | Instr::ISelfDestruct
        | Instr::ICall
        | Instr::IStaticCall
        | Instr::ICallCode
        | Instr::IDelegateCall => true,
        _ => false,
    }
}

pub fn symbolic_step(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let ins = s.get_instruction();
    if ins.is_none() {
        error!("Could not fetch next instruction: {:?}", s);
        return vec![];
    }
    let ins = ins.unwrap();
    match ins {
        Instr::IAdd => arith2(s, |a, b| add(a, b)),
        Instr::ISub => arith2(s, |a, b| sub(a, b)),
        Instr::IMul => arith2(s, |a, b| mul(a, b)),
        Instr::IDiv => arith2(s, |a, b| div(a, b)),
        Instr::ISDiv => arith2(s, |a, b| sdiv(a, b)),
        Instr::IMod => arith2(s, |a, b| umod(a, b)),
        Instr::ISMod => arith2(s, |a, b| smod(a, b)),
        Instr::IAddMod => arith3(s, |a, b, c| umod(&add(a, b), c)),
        Instr::IMulMod => arith3(s, |a, b, c| umod(&mul(a, b), c)),
        Instr::IExp => exponentiation(s),
        Instr::ILt => arith2(s, |a, b| lt(a, b)),
        Instr::IGt => arith2(s, |a, b| lt(b, a)),
        Instr::ISLt => arith2(s, |a, b| slt(a, b)),
        Instr::ISGt => arith2(s, |a, b| slt(b, a)),
        Instr::IEql => arith2(s, |a, b| eql(a, b)),
        Instr::IIsZero => arith1(s, |a| eql(a, &zero())),
        Instr::IAnd => arith2(s, |a, b| and(a, b)),
        Instr::IOr => arith2(s, |a, b| or(a, b)),
        Instr::IXor => arith2(s, |a, b| xor(a, b)),
        Instr::INot => arith1(s, |a| not(a)),
        Instr::IByte => arith2(s, |offset, val| {
            ite(&lt(offset, &const256("32")), &byte_at(val, offset), &zero())
        }),
        Instr::IShl => arith2(s, |shift, value| shl(value, shift)),
        Instr::IAShr => arith2(s, |shift, value| ashr(value, shift)),
        Instr::ILShr => arith2(s, |shift, value| lshr(value, shift)),
        Instr::ISHA3 => keccak(s),
        Instr::IAddr => arith0(s, Some(&s.account().addr)),
        Instr::IBalance => balance(s),
        Instr::IOrigin => arith0(s, Some(&s.input_tx().origin)),
        Instr::ICaller => arith0(s, Some(&s.input_tx().caller)),
        Instr::ICallValue => arith0(s, Some(&s.input_tx().callvalue)),
        Instr::ICallDataLoad => calldataload(s),
        Instr::ICallDataSize => arith0(s, Some(&s.input_tx().calldata_size)),
        Instr::ICallDataCopy => calldatacopy(s),
        Instr::ICodeSize => arith0(s, Some(&const_usize(s.get_codesize()))),
        Instr::IGasPrice => arith0(s, Some(&s.env.latest_block().gasprice)),
        Instr::IBlockHash => blockhash(s),
        Instr::ICoinBase => arith0(s, Some(&s.env.latest_block().coinbase)),
        Instr::ITimeStamp => arith0(s, Some(&s.env.latest_block().timestamp)),
        Instr::INumber => arith0(s, Some(&s.env.latest_block().number)),
        Instr::IDifficulty => arith0(s, Some(&s.env.latest_block().difficulty)),
        Instr::IGasLimit => arith0(s, Some(&s.env.latest_block().gas_limit)),
        Instr::IPop => pop_n(s, 1),
        Instr::IMLoad => memload(s),
        Instr::IMStore => mstore(s),
        Instr::IMStore8 => mstore8(s),
        Instr::ISLoad => storage_load(s),
        Instr::ISStore => sstore(s),
        Instr::IJump => jump(s),
        Instr::IJumpIf => jump_if(s),
        Instr::IPC => arith0(s, Some(&const_usize(s.pc))),
        Instr::IMSize => arith0(s, Some(&s.env.latest_block().mem_size)),
        Instr::IGas => arith0(s, Some(&s.input_tx().gas)),
        Instr::IJumpDest => vec![(s.create_succ(), edge_exec())],
        Instr::IPush(a) => arith0(s, Some(&const_vec(&a))),
        Instr::IDup(a) => arith0(s, s.stack.get(s.stack.len() - a)),
        Instr::ISwap(a) => swap(s, a),
        Instr::ILog(n) => {
            if s.flags.contains(Flags::STATIC) {
                warn!("State changing log operation during static call, dropping path!");
                return vec![];
            }
            pop_n(s, n + 2)
        }
        Instr::ICall => new_call(s, CallType::Call),
        Instr::IStaticCall => new_call(s, CallType::StaticCall),
        Instr::ICallCode => new_call(s, CallType::CallCode),
        Instr::IDelegateCall => new_call(s, CallType::DelegateCall),
        Instr::ISelfDestruct => selfdestruct(s),
        Instr::IStop => stop(s),
        Instr::IRevert => revert(s),
        Instr::IReturn => ireturn(s),
        Instr::IInvalid => vec![], // execution reached invalid state, drop path
        Instr::ICodeCopy => code_copy(s),
        Instr::IRDataSize => returndata_size(s),
        Instr::IRDataCopy => returndata_copy(s),
        Instr::IExtCodeSize => extcode_size(s),
        Instr::ISext => sign_extend(s),
        Instr::IExtCodeCopy => ext_code_copy(s),
        Instr::ICreate => create_account(s),
        Instr::ICreate2 => fail_unknown(&ins),
    }
}
