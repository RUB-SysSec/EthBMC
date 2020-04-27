use std::sync::Arc;

use crate::se::{
    env::fresh_var_name,
    expr::bval::*,
    expr::symbolic_memory::{self, *},
    symbolic_edge::*,
    symbolic_state::{Flags, HaltingReason, SeState},
};

pub fn code_copy(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some((mem_addr, code_addr, size)) = res.pop3() {
        let (code_addr_c, size_c) = match (FVal::as_usize(&code_addr), FVal::as_usize(&size)) {
            (Some(a), Some(b)) => (a, b),
            _ => {
                warn!("Can't get constant values for code copy, dropping path");
                return vec![];
            }
        };

        return copy_code_to_mem(
            s,
            res,
            &mem_addr,
            code_addr_c,
            size_c,
            s.account().code().unwrap(),
        );
    }
    vec![]
}

pub fn ext_code_copy(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some((addr, mem_addr, code_addr, size)) = res.pop4() {
        let (code_addr_c, size_c) = match (FVal::as_usize(&code_addr), FVal::as_usize(&size)) {
            (Some(a), Some(b)) => (a, b),
            _ => {
                warn!("Can't get constant values for ext code copy, dropping path");
                return vec![];
            }
        };

        let code;
        {
            let acc = if let Some(acc) = s.env.try_get_account_by_addr(&addr) {
                acc
            } else {
                let memory = Arc::make_mut(&mut res.memory);
                let maybe_id =
                    Arc::make_mut(&mut res.env).try_load_account_from_chain(memory, &addr);
                if maybe_id.is_none() {
                    // we could copy from an symbolic array here
                    warn!("Unsupported symbolic ext code copy, dropping path!");
                    return vec![];
                }
                res.env.get_account(&maybe_id.unwrap())
            };

            code = acc.code().cloned().unwrap(); // this is super inefficient but w/e
        }

        return copy_code_to_mem(s, res, &mem_addr, code_addr_c, size_c, &code);
    }
    vec![]
}

fn copy_code_to_mem(
    s: &SeState,
    mut res: SeState,
    mem_addr: &BVal,
    code_addr_c: usize,
    size_c: usize,
    code: &[u8],
) -> Vec<(SeState, EdgeType)> {
    // merge 256 byte writes
    let quot = size_c / 32;
    let rem = size_c % 32;

    let mut c_addr;
    for i in 0..quot {
        let mut current_256_byte: Vec<u8> = Vec::with_capacity(32);

        for j in 0..32 {
            // move offset
            c_addr = code_addr_c + (i * 32) + j;
            if c_addr >= code.len() {
                warn!("Code copy out of bounds, halting execution");
                let mut res = s.create_succ();
                res.halting_reason = Some(HaltingReason::Stop);
                return vec![(res, edge_terminal())];
            }
            let byte = code[c_addr];
            current_256_byte.push(byte);
        }

        res.mem = word_write(
            Arc::make_mut(&mut res.memory),
            res.mem,
            &add(&mem_addr, &const_usize(i * 32)),
            &const_u256(current_256_byte.as_slice().into()),
        );
    }

    let code_offset = code_addr_c + (32 * quot);
    for i in 0..rem {
        c_addr = code_offset + i;
        if c_addr >= code.len() {
            warn!("Code copy out of bounds, halting execution");
            let mut res = s.create_succ();
            res.halting_reason = Some(HaltingReason::Stop);
            return vec![(res, edge_terminal())];
        }
        let byte = code[c_addr];
        res.mem = byte_write(
            Arc::make_mut(&mut res.memory),
            res.mem,
            &add(&mem_addr, &const_usize((quot * 32) + i)),
            &const_usize(byte as usize),
        );
    }

    vec![(res, edge_exec())]
}

pub fn returndata_copy(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some((mem_addr, ret_addr, size)) = res.pop3() {
        res.mem = match res.returndata {
            Some(ret) => memcopy(
                Arc::make_mut(&mut res.memory),
                res.mem,
                ret,
                &mem_addr,
                &ret_addr,
                &size,
            ),
            None => memset(
                Arc::make_mut(&mut res.memory),
                res.mem,
                &mem_addr,
                &const_usize(0),
                &size,
            ),
        };
        return vec![(res, edge_exec())];
    }
    vec![]
}

pub fn returndata_size(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    res.push(Arc::clone(&s.returndata_size));
    vec![(res, edge_exec())]
}

pub fn calldatacopy(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some((mem_addr, data_addr, size)) = res.pop3() {
        // fix size variable in concrete mode
        if s.config().concrete_copy {
            res.push_constraint(le(&size, &const_usize(256)));
        }
        res.mem = memcopy(
            Arc::make_mut(&mut res.memory),
            s.mem,
            s.input_tx().data,
            &mem_addr,
            &data_addr,
            &size,
        );
        return vec![(res, edge_exec())];
    }
    vec![]
}

pub fn calldataload(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some(ref addr) = res.stack.pop() {
        let load = mload(&res.memory, res.input_tx().data, addr);
        res.record_read(&load);
        res.push(load);
        return vec![(res, edge_exec())];
    }
    vec![]
}

pub fn memload(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some(ref addr) = res.stack.pop() {
        let load = mload(&res.memory, res.mem, addr);
        res.record_read(&load);
        res.push(load);
        return vec![(res, edge_exec())];
    }
    vec![]
}

pub fn mstore(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some((addr, val)) = res.pop2() {
        res.mem = word_write(Arc::make_mut(&mut res.memory), res.mem, &addr, &val);
        return vec![(res, edge_exec())];
    }
    vec![]
}

pub fn mstore8(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some((addr, val)) = res.pop2() {
        res.mem = byte_write(Arc::make_mut(&mut res.memory), res.mem, &addr, &val);
        return vec![(res, edge_exec())];
    }
    vec![]
}

fn extract_mapping_key(memory: &SymbolicMemory, val: &BVal) -> Option<BVal> {
    match val.val() {
        Val256::FSHA3(mem, ref offset, ref len) => {
            match (
                FVal::check_truth(&eql(offset, &const_usize(0))),
                FVal::check_truth(&eql(len, &const_usize(0x40))),
            ) {
                (SymbolicTruth::True, SymbolicTruth::True) => {}
                _ => return None,
            }
            let position = mload(memory, *mem, &add(offset, &const_usize(0x20)));
            if !matches!(position, Val256::FConst(..)) {
                return None;
            }
            Some(position)
        }
        _ => None,
    }
}

pub fn keccak(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some((offset, len)) = res.pop2() {
        let keccak = sha3(&s.memory, s.mem, &offset, &len);

        // record the keccak result
        if !FVal::is_constant(&keccak) {
            res.record_keccak_result(&keccak);
        }

        res.push(keccak);
        return vec![(res, edge_exec())];
    }
    vec![]
}

pub fn storage_load(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some(ref addr) = res.stack.pop() {
        let load = if cfg!(feature = "keccak") {
            let mut mapping_key = None;
            match addr.val() {
                Val256::FSHA3(..) => {
                    mapping_key = extract_mapping_key(&res.memory, &addr);
                }
                Val256::FAdd(ref a, ref b) => {
                    if !(matches!(a, Val256::FSHA3(..)) && matches!(b, Val256::FSHA3(..))) {
                        if matches!(a, Val256::FSHA3(..)) {
                            mapping_key = extract_mapping_key(&res.memory, a);
                        }
                        if matches!(b, Val256::FSHA3(..)) {
                            mapping_key = extract_mapping_key(&res.memory, b);
                        }
                    }
                }
                _ => {}
            }

            // remove sha3 key from stored set
            if mapping_key.is_some() {
                res.remove_keccak_result(addr);
            }

            if let Some(key) = mapping_key {
                {
                    if let Some(mem) = res.account().mappings.get(&key) {
                        debug!("Load from mapping: {:?}", key);
                        sload(&s.memory, *mem, addr)
                    } else {
                        debug!("Mapping never writen to, returning zero!");
                        zero()
                    }
                }
            } else {
                sload(&s.memory, s.account().storage, addr)
            }
        } else {
            sload(&s.memory, s.account().storage, addr)
        };
        res.record_read(&load);
        res.push(load);
        return vec![(res, edge_exec())];
    }
    vec![]
}

pub fn sstore(s: &SeState) -> Vec<(SeState, EdgeType)> {
    if s.flags.contains(Flags::STATIC) {
        warn!("State changing sstore operation during static call, dropping path!");
        return vec![];
    }
    let mut res = s.create_succ();
    if let Some((addr, val)) = res.pop2() {
        let mut mapping_key = None;
        if cfg!(feature = "keccak") {
            match addr.val() {
                Val256::FSHA3(..) => {
                    mapping_key = extract_mapping_key(&res.memory, &addr);
                }
                Val256::FAdd(ref a, ref b) => {
                    if !(matches!(a, Val256::FSHA3(..)) && matches!(b, Val256::FSHA3(..))) {
                        if matches!(a, Val256::FSHA3(..)) {
                            mapping_key = extract_mapping_key(&res.memory, a);
                        }
                        if matches!(b, Val256::FSHA3(..)) {
                            mapping_key = extract_mapping_key(&res.memory, b);
                        }
                    }
                }
                _ => {}
            }

            // remove sha3 key from stored set
            if mapping_key.is_some() {
                res.remove_keccak_result(&addr);
            }

            if let Some(key) = mapping_key.clone() {
                {
                    debug!("Write to mapping: {:?}", key);
                    let entry_key;
                    {
                        let mem = symbolic_memory::create_new_memory(
                            Arc::make_mut(&mut res.memory),
                            fresh_var_name("mapping"),
                            MemoryType::Storage,
                            None,
                        );
                        let mapping = Arc::make_mut(&mut res.account_mut().mappings);
                        entry_key = *mapping.entry(key.clone()).or_insert_with(|| mem);
                    }

                    let write = word_write(Arc::make_mut(&mut res.memory), entry_key, &addr, &val);
                    Arc::make_mut(&mut res.account_mut().mappings).insert(key, write);
                }

                return vec![(res, edge_exec())];
            }
        }
        let new_storage = word_write(
            Arc::make_mut(&mut res.memory),
            s.account().storage,
            &addr,
            &val,
        );
        res.account_mut().storage = new_storage;
        return vec![(res, edge_exec())];
    }
    vec![]
}

pub fn revert(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some((addr, size)) = res.pop2() {
        set_returndata(&mut res, &addr, &size);
        res.halting_reason = Some(HaltingReason::Revert);
        res.revert_state_changes();

        return vec![(res, edge_terminal())];
    }
    vec![]
}

pub fn ireturn(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some((addr, size)) = res.pop2() {
        // set returndata
        set_returndata(&mut res, &addr, &size);
        res.halting_reason = Some(HaltingReason::Return);

        return vec![(res, edge_terminal())];
    }

    vec![]
}

pub fn set_returndata(s: &mut SeState, addr: &BVal, size: &BVal) {
    let name = format!("{}_returndata", s.account().name);
    let mut returndata = symbolic_memory::create_new_memory(
        Arc::make_mut(&mut s.memory),
        name,
        MemoryType::Data,
        Some(size.clone()),
    );
    returndata = memcopy(
        Arc::make_mut(&mut s.memory),
        returndata,
        s.mem,
        &const_usize(0),
        &addr,
        &size,
    );
    s.returndata = Some(returndata);
    s.returndata_size = size.clone();
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::test_helpers::generate_test_graph;

    use std::collections::HashSet;
    use std::iter::FromIterator;

    use crate::bytecode::Instr;
    use crate::disasm::Disasm;
    use crate::se::{
        env::Env,
        expr::solver::Solvers,
        symbolic_analysis::{Context, CONFIG},
        symbolic_graph::SymbolicGraph,
        symbolic_state::{HaltingReason, SeState},
    };

    #[test]
    fn memload_test() {
        CONFIG.write().unwrap().disable_optimizations = true;
        let ins = vec![
            Instr::IPush(vec![0x01]), // value for store
            Instr::ICaller,           // create sym value
            Instr::IMStore,
            Instr::ICaller,
            Instr::IMLoad,
        ];
        let g = generate_test_graph(ins);
        let state = &g.get_state_by_id(6);
        let store_addr = &state.input_tx().caller;

        let mut memory = (*g.get_state_by_id(1).memory).clone();
        let mut correct_mem = symbolic_memory::create_new_memory(
            &mut memory,
            format!("{}_mem_1", state.account().name.clone()),
            MemoryType::Memory,
            None,
        );
        correct_mem = word_write(&mut memory, correct_mem, store_addr, &const_usize(0x01));

        let correct_bval = mload(&memory, correct_mem, store_addr);

        assert_eq!(
            HashSet::<BVal>::from_iter((0..32).into_iter().map(|i| mload8(
                &memory,
                state.mem,
                &add(&const_usize(i), &store_addr)
            ))),
            state.get_reads(state.mem).unwrap()
        );
        assert!(compare_bval(&correct_bval, &state.stack[0]));

        CONFIG.write().unwrap().disable_optimizations = false;
    }

    #[test]
    fn calldataload_test() {
        let ins = vec![
            Instr::IPush(vec![0x01]), // value for read
            Instr::ICallDataLoad,
        ];
        let g = generate_test_graph(ins);

        let state = &g.get_state_by_id(3);

        let store_addr = const_usize(0x01);
        let mut memory = (*g.get_state_by_id(1).memory).clone();
        let correct_data = symbolic_memory::create_new_memory(
            &mut memory,
            format!("{}_data", state.input_tx().name.clone()),
            MemoryType::Data,
            Some(state.input_tx().calldata_size.clone()),
        );
        let correct_bval = mload(&memory, correct_data, &store_addr);

        assert_eq!(
            HashSet::<BVal>::from_iter((0..32).into_iter().map(|i| mload8(
                &memory,
                state.input_tx().data,
                &add(&const_usize(i), &store_addr)
            ))),
            state.get_reads(state.input_tx().data).unwrap()
        );
        assert!(
            compare_bval(&correct_bval, &state.stack[0]),
            "\n\tleft: {:?}\n\tright: {:?}",
            &correct_bval,
            &state.stack[0]
        );
    }

    #[test]
    fn return_test() {
        let ins = vec![
            Instr::IPush(vec![0x41, 0x41, 0x41, 0x41]), // value
            Instr::IPush(vec![0x10]),                   // addr
            Instr::ISStore,
            Instr::IPush(vec![0x41, 0x41, 0x41, 0x41]), // size
            Instr::IPush(vec![0x10]),                   // addr
            Instr::IReturn,
        ];
        let g = generate_test_graph(ins);

        let state = &g.get_state_by_id(6);
        let mut memory = (*g.get_state_by_id(1).memory).clone();
        let mut returndata = symbolic_memory::create_new_memory(
            &mut memory,
            format!("{}_returndata", state.account().name),
            MemoryType::Data,
            Some(const_usize(0x41414141)),
        );
        returndata = memcopy(
            &mut memory,
            returndata,
            state.mem,
            &const_usize(0),
            &const_usize(0x10),
            &const_usize(0x41414141),
        );

        let state = &g.get_state_by_id(7);
        assert_eq!(const_usize(0x41414141), state.returndata_size);
        assert!(symbolic_memory::memory_info_equal(
            &memory[returndata],
            &state.memory[state.returndata.clone().unwrap()]
        ));
        assert!(!symbolic_memory::memory_info_equal(
            &state.memory[g.get_state_by_id(1).account().storage],
            &state.memory[state.account().storage]
        ));
    }

    #[test]
    fn revert_test() {
        let ins = vec![
            Instr::IPush(vec![0x41, 0x41, 0x41, 0x41]), // value
            Instr::IPush(vec![0x00]),                   // addr
            Instr::ISStore,
            Instr::IPush(vec![0x41, 0x41, 0x41, 0x41]), // size
            Instr::IPush(vec![0x00]),                   // addr
            Instr::IRevert,
        ];
        let g = generate_test_graph(ins);

        let state = &g.get_state_by_id(7);
        assert_eq!(const_usize(0x41414141), state.returndata_size);
        assert_eq!(state.halting_reason, Some(HaltingReason::Revert),);
    }

    // 0x165B98160458E9698bF85E29ED09e8c6e3dDDc85
    #[test]
    #[ignore]
    fn code_copy_large_test() {
        CONFIG.write().unwrap().concrete_load = true;

        let ins = vec![
            Instr::IPush(vec![0x13, 0x35]), // size
            Instr::IPush(vec![0x08]),       // data offset
            Instr::IPush(vec![0x00]),       // mem addr
            Instr::ICodeCopy,
        ];

        let mut code: Vec<u8> = Vec::with_capacity(0x1135 + 0x8);
        code.push(0x11);
        code.push(0x35);
        code.push(0x61);
        code.push(0x08);
        code.push(0x60);
        code.push(0x00);
        code.push(0x60);
        code.push(0x39);

        for i in 0..0x1335 {
            code.push((i % 256) as u8);
        }

        let mut env = Env::new();
        let mut memory = symbolic_memory::new_memory();

        let attacker = env.new_attacker_account(&mut memory);
        let victim = env.new_victim_account(&mut memory, &code);
        let inital_tx = env.new_attacker_tx(&mut memory, attacker, victim);

        let initial_storage = env.get_account(&victim).storage;
        let dasm = Disasm::new(ins);
        let config = CONFIG.read().unwrap().clone();

        let memory = Arc::new(memory);
        let context = Arc::new(Context::new(
            config,
            dasm,
            initial_storage,
            Solvers::Yice {
                count: num_cpus::get(),
                timeout: 120_000,
            },
        ));
        let state = SeState::new(context, memory, &Arc::new(env), victim, inital_tx);

        let mut g = SymbolicGraph::new(state);
        g.analyze_graph();
        let state = &g.get_state_by_id(5);
        for i in 0..0x1335 {
            let current_byte = mload8(&state.memory, state.mem, &const_usize(i));
            assert_eq!(
                code[i + 0x08] as usize,
                FVal::as_usize(&current_byte).unwrap(),
                "Error on code copy byte {}",
                i,
            );
        }

        // check for no panic
        state.check_sat();

        CONFIG.write().unwrap().concrete_load = false;
    }

    #[test]
    fn code_copy_test() {
        let ins = vec![
            Instr::IPush(vec![0x03]), // size
            Instr::IPush(vec![0x07]), // data offset
            Instr::IPush(vec![0x00]), // mem addr
            Instr::ICodeCopy,
        ];

        let mut env = Env::new();
        let mut memory = symbolic_memory::new_memory();

        let attacker = env.new_attacker_account(&mut memory);
        let binary = vec![0x60, 0x00, 0x60, 0x00, 0x60, 0x03, 0x39, 0xAA, 0xBB, 0xCC];
        let victim = env.new_victim_account(&mut memory, &binary);
        let inital_tx = env.new_attacker_tx(&mut memory, attacker, victim);

        let initial_storage = env.get_account(&victim).storage;
        let dasm = Disasm::new(ins);
        let config = CONFIG.read().unwrap().clone();

        let context = Arc::new(Context::new(
            config,
            dasm,
            initial_storage,
            Solvers::Yice {
                count: num_cpus::get(),
                timeout: 120_000,
            },
        ));
        let state = SeState::new(context, Arc::new(memory), &Arc::new(env), victim, inital_tx);

        let mut correct_mem = (*state.memory).clone();
        let mut mem = byte_write(
            &mut correct_mem,
            state.mem,
            &add(&const_usize(0x00), &const_usize(0x00)),
            &const_usize(0xAA),
        );
        mem = byte_write(
            &mut correct_mem,
            mem,
            &add(&const_usize(0x00), &const_usize(0x01)),
            &const_usize(0xBB),
        );
        mem = byte_write(
            &mut correct_mem,
            mem,
            &add(&const_usize(0x00), &const_usize(0x02)),
            &const_usize(0xCC),
        );

        let mut g = SymbolicGraph::new(state);
        g.analyze_graph();
        let state = &g.get_state_by_id(5);
        assert!(symbolic_memory::memory_info_equal(
            &correct_mem[mem],
            &state.memory[state.mem]
        ));
    }

    #[test]
    fn ext_code_copy_test() {
        let ins = vec![
            Instr::IPush(vec![0x03]), // size
            Instr::IPush(vec![0x07]), // data offset
            Instr::IPush(vec![0x00]), // mem addr
            Instr::IPush(vec![0xAA]), // address
            Instr::IExtCodeCopy,
        ];

        let mut env = Env::new();
        let mut memory = symbolic_memory::new_memory();

        let attacker = env.new_attacker_account(&mut memory);
        let binary = vec![0x60, 0x00, 0x60, 0x00, 0x60, 0x03, 0x39, 0xAA, 0xBB, 0xCC];
        let victim = env.new_victim_account(&mut memory, &vec![]);
        let addr = const_usize(0xAA);
        let _copy_account = env.new_account(
            &mut memory,
            "copy_test",
            &addr,
            Some(binary),
            &const_usize(0),
        );
        let inital_tx = env.new_attacker_tx(&mut memory, attacker, victim);

        let initial_storage = env.get_account(&victim).storage;
        let dasm = Disasm::new(ins);
        let config = CONFIG.read().unwrap().clone();

        let context = Arc::new(Context::new(
            config,
            dasm,
            initial_storage,
            Solvers::Yice {
                count: num_cpus::get(),
                timeout: 120_000,
            },
        ));
        let state = SeState::new(
            context,
            Arc::new(memory.clone()),
            &Arc::new(env),
            victim,
            inital_tx,
        );
        let mut memory = (*state.memory).clone();

        let mut correct_mem = byte_write(
            &mut memory,
            state.mem,
            &add(&const_usize(0x00), &const_usize(0x00)),
            &const_usize(0xAA),
        );
        correct_mem = byte_write(
            &mut memory,
            correct_mem,
            &add(&const_usize(0x00), &const_usize(0x01)),
            &const_usize(0xBB),
        );
        correct_mem = byte_write(
            &mut memory,
            correct_mem,
            &add(&const_usize(0x00), &const_usize(0x02)),
            &const_usize(0xCC),
        );

        let mut g = SymbolicGraph::new(state);
        g.analyze_graph();
        let state = &g.get_state_by_id(6);
        assert!(symbolic_memory::memory_info_equal(
            &memory[correct_mem],
            &state.memory[state.mem]
        ));
    }

    #[test]
    fn calldataload_constraint_test() {
        let ins = vec![
            Instr::IPush(vec![0x00]), // addr for read
            Instr::ICallDataLoad,
        ];
        let g = generate_test_graph(ins);

        let mut state = g.get_state_by_id(3).clone();
        let load = Arc::clone(&state.stack[0]);
        let calldata_size_ptr = Arc::clone(&state.input_tx().calldata_size);
        state.push_constraint(eql(
            &const256(
                "29515630583031984977126754662397482469828521605804793235684728428402426511360",
            ),
            &load,
        ));
        let mut fail_state = state.clone();
        state.push_constraint(eql(&const_usize(0x4), &calldata_size_ptr));

        {
            let mut read_state = state.clone();
            let addr = &const_usize(0x00);
            let data = read_state.input_tx().data;
            let load = mload(&read_state.memory, data, addr);
            read_state.push_constraint(eql(&var("A"), &load));
            read_state.record_read(&load);
            assert_eq!(
                const256(
                    "29515630583031984977126754662397482469828521605804793235684728428402426511360",
                ),
                read_state.get_value(&var("A")).unwrap()
            );
        }

        assert!(state.check_sat());

        fail_state.push_constraint(eql(&const_usize(0x2), &calldata_size_ptr));

        assert!(!fail_state.check_sat());
    }
}
