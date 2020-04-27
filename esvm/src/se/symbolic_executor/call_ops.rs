use std::sync::Arc;

use crate::se::{
    config::HIJACK_ADDR,
    env::{AccountId, TxId},
    expr::{
        bval::*,
        symbolic_memory::{memcopy, memset},
    },
    symbolic_analysis::{Analysis, AnalysisMode},
    symbolic_edge::*,
    symbolic_state::{Flags, HaltingReason, ResultState, SeState},
};

pub fn create_account(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some(_) = res.pop3() {
        let callres = fresh_var("account_creation");
        let constraint = or(&eql(&callres, &one()), &eql(&callres, &zero()));
        res.push_constraint(constraint);
        res.stack.push(callres);
    }
    vec![(res, edge_exec())]
}

fn call_op<F>(to: &BVal, s: SeState, include_self: bool, f: F) -> Vec<(SeState, EdgeType)>
where
    F: Fn(&BVal, &BVal, AccountId, SeState) -> Option<Vec<(SeState, EdgeType)>>,
{
    if FVal::as_bigint(&to).is_some() {
        let mut res = s.fork();
        let id = if let Some(id) = s.env.try_get_account_id_by_addr(to) {
            *id
        } else {
            let maybe_id = Arc::make_mut(&mut res.env)
                .try_load_account_from_chain(Arc::make_mut(&mut res.memory), to);
            if maybe_id.is_none() {
                return vec![];
            }
            maybe_id.unwrap()
        };

        if let Some(transition) = f(to, to, id, res) {
            transition
        } else {
            vec![]
        }
    } else {
        let mut states = vec![];
        let accounts = if include_self {
            s.env.get_addresses_except(&s.account)
        } else {
            s.env.get_addresses()
        };
        for (addr, id) in accounts {
            let fork = s.fork();
            if let Some(mut transition) = f(to, &addr, id, fork) {
                states.append(&mut transition);
            }
        }
        states
    }
}

// fork over all known accounts in the execution env
pub fn extcode_size(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some(to) = res.pop1() {
        return call_op(&to, res, false, |to, addr, id, mut check| {
            // add constraint along this path
            check.push_constraint(eql(&to, &addr));
            let codesize = const_usize(check.env.get_account(&id).get_codesize());
            if !check.check_sat() {
                return None;
            }
            check.push(codesize);
            Some(vec![(check, edge_exec())])
        });
    }
    vec![]
}

// fork over all known accounts in the execution env
pub fn balance(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some(to) = res.pop1() {
        let possible_states = call_op(&to, res, false, |to, addr, id, mut check| {
            // add constraint along this path
            check.push_constraint(eql(&to, &addr));
            let balance = Arc::clone(&check.env.get_account(&id).balance);
            if !check.check_sat() {
                return None;
            }
            check.push(balance);
            Some(vec![(check, edge_exec())])
        });
        return possible_states;
    }
    vec![]
}

pub fn selfdestruct(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some(to) = res.pop1() {
        return call_op(&to, res, true, |to, addr, id, mut fork| {
            fork.push_constraint(eql(to, addr));

            if !fork.check_sat() {
                return None;
            }

            let victim_balance = Arc::clone(&fork.account().balance);

            // update balance
            {
                let acc = Arc::make_mut(&mut fork.env).get_account_mut(&id);

                let new_balance = add(&victim_balance, &acc.balance);
                acc.balance = new_balance;
            }
            fork.account_mut().selfdestruct = true;

            fork.reset_returndata();
            fork.halting_reason = Some(HaltingReason::Selfdestruct);
            Some(vec![(fork, edge_terminal())])
        });
    }
    vec![]
}

#[derive(Clone, Copy, PartialEq)]
pub enum CallType {
    Call,
    StaticCall,
    CallCode,
    DelegateCall,
}

fn set_precompiled_contracts_flags(s: &mut SeState, to: &BVal) {
    if let Some(u) = FVal::as_usize(to) {
        match u {
            0x1 => s.flags |= Flags::ECDSA_RECOVERY,
            0x2 => s.flags |= Flags::SHA256,
            0x3 => s.flags |= Flags::RIPEMD160,
            0x4 => s.flags |= Flags::IDENTITY,
            0x5 => s.flags |= Flags::MODULAR_EXPONENTIATION,
            0x6 => s.flags |= Flags::EC_ADDITION,
            0x7 => s.flags |= Flags::EC_SCALAR_MULTIPLICATION,
            0x8 => s.flags |= Flags::EC_PAIRING_EQUATION,
            _ => {}
        }
    }
}

pub fn new_call(s: &SeState, call_type: CallType) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some(args) = args_for_call(&mut res, call_type) {
        let CallArgs {
            ref gas,
            ref to,
            ref value,
            ref in_off,
            ref in_size,
            ref out_off,
            ref out_size,
        } = args;
        if res.call_depth > res.config().call_depth_limit {
            info!("Call depth limit reached, dropping path!");
            return vec![];
        }

        if s.flags.contains(Flags::STATIC) && call_type.is_static_call() {
            debug!("Restricting value during static call!");
            res.push_constraint(eql(value, &zero()));
        }

        let mut transitions = vec![];

        // check for reeantrancy, control flow hijack and precompiled contracts
        match call_type {
            CallType::Call | CallType::StaticCall => {
                set_precompiled_contracts_flags(&mut res, to);
                if let Some(reeantrancy) = check_for_reeantrancy(&res, &args) {
                    transitions.push(reeantrancy);
                }
            }
            CallType::CallCode | CallType::DelegateCall => {
                if let Some(hijack) = check_for_control_flow_hijack(&res, to) {
                    transitions.push(hijack);
                }
            }
        };

        let res = res; // make res imutable from here

        transitions.append(&mut call_op(to, res, true, |to, addr, id, mut call| {
            let mut trans = Vec::new();
            // constrain address
            call.push_constraint(eql(to, &addr));

            // check if the address is actually possible
            if !call.check_sat() {
                return None;
            }

            // Create a failure state to simulate the call failing
            // create and push a failure state
            trans.push(create_failure_state(&call, id));

            let tx_type = match call_type {
                CallType::Call | CallType::StaticCall => TxType::Call(id),
                CallType::CallCode => TxType::CallCode,
                CallType::DelegateCall => TxType::DelegateCall,
            };

            // Create a new transaction for the real call
            let tx = create_new_outgoing(&mut call, gas, in_size, out_size, in_off, value, tx_type);

            // on normal calls just simulate value transfer
            if (call_type.is_static_call() || call_type.is_call())
                && call.env.get_account(&id).code().is_none()
            {
                info!(
                    "Transfering money from {:?} to {:?}",
                    call.account().addr,
                    addr
                );
                // no account code, i.e. we only tramsfer money
                let callres = fresh_var(&format!(
                    "call_{}_to_{}_normal",
                    call.account().name,
                    call.env.get_account(&id).name
                ));
                call.push_constraint(eql(&callres, &one()));
                call.stack.push(callres);

                trans.push((call, edge_call_ret()));
            } else if call.env.get_account(&id).code().is_some() && cfg!(feature = "calls") {
                match call_type {
                    CallType::Call | CallType::StaticCall => {
                        info!(
                            "Executing {} from {:?} to {:?}",
                            call_type.name(),
                            call.account().addr,
                            addr
                        );
                    }
                    CallType::CallCode | CallType::DelegateCall => {
                        info!(
                            "Executing {} from {:?} with code {:?}",
                            call_type.name(),
                            call.account().addr,
                            addr
                        );
                    }
                }

                let code = call.env.get_account(&id).code().unwrap();
                let end_states = match call_type {
                    CallType::Call | CallType::StaticCall => {
                        execute_contract(&call, &call.account().id, &id, &tx, &code)
                    }
                    CallType::CallCode => {
                        execute_contract(&call, &call.account().id, &call.account, &tx, &code)
                    }
                    CallType::DelegateCall => {
                        // delegate call
                        let to = call
                            .env
                            .try_get_account_id_by_addr(&call.input_tx().caller)
                            .unwrap();
                        execute_contract(&call, to, &call.account, &tx, &code)
                    }
                };

                for end_state in end_states {
                    let callres_execution = fresh_var(&format!(
                        "{}_{}_{}_execution",
                        call_type.var_name(),
                        call.account().name,
                        call.env.get_account(&id).name
                    ));

                    trans.push(create_return_state(
                        &call,
                        end_state,
                        callres_execution,
                        out_off,
                        out_size,
                    ));
                }
            }
            Some(trans)
        }));
        return transitions;
    }
    vec![]
}

impl CallType {
    fn is_static_call(self) -> bool {
        if let CallType::StaticCall = self {
            true
        } else {
            false
        }
    }

    fn is_call(self) -> bool {
        if let CallType::Call = self {
            true
        } else {
            false
        }
    }

    fn name(&self) -> &str {
        match self {
            CallType::Call => "call",
            CallType::StaticCall => "static call",
            CallType::CallCode => "call code",
            CallType::DelegateCall => "delegate call",
        }
    }

    fn var_name(&self) -> &str {
        match self {
            CallType::Call => "call",
            CallType::StaticCall => "static_call",
            CallType::CallCode => "call_code",
            CallType::DelegateCall => "delegate_call",
        }
    }
}

struct CallArgs {
    gas: BVal,
    to: BVal,
    value: BVal,
    in_off: BVal,
    in_size: BVal,
    out_off: BVal,
    out_size: BVal,
}

fn args_for_call(state: &mut SeState, call_type: CallType) -> Option<CallArgs> {
    match call_type {
        CallType::Call | CallType::StaticCall | CallType::CallCode => {
            let (gas, to, value, in_off, in_size, out_off, out_size) = state.pop7()?;
            Some(CallArgs {
                gas,
                to,
                value,
                in_off,
                in_size,
                out_off,
                out_size,
            })
        }
        CallType::DelegateCall => {
            let (gas, to, in_off, in_size, out_off, out_size) = state.pop6()?;
            let value = Arc::clone(&state.input_tx().callvalue);
            Some(CallArgs {
                gas,
                to,
                value,
                in_off,
                in_size,
                out_off,
                out_size,
            })
        }
    }
}

fn create_failure_state(s: &SeState, id: AccountId) -> (SeState, EdgeType) {
    let mut failure = s.fork();
    let callres_fail = fresh_var(&format!(
        "call_{}_to_{}_fail",
        failure.account().name,
        failure.env.get_account(&id).name
    ));

    failure.push_constraint(eql(&callres_fail, &zero()));
    failure.push(callres_fail);

    failure.flags |= Flags::FAILURE;
    (failure, edge_call_ret())
}

fn execute_contract(
    s: &SeState,
    from: &AccountId,
    to: &AccountId,
    outgoing_tx: &TxId,
    code: &[u8],
) -> Vec<ResultState> {
    let mut exe = s.clone();
    exe.call_depth += 1;

    let config = exe.context.config().clone();
    let memory = Arc::clone(&s.memory);

    let context = Analysis::from_result_state(
        code,
        from,
        to,
        config,
        exe.as_result_state(),
        AnalysisMode::Call(*outgoing_tx),
        memory,
    );
    context.execute_call()
}

fn create_return_state(
    s: &SeState,
    end_state: ResultState,
    callres_execution: BVal,
    out_off: &BVal,
    out_size: &BVal,
) -> (SeState, EdgeType) {
    let mut return_state = s.fork();

    // copy env
    return_state.env = Arc::clone(&end_state.env);

    // constraints
    return_state.set_constraints(&end_state.constraints);

    // update old memory
    Arc::make_mut(&mut return_state.old_memory).insert(end_state.mem);

    // reads
    return_state.reads = Arc::clone(&end_state.reads);

    // flags
    return_state.flags = (end_state.flags & Flags::NON_STATIC_MASK) | s.flags;

    // keccak
    return_state.keccaks = Arc::clone(&end_state.keccaks);

    // memory
    let mut memory = Arc::clone(&end_state.memory);

    // tracker
    return_state.constraints_tracker = Arc::clone(&end_state.constraints_tracker);

    // clone return data if available and set callres constraint
    match end_state.halting_reason {
        Some(HaltingReason::Revert) => {
            return_state.push_constraint(eql(&callres_execution, &zero()));
            return_state.returndata = end_state.returndata;
            return_state.returndata_size = end_state.returndata_size;
            return_state.mem = memcopy(
                Arc::make_mut(&mut memory),
                s.mem,
                return_state.returndata.unwrap(),
                out_off,
                &const_usize(0),
                out_size,
            );
        }
        Some(HaltingReason::Return) => {
            return_state.push_constraint(eql(&callres_execution, &one()));
            return_state.returndata = end_state.returndata;
            return_state.returndata_size = end_state.returndata_size;
            return_state.mem = memcopy(
                Arc::make_mut(&mut memory),
                s.mem,
                return_state.returndata.unwrap(),
                out_off,
                &const_usize(0),
                out_size,
            );
        }
        Some(HaltingReason::Stop) | Some(HaltingReason::Selfdestruct) => {
            return_state.push_constraint(eql(&callres_execution, &one()));
            return_state.returndata = None;
            return_state.returndata_size = const_usize(0);
            return_state.mem = memset(
                Arc::make_mut(&mut memory),
                s.mem,
                out_off,
                &const_usize(0),
                out_size,
            );
        }
        None => panic!("Did not set halting state correctly / did not correctly return end states"),
    }
    return_state.memory = memory;
    return_state.stack.push(callres_execution);

    (return_state, edge_call_ret())
}

pub enum TxType {
    Call(AccountId),
    CallCode,
    DelegateCall,
}

pub fn create_new_outgoing(
    s: &mut SeState,
    gas: &BVal,
    in_size: &BVal,
    out_size: &BVal,
    in_off: &BVal,
    value: &BVal,
    to: TxType,
) -> TxId {
    let acc_name = s.account().name.clone();
    let origin = Arc::clone(&s.input_tx().origin); // origin

    let caller = match &to {
        TxType::Call(_) | TxType::CallCode => s.account,
        TxType::DelegateCall => *s
            .env
            .try_get_account_id_by_addr(&s.input_tx().caller)
            .unwrap(),
    };
    let to = match to {
        TxType::Call(a) => a,
        TxType::CallCode | TxType::DelegateCall => s.account,
    };

    let env = Arc::make_mut(&mut s.env);
    let memory = Arc::make_mut(&mut s.memory);

    let outgoing_tx = env.new_output_tx(
        memory,
        &acc_name, // name
        &caller,   // caller
        &origin,   // origin
        &to,       // addr
        gas,       // gas
        value,
        &Arc::clone(in_size),  // calldata_size
        &Arc::clone(out_size), // returndata_size
    );

    // copy outgoing tx data from current execution
    let data = env.get_tx(&outgoing_tx).data;
    env.get_tx_mut(&outgoing_tx).data =
        memcopy(memory, data, s.mem, &const_usize(0), in_off, in_size);

    outgoing_tx
}

fn check_for_control_flow_hijack(s: &SeState, to: &BVal) -> Option<(SeState, EdgeType)> {
    let mut hijack = s.fork();
    hijack.push_constraint(eql(to, &const256(HIJACK_ADDR)));
    if hijack.check_sat() {
        hijack.flags |= Flags::HIJACK_CONTROL_FLOW;

        let callres_hijack = fresh_var(&format!("call_code_{}_hijack", hijack.account().name,));
        hijack.push_constraint(eql(&callres_hijack, &one()));
        hijack.stack.push(callres_hijack);

        return Some((hijack, edge_call_ret()));
    }
    None
}

fn check_for_reeantrancy(s: &SeState, args: &CallArgs) -> Option<(SeState, EdgeType)> {
    let mut reentrancy = s.fork();
    let reentrancy_id = s
        .env
        .try_get_account_id_by_addr(&const256(HIJACK_ADDR))
        .unwrap();

    // create new outgoing tx
    let _outgoing_tx = create_new_outgoing(
        &mut reentrancy,
        &args.gas,
        &args.in_size,
        &args.out_size,
        &args.in_off,
        &args.value,
        TxType::Call(*reentrancy_id),
    );

    reentrancy.push_constraint(eql(&args.to, &const256(HIJACK_ADDR)));
    reentrancy.push_constraint(lt(&const_usize(2300), &args.gas));

    if reentrancy.check_sat() {
        reentrancy.flags |= Flags::REENTRANCY;

        let callres_reeentrancy =
            fresh_var(&format!("reentrancy_{}_res", reentrancy.account().name,));
        reentrancy.push_constraint(eql(&callres_reeentrancy, &one()));
        reentrancy.stack.push(callres_reeentrancy);

        return Some((reentrancy, edge_call_ret()));
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::collections::HashSet;
    use std::env;
    use std::iter::FromIterator;

    use parity_connector::BlockSelector;
    use uint::U256;

    use crate::se::config::{ORIGIN, TARGET_ADDR};
    use crate::se::symbolic_analysis::{ParityInfo, CONFIG};
    use crate::test_helpers::{generate_test_graph, generate_test_state};

    //  This "unit" test is terribly designed, it tests way to much...
    #[test]
    fn call_value_transfer_test() {
        let mut state = generate_test_state();
        let gas = const_usize(0xAA);
        let to = const_u256(U256::from_dec_str(ORIGIN).unwrap()); //
        let value = const_usize(0xCC);
        let in_off = const_usize(0xDD);
        let in_size = const_usize(0xEE);
        let out_off = const_usize(0xFF);
        let out_size = const_usize(0x11);
        state.push(out_size);
        state.push(out_off);
        state.push(in_size);
        state.push(in_off);
        state.push(value);
        state.push(Arc::clone(&to));
        state.push(gas);

        let orig_env = Arc::clone(&state.env);
        let orig_victim_balance = Arc::clone(&state.account().balance);
        let attacker = state.env.try_get_account_by_addr(&Arc::clone(&to)).unwrap();
        let orig_attacker_balance = Arc::clone(&attacker.balance);

        let attacker_name = &attacker.name;
        let victim_name = &state.account().name;

        let mut transitions = new_call(&state, CallType::Call);

        // both transitions
        let mut success = transitions.pop().unwrap().0;
        let mut fail = transitions.pop().unwrap().0;

        // check constraints
        let fail_constraint = Arc::make_mut(&mut fail.constraints).pop().unwrap();
        assert_eq!(
            eql(
                &var(&format!("call_{}_to_{}_fail_1", victim_name, attacker_name)),
                &const_usize(0)
            ),
            fail_constraint
        );
        let success_constraint = Arc::make_mut(&mut success.constraints).pop().unwrap();
        assert_eq!(
            eql(
                &var(&format!(
                    "call_{}_to_{}_normal_1",
                    victim_name, attacker_name
                )),
                &const_usize(1)
            ),
            success_constraint
        );

        // check env
        assert_eq!(orig_env, fail.env);

        let attacker = success
            .env
            .try_get_account_by_addr(&Arc::clone(&to))
            .unwrap();
        let victim = success.account();

        let victim_balance = sub(&orig_victim_balance, &const_usize(0xCC));
        let attacker_balance = add(&orig_attacker_balance, &const_usize(0xCC));

        assert_eq!(victim_balance, victim.balance);
        assert_eq!(attacker_balance, attacker.balance);
    }

    #[test]
    fn create_new_outgoing_test() {
        let ins = vec![];
        let g = generate_test_graph(ins);

        let mut state = g.get_state_by_id(1).clone();
        Arc::make_mut(&mut state.env).new_account(
            Arc::make_mut(&mut state.memory),
            "test_acc",
            &const_usize(0),
            None,
            &const_usize(1),
        );
        let start_env = Arc::clone(&state.env);
        let id = create_new_outgoing(
            &mut state,
            &const_usize(0),
            &const_usize(0),
            &const_usize(0),
            &const_usize(0),
            &const_usize(0),
            TxType::CallCode,
        );
        assert_ne!(start_env, state.env);

        // just check for no panic
        let _ = state.env.get_tx(&id);
    }

    #[test]
    fn call_ops_test() {
        let state = generate_test_graph(vec![]).get_state_by_id(1).clone();
        let coinbase = Arc::clone(&state.env.latest_block().coinbase);

        let res = call_op(&coinbase, state, false, |to, addr, _id, s| {
            let mut res = s.fork();
            res.push_constraint(add(to, addr));
            Some(vec![(res, edge_terminal())])
        });

        // get constraints
        let constraints = {
            let mut r = vec![];
            for re in res {
                r.push(Arc::clone(&re.0.constraints[0]));
            }
            HashSet::from_iter(r.into_iter())
        };

        let mut correct = HashSet::new();
        correct.insert(add(
            &coinbase,
            &const_u256(U256::from_dec_str(TARGET_ADDR).unwrap()),
        ));
        correct.insert(add(
            &coinbase,
            &const_u256(U256::from_dec_str(ORIGIN).unwrap()),
        ));
        correct.insert(add(
            &coinbase,
            &const_u256(U256::from_dec_str(HIJACK_ADDR).unwrap()),
        ));

        assert_eq!(correct, constraints);
    }

    #[test]
    #[ignore]
    fn parity_call_ops_test() {
        let ip = env::var("PARITY_IP").unwrap();
        // init global config with parity
        let parity = ParityInfo(ip, 8545, BlockSelector::Specific(6281955));
        CONFIG.write().unwrap().parity = Some(parity);

        let state = generate_test_graph(vec![]).get_state_by_id(1).clone();
        let addr = const_u256(
            U256::from_dec_str("228723907117702717599418931794880362350572260118").unwrap(),
        );

        let res = call_op(&addr, state, false, |to, addr, id, s| {
            assert_eq!(to, addr);
            let mut res = s.fork();
            {
                let balance = Arc::clone(&res.env.get_account(&id).balance);
                res.push_constraint(add(&var("dummy"), &balance));
            }
            Some(vec![(res, edge_terminal())])
        });

        let correct = add(
            &var("dummy"),
            &const_u256(U256::from_dec_str("1538423056629367645420298").unwrap()),
        );
        let balance = Arc::clone(&res[0].0.constraints[0]);
        assert_eq!(correct, balance);

        CONFIG.write().unwrap().parity = None;
    }
}
