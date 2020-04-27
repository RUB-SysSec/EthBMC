use std::sync::Arc;

use crate::se::{
    expr::bval::*,
    symbolic_edge::{edge_exec, edge_terminal, EdgeType},
    symbolic_state::{HaltingReason, SeState},
};

pub fn stop(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    res.reset_returndata();
    res.halting_reason = Some(HaltingReason::Stop);
    vec![(res, edge_terminal())]
}

pub fn pop_n(s: &SeState, mut n: usize) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    while n > 0 {
        if res.stack.pop().is_none() {
            return vec![];
        }
        n -= 1;
    }
    vec![(res, edge_exec())]
}

pub fn swap(s: &SeState, n: usize) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    let last = res.stack.len() - 1;
    if let Some(low) = res.stack.get(last - n).cloned() {
        let high = res.stack[last].clone();
        res.stack[last] = low.clone();
        res.stack[last - n] = high;
        return vec![(res, edge_exec())];
    }
    vec![]
}

pub fn blockhash(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some(blocknumber) = res.stack.pop() {
        match (
            &res.env.blockhashes,
            FVal::as_usize(&blocknumber),
            FVal::as_usize(&res.env.latest_block().number),
        ) {
            (Some(hashes), Some(number), Some(current_blocknumber)) => {
                // check if future number is requested
                if number > current_blocknumber {
                    warn!("Accessing future blocknumber: {}!", number);
                    res.push(zero());
                } else {
                    let difference = current_blocknumber - number;
                    if let Some(hash) = hashes.get(difference) {
                        res.push(Arc::clone(hash));
                    } else {
                        warn!("Accessing invalid blockhash: {}!", difference);
                        res.push(zero());
                    }
                }
            }
            (Some(hashes), None, _) => {
                // symbolic number ite over all possible cases
                let mut iter = hashes.iter();
                let first = iter.next().unwrap();
                let mut ifthen = ite(
                    // condition
                    &eql(
                        &blocknumber,
                        &sub(&Arc::clone(&res.env.latest_block().number), &const_usize(0)),
                    ),
                    // true
                    &first,
                    // false
                    &const_usize(0),
                );

                // start iterating +1
                for (i, hash) in iter.enumerate() {
                    ifthen = ite(
                        // condition
                        &eql(
                            &blocknumber,
                            &sub(
                                &Arc::clone(&res.env.latest_block().number),
                                &const_usize(i + 1),
                            ),
                        ),
                        // true
                        &hash,
                        // false
                        &ifthen,
                    );
                }
                res.push(ifthen);
            }
            _ => {
                // overapproximate with latest block hash
                res.push(Arc::clone(&s.env.latest_block().blockhash));
            }
        }

        return vec![(res, edge_exec())];
    }
    vec![]
}

// Only support constant atm
pub fn exponentiation(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some((base, exponent)) = res.pop2() {
        match (FVal::as_usize(&base), FVal::as_usize(&exponent)) {
            (Some(_), Some(_)) | (Some(2), None) => {
                res.push(exp(&base, &exponent));
                return vec![(res, edge_exec())];
            }
            _ => warn!("Not supported symbolic exponentiation, dropping path"),
        }
    }
    vec![]
}

pub fn sign_extend(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some((size, value)) = res.pop2() {
        let testbit = ite(
            &le(&size, &const_usize(31)),
            &add(&mul(&size, &const_usize(8)), &const_usize(7)),
            &const_usize(257),
        );
        let res_1 = or(
            &value,
            &sub(&const_usize(2 ^ 256), &shl(&const_usize(1), &testbit)),
        );
        let res_2 = and(
            &value,
            &sub(&shl(&const_usize(1), &testbit), &const_usize(1)),
        );
        let final_res = ite(
            &neql(
                &and(&value, &shl(&const_usize(1), &testbit)),
                &const_usize(0),
            ),
            &res_1,
            &res_2,
        );
        res.push(final_res);
        return vec![(res, edge_exec())];
    }
    vec![]
}

pub fn jump_if(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut fallthrough = s.create_succ();
    if let Some((ref target, ref cond)) = fallthrough.pop2() {
        let targets_iter = fallthrough.jump_to(target).into_iter();
        let mut targets = targets_iter
            .flat_map(|t| s.get_jump_info(cond, target, t))
            .collect::<Vec<_>>();
        let fallthrough_cond = eql(cond, &zero());
        if let Some(ft) =
            s.get_jump_info(&fallthrough_cond, &const_usize(fallthrough.pc), fallthrough)
        {
            targets.push(ft);
        }
        return targets;
    }
    vec![]
}

pub fn jump(s: &SeState) -> Vec<(SeState, EdgeType)> {
    let mut res = s.create_succ();
    if let Some(ref target) = res.stack.pop() {
        return res
            .jump_to(target)
            .into_iter()
            .flat_map(|t| s.get_jump_info(&one(), target, t))
            .collect::<Vec<_>>();
    }
    vec![]
}

pub fn arith0(s: &SeState, a: Option<&BVal>) -> Vec<(SeState, EdgeType)> {
    if let Some(v) = a {
        let mut res = s.create_succ();
        res.push(v.clone());
        vec![(res, edge_exec())]
    } else {
        vec![]
    }
}

pub fn arith1<F>(s: &SeState, f: F) -> Vec<(SeState, EdgeType)>
where
    F: Fn(&BVal) -> BVal,
{
    let mut res = s.create_succ();
    if let Some(ref a) = res.stack.pop() {
        res.push(f(a));
        return vec![(res, edge_exec())];
    }
    vec![]
}

pub fn arith2<F>(s: &SeState, f: F) -> Vec<(SeState, EdgeType)>
where
    F: Fn(&BVal, &BVal) -> BVal,
{
    let mut res = s.create_succ();
    if let Some((ref a, ref b)) = res.pop2() {
        res.push(f(a, b));
        return vec![(res, edge_exec())];
    }
    vec![]
}

pub fn arith3<F>(s: &SeState, f: F) -> Vec<(SeState, EdgeType)>
where
    F: Fn(&BVal, &BVal, &BVal) -> BVal,
{
    let mut res = s.create_succ();
    if let Some((ref a, ref b, ref c)) = res.pop3() {
        res.push(f(a, b, c));
        return vec![(res, edge_exec())];
    }
    vec![]
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::bytecode::Instr;
    use crate::test_helpers::generate_test_graph;

    #[test]
    fn swap() {
        let ins = vec![
            Instr::IPush(vec![0xfa, 0x11, 0xfa, 0x22]), //value
            Instr::IPush(vec![0x42, 0x43, 0x44, 0x45]), //value
            Instr::IPush(vec![0xaa, 0xbb, 0xcc, 0xdd]), //value
            Instr::ISwap(2),
        ];

        let g = generate_test_graph(ins);

        let state = &g.get_state_by_id(5);
        assert_eq!(0xaabbccdd, FVal::as_usize(&state.stack[0]).unwrap());
        assert_eq!(0xfa11fa22, FVal::as_usize(&state.stack[2]).unwrap());
    }

    // just check for no panic
    #[test]
    fn jump_at_end() {
        let ins = vec![
            Instr::IPush(vec![0x5]),
            Instr::IJump,
            Instr::IJumpDest,
            Instr::IStop,
            Instr::IJumpDest,
            Instr::IPush(vec![0x3]),
            Instr::IJump,
        ];
        let _g = generate_test_graph(ins);
        assert!(true);
    }

    #[test]
    fn byte_at_test() {
        let ins = vec![
            Instr::IPush(vec![0x41, 0x41, 0x41, 0x41]), // out size
            Instr::IPush(vec![0x00]),                   // out offset
            Instr::IByte,
        ];
        let g = generate_test_graph(ins);

        let state = &g.get_state_by_id(4);
        assert_eq!(FVal::as_usize(&state.stack[0]).unwrap(), 0x41);
    }

    #[test]
    fn dup_test() {
        let ins = vec![
            Instr::IPush(vec![0x01]),
            Instr::IPush(vec![0x02]),
            Instr::IPush(vec![0x03]),
            Instr::IDup(1),
            Instr::IDup(4),
        ];

        let g = generate_test_graph(ins);
        let state = &g.get_state_by_id(5);
        assert_eq!(const_usize(0x03), state.stack[3]);
        let state = &g.get_state_by_id(6);
        assert_eq!(const_usize(0x01), state.stack[4]);
    }
}
