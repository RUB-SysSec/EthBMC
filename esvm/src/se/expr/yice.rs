use std::{
    collections::hash_map::DefaultHasher,
    fs::File,
    hash::{Hash, Hasher},
    io::Write,
};

use regex::Regex;
use subprocess::{Exec, Redirection};
use uint::U256;

use crate::se::{
    expr::{
        bval::{const_u256, BVal},
        solver::Solver,
    },
    symbolic_analysis::CONFIG,
};

lazy_static! {
    static ref VALUE_RE: Regex =
        // yice only supports binary encoding for return values
        Regex::new(r"\(\((?P<expr>(.*))\n?\s*#b(?P<value>([01]*))\)\)").unwrap();
}

pub struct YiceInstance {
    timeout: usize,
    input_buffer: String,
    dump: bool,
}

fn parse_binary_str(input: &str) -> U256 {
    let reverse: Vec<char> = input.chars().collect();
    debug_assert!(reverse.len() % 8 == 0);
    let mut result: [u8; 32] = [0; 32];
    for (i, chunk) in reverse.as_slice().chunks(8).rev().enumerate() {
        let mut byte: u8 = 0;
        for (i, c) in chunk.iter().rev().enumerate() {
            match c {
                '0' => {}
                '1' => byte ^= 1 << i,
                _ => unreachable!(),
            }
        }
        result[31 - i] = byte;
    }
    result.into()
}

impl YiceInstance {
    pub fn new(timeout: usize) -> Self {
        let input_buffer = String::from("(set-logic QF_ABV)\n");
        let timeout = timeout / 1_000; // yice uses seconds
        let dump = CONFIG.read().unwrap().dump_solver;
        Self {
            timeout,
            input_buffer,
            dump,
        }
    }

    fn communicate(&self) -> String {
        Exec::cmd("yices-smt2")
            .arg(format!("--timeout={}", self.timeout).as_str())
            .stdin(self.input_buffer.as_str())
            .stderr(Redirection::Merge)
            .stdout(Redirection::Pipe)
            .capture()
            .unwrap()
            .stdout_str()
    }

    fn check(&self, output: &str) -> bool {
        if output.contains("yice") {
            debug!("Yice error: {}, for input: {}", output, self.input_buffer);
            false
        } else if output.contains("unsat") {
            false
        } else if output.contains("sat") {
            true
        } else if output.contains("unknown") {
            warn!("Solver timed out after {} seconds", self.timeout);
            false
        } else {
            debug!(
                "Strange yice output: {}, for input: {}",
                output, self.input_buffer
            );
            false
        }
    }
}

impl Solver for YiceInstance {
    fn push_formula(&mut self, formula: &str) {
        self.input_buffer.push_str(&format!("{}\n", formula));
    }

    fn check_sat(&mut self) -> bool {
        self.input_buffer.push_str("(check-sat)\n");
        self.check(&self.communicate())
    }

    fn get_value(&mut self, value: &str) -> Option<BVal> {
        self.input_buffer.push_str("(check-sat)\n");
        self.input_buffer
            .push_str(&format!("(get-value ({}))\n", value));
        let output = self.communicate();

        if !self.check(&output) {
            return None;
        }

        let caps = if let Some(x) = VALUE_RE.captures(&output) {
            x
        } else {
            return None;
        };
        caps.name("value")
            .map(|x| const_u256(parse_binary_str(x.as_str())))
    }

    fn get_values(&mut self, values: &[String]) -> Option<Vec<BVal>> {
        self.input_buffer.push_str("(check-sat)\n");
        for value in values {
            self.input_buffer
                .push_str(&format!("(get-value ({}))\n", value));
        }
        let output = self.communicate();

        if !self.check(&output) {
            return None;
        }

        let mut result = Vec::with_capacity(values.len());
        for cap in VALUE_RE.captures_iter(&output) {
            result.push(
                cap.name("value")
                    .map(|x| const_u256(parse_binary_str(x.as_str())))?,
            );
        }

        Some(result)
    }

    fn reset(&mut self) {
        if self.dump {
            let mut s = DefaultHasher::new();
            self.input_buffer.hash(&mut s);
            let f_name = format!("queries/{:x}.smt2", s.finish());
            let mut file = File::create(f_name).unwrap();
            file.write_all(self.input_buffer.as_bytes()).unwrap();
        }

        self.input_buffer.clear();
        self.input_buffer.push_str("(set-logic QF_ABV)\n")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::se::expr::bval::const_usize;

    const TEST_TIMEOUT: usize = 120;

    #[test]
    fn yice_general_test() {
        let test_formula = String::from(
            "(declare-const a (_ BitVec 256))
        (declare-const b (_ BitVec 8))
        (assert (= a (_ bv10 256)))
        (assert (= b ((_ extract 7 0) a) ))",
        );
        let mut yice = YiceInstance::new(TEST_TIMEOUT);
        for line in test_formula.lines() {
            yice.push_formula(line);
        }
        assert_eq!(true, yice.check_sat());
    }

    #[test]
    fn yice_general_false_test() {
        let f_false = String::from(
            "(declare-const a (_ BitVec 256))
        (declare-const b (_ BitVec 256))
        (assert (= a (_ bv10 256)))
        (assert (= b (_ bv11 256)))
        (assert (= a b))",
        );
        let mut yice = YiceInstance::new(TEST_TIMEOUT);
        for line in f_false.lines() {
            yice.push_formula(line);
        }
        assert_eq!(false, yice.check_sat());
    }

    #[test]
    fn yice_get_value() {
        let mut yice = YiceInstance::new(TEST_TIMEOUT);

        yice.push_formula(&String::from("(declare-const a (_ BitVec 256))"));
        yice.push_formula(&String::from("(assert (= a (_ bv10 256)))"));
        assert_eq!(Some(const_usize(10)), yice.get_value("a"));
    }

    #[test]
    fn yice_get_value_8() {
        let mut yice = YiceInstance::new(TEST_TIMEOUT);

        yice.push_formula(&String::from("(declare-const a (_ BitVec 8))"));
        yice.push_formula(&String::from("(assert (= a (_ bv10 8)))"));
        assert_eq!(Some(const_usize(10)), yice.get_value("a"));
    }

    #[test]
    fn yice_get_values() {
        let mut yice = YiceInstance::new(TEST_TIMEOUT);

        yice.push_formula(&String::from("(declare-const a (_ BitVec 256))"));
        yice.push_formula(&String::from("(assert (= a (_ bv10 256)))"));
        yice.push_formula(&String::from("(declare-const b (_ BitVec 256))"));
        yice.push_formula(&String::from("(assert (= b (_ bv11 256)))"));
        assert_eq!(
            Some(vec!(const_usize(10), const_usize(11))),
            yice.get_values(&["a".to_owned(), String::from("b")])
        );
    }
}
