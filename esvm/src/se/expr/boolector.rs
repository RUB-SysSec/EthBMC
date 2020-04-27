use std::{
    collections::hash_map::DefaultHasher,
    fs::File,
    hash::{Hash, Hasher},
    io::Write,
};

use regex::Regex;
use subprocess::{Exec, Redirection};

use crate::se::{
    expr::{
        bval::{const256, BVal},
        solver::Solver,
    },
    symbolic_analysis::CONFIG,
};

lazy_static! {
    static ref VALUE_RE: Regex =
        Regex::new(r"\(\((?P<expr>(.*)) \(_ bv(?P<value>([0-9]*)) (256|8)\)\)\)").unwrap();
}

pub struct BoolectorInstance {
    timeout: usize,
    input_buffer: String,
    dump: bool,
}

impl BoolectorInstance {
    pub fn new(timeout: usize) -> Self {
        let input_buffer = String::from("(set-logic QF_ABV)\n");
        let timeout = timeout / 1_000; // boolector uses seconds
        let dump = CONFIG.read().unwrap().dump_solver;
        Self {
            timeout,
            input_buffer,
            dump,
        }
    }

    fn communicate(&self) -> String {
        Exec::cmd("boolector")
            .arg(format!("--time={}", self.timeout).as_str())
            .arg("-m")
            .arg("-d")
            .stdin(self.input_buffer.as_str())
            .stderr(Redirection::Merge)
            .stdout(Redirection::Pipe)
            .capture()
            .unwrap()
            .stdout_str()
    }

    fn check(&self, output: &str) -> bool {
        if output.contains("boolector") {
            debug!(
                "Boolector error: {}, for input: {}",
                output, self.input_buffer
            );
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
                "Strange boolector output: {}, for input: {}",
                output, self.input_buffer
            );
            false
        }
    }
}

impl Solver for BoolectorInstance {
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
        caps.name("value").map(|x| const256(x.as_str()))
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
            result.push(cap.name("value").map(|x| const256(x.as_str()))?);
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
    fn boolector_general_test() {
        let test_formula = String::from(
            "(declare-const a (_ BitVec 256))
        (declare-const b (_ BitVec 8))
        (assert (= a (_ bv10 256)))
        (assert (= b ((_ extract 7 0) a) ))",
        );
        let mut boolector = BoolectorInstance::new(TEST_TIMEOUT);
        for line in test_formula.lines() {
            boolector.push_formula(line);
        }
        assert_eq!(true, boolector.check_sat());
    }

    #[test]
    fn boolector_general_false_test() {
        let f_false = String::from(
            "(declare-const a (_ BitVec 256))
        (declare-const b (_ BitVec 256))
        (assert (= a (_ bv10 256)))
        (assert (= b (_ bv11 256)))
        (assert (= a b))",
        );
        let mut boolector = BoolectorInstance::new(TEST_TIMEOUT);
        for line in f_false.lines() {
            boolector.push_formula(line);
        }
        assert_eq!(false, boolector.check_sat());
    }

    #[test]
    fn boolector_get_value() {
        let mut boolector = BoolectorInstance::new(TEST_TIMEOUT);

        boolector.push_formula(&String::from("(declare-const a (_ BitVec 256))"));
        boolector.push_formula(&String::from("(assert (= a (_ bv10 256)))"));
        assert_eq!(Some(const_usize(10)), boolector.get_value("a"));
    }

    #[test]
    fn boolector_get_values() {
        let mut boolector = BoolectorInstance::new(TEST_TIMEOUT);

        boolector.push_formula(&String::from("(declare-const a (_ BitVec 256))"));
        boolector.push_formula(&String::from("(assert (= a (_ bv10 256)))"));
        boolector.push_formula(&String::from("(declare-const b (_ BitVec 256))"));
        boolector.push_formula(&String::from("(assert (= b (_ bv11 256)))"));
        assert_eq!(
            Some(vec!(const_usize(10), const_usize(11))),
            boolector.get_values(&["a".to_owned(), String::from("b")])
        );
    }
}
