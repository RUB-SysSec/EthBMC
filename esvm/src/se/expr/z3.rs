use std::{
    collections::hash_map::DefaultHasher,
    error::Error,
    fs::File,
    hash::{Hash, Hasher},
    io::{prelude::*, BufReader, Write},
    process::{Child, Command, Stdio},
    sync::mpsc::{channel, Receiver},
    thread,
    time::Duration,
};

use regex::Regex;

use crate::se::{
    expr::{
        bval::{const256, BVal},
        solver::Solver,
    },
    symbolic_analysis::CONFIG,
};

lazy_static! {
    static ref GET_VALUE_RE: Regex =
        Regex::new(r"\(\((?P<expr>(.*)) \(_ bv(?P<value>([0-9]*)) (256|8)\)\)\)").unwrap();
}

#[derive(Debug)]
pub struct Z3Instance {
    process: Child,
    receiver: Receiver<String>,
    current_input: String,
    timeout: usize,
    warnings: bool,
    dump: bool,

    values_as_dec: bool,
}

// dropping causes the process to stick around, since Child does not implement the drop trait
// see: https://doc.rust-lang.org/std/process/struct.Child.html
impl Drop for Z3Instance {
    fn drop(&mut self) {
        self.exit();
    }
}

impl Z3Instance {
    pub fn new(timeout: usize) -> Self {
        let timeout = timeout * 1000; // z3 (soft) timeouts operate in milliseconds
        let mut child = match Command::new("z3")
            .args(&["-smt2", &format!("-t:{}", timeout), "-in"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
        {
            Err(why) => panic!("couldn't spawn z3: {}", why.description()),
            Ok(process) => process,
        };

        let (sender, receiver) = channel();
        let reader = BufReader::new(child.stdout.take().unwrap());

        // spawn receiver thread that constantly reads from the underlying process
        // when the process dies, child stdout gets droped which will drop reader which in turn drops the thread
        let _ = thread::spawn(move || {
            reader
                .lines()
                .filter_map(|line| line.ok())
                .for_each(|line| match sender.send(line) {
                    Ok(_) => {}
                    Err(_) => {
                        return;
                    }
                });
        });

        let values_as_dec = false;
        let current_input = String::new();
        let dump = CONFIG.read().unwrap().dump_solver;
        let mut z3 = Z3Instance {
            process: child,
            receiver,
            values_as_dec,
            current_input,
            timeout,
            dump,
            warnings: true,
        };
        z3.set_config();
        z3
    }
}
impl Solver for Z3Instance {
    fn push_formula(&mut self, formula: &str) {
        self.current_input.push_str(&format!("{}\n", formula));
        self.send(formula);
    }

    fn check_sat(&mut self) -> bool {
        self.check()
    }

    fn reset(&mut self) {
        self.send("(reset)");
        self.current_input.clear();
    }

    fn get_value(&mut self, value: &str) -> Option<BVal> {
        self.values_as_dec();
        if !self.check() {
            return None;
        }

        self.send(&format!("(get-value ({}))", value));
        let res = self.recv().unwrap();
        let caps = if let Some(x) = GET_VALUE_RE.captures(&res) {
            x
        } else {
            return None;
        };
        caps.name("value").map(|x| const256(x.as_str()))
    }

    fn get_values(&mut self, values: &[String]) -> Option<Vec<BVal>> {
        self.values_as_dec();

        if !self.check() {
            return None;
        }

        let mut vals = Vec::with_capacity(values.len());
        for value in values {
            self.send(&format!("(get-value ({}))", value));
            let res = self.recv().unwrap();
            let caps = if let Some(x) = GET_VALUE_RE.captures(&res) {
                x
            } else {
                return None;
            };
            vals.push(caps.name("value").map(|x| const256(x.as_str()))?);
        }
        Some(vals)
    }
}

impl Z3Instance {
    fn set_config(&mut self) {
        self.send("(set-logic QF_ABV)");
        self.send("(set-option :global-decls false)");
    }

    // this will reset z3 since we can not control asserts/defs
    #[cfg(test)]
    fn check_formula(&mut self, formula: &str) -> bool {
        self.reset();
        self.current_input.push_str(formula);
        self.send(formula);
        let res = self.check();
        self.reset();
        res
    }

    fn values_as_dec(&mut self) {
        if self.values_as_dec {
            return;
        }
        self.send("(set-option :pp.bv-literals false)");
        self.values_as_dec = true;
    }

    fn send(&mut self, cmd: &str) {
        let process_in = self.process.stdin.as_mut().unwrap();

        let mut input = String::from(cmd);
        input.push_str("\n");
        process_in
            .write_all(input.as_bytes())
            .expect("Could not write to z3 process");
        process_in.flush().expect("Could not flush buffer");
    }

    fn exit(&mut self) {
        self.send("(exit)");
        self.process.wait().expect("Could not close z3 process");
    }

    fn recv(&mut self) -> Result<String, String> {
        let mut res = String::new();

        // provide an initial timeout slightly longer then the query timeout
        let mut timeout = self.timeout + 200;
        let mut first_round = true;
        while let Ok(line) = self
            .receiver
            .recv_timeout(Duration::from_millis(timeout as u64))
        {
            res.push_str(&line.replace("\n", ""));

            // after first round reset so we do not wait forever when we read all the output
            if first_round {
                timeout = 100;
                first_round = false;
            }
        }
        if res.contains("error") {
            return Err(res);
        }
        Ok(res)
    }

    // internal use
    fn check(&mut self) -> bool {
        self.send("(check-sat)");
        if self.dump {
            let mut s = DefaultHasher::new();
            self.current_input.hash(&mut s);
            let f_name = format!("queries/{:x}.smt2", s.finish());
            let mut file = File::create(f_name).unwrap();
            file.write_all(self.current_input.as_bytes()).unwrap();
        }
        let res = match self.recv() {
            Ok(r) => r,
            Err(err) => {
                debug!(
                    "Error in z3 output: {}\nInput: \n{}",
                    err,
                    self.debug_ouput()
                );
                return false;
            }
        };
        // solver timeout handeled as unsat
        if res.contains("unsat") {
            return false;
        }
        if res.contains("sat") {
            return true;
        }
        if res.contains("unknown") {
            if self.warnings {
                // timeout is specified in miliseconds
                warn!("Solver timed out after {} seconds.", self.timeout / 1_000);
                debug!("{}", self.debug_ouput());
            }
            return false;
        }
        debug!("Strange z3 output: {}", res);
        false
    }

    fn debug_ouput(&self) -> String {
        let mut debug_ouput = String::new();

        for (i, line) in self.current_input.lines().enumerate() {
            debug_ouput.push_str(&format!("{}\t{}\n", i, line));
        }
        debug_ouput
    }
}
