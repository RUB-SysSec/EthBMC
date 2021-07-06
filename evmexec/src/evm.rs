use std::{
    collections::HashMap,
    error::Error,
    io::{self, prelude::*, BufReader, Read},
};

use ethereum_newtypes::{Address, Bytes, Hash, WU256};
use log::debug;
use subprocess::{Exec, Redirection};
use tempfile::TempPath;

use crate::{
    evmtrace::{ContextParser, Instruction, InstructionContext},
    genesis::{Account, Genesis},
};

/// A struct to hold the evm information
pub struct Evm {
    /// The Genesis file for the current execution
    pub genesis: Genesis,
}

#[derive(Debug)]
pub struct EvmInput {
    pub input_data: Bytes,
    pub sender: Address,
    pub receiver: Address,
    pub gas: u32,
    pub value: WU256,
}

impl Default for Evm {
    fn default() -> Self {
        Self::new()
    }
}

impl From<Genesis> for Evm {
    fn from(genesis: Genesis) -> Self {
        Self { genesis }
    }
}

impl Evm {
    pub fn new() -> Self {
        let genesis = Genesis::new();
        Self { genesis }
    }

    pub fn execute(self, input: EvmInput) -> Execution {
        let res = self.execute_input(&input);
        Execution {
            genesis: self.genesis,
            input,
            result: res,
        }
    }

    fn execute_input(&self, input: &EvmInput) -> Result<ExecutionResult, crate::Error> {
        let (output, _path) = self.execute_vm(input)?;
        self.parse_trace(output, input.receiver.clone())
    }

    fn execute_vm(
        &self,
        input: &EvmInput,
    ) -> Result<(BufReader<Box<dyn Read>>, TempPath), crate::Error> {
        let path = self.genesis.export()?.into_temp_path();
        let args = [
            "--prestate",
            path.to_str()
                .ok_or_else(|| io::Error::from(io::ErrorKind::InvalidInput))?,
            "--gas",
            &format!("{}", input.gas),
            "--sender",
            &format!("{:x}", input.sender),
            "--receiver",
            &format!("{:x}", input.receiver),
            "--value",
            &format!("{:x}", input.value),
            "--input",
            &encode(&input.input_data.as_slice(), &Prefixed::No),
            "--json",
            "--dump",
            "run",
        ];

        if cfg!(feature = "verbose") {
            let mut debug = String::new();
            for arg in &args {
                debug.push_str(&format!(" {}", arg));
            }
            debug!("Starting evm with arguments: {:x?}", debug);
        }

        let read_handle = match Exec::cmd("evm")
            .args(&args)
            .stderr(Redirection::Merge) // redirect err output to stdout
            .stream_stdout()
        {
            Err(why) => panic!("couldn't spawn evm: {}", why.description()),
            Ok(process) => process,
        };
        // also return the path object to ensure the temporary file does not get dropped until the
        // output of the exeution is read
        Ok((BufReader::new(Box::new(read_handle)), path))
    }

    fn parse_trace(
        &self,
        mut reader: BufReader<Box<dyn Read>>,
        receiver: Address,
    ) -> Result<ExecutionResult, crate::Error> {
        let mut buf = String::new();
        let mut instructions = Vec::new();
        let mut parser = ContextParser::new(receiver);

        while let Ok(d) = reader.read_line(&mut buf) {
            // end of stream
            if d == 0 {
                break;
            }
            if buf.contains("Fatal") {
                return Err(crate::Error::custom(format!(
                    "Could not fetch evm output: {}",
                    buf,
                )));
            }

            // detect end of the trace
            if buf.contains("output") {
                break;
            } else if let Some(ins) = parser.parse_trace_line(&buf) {
                instructions.push(ins);
            }

            // clear buffer for reuse
            buf.clear();
        }

        let new_state = if cfg!(feature = "verbose") {
            buf.clear();
            while let Ok(d) = reader.read_line(&mut buf) {
                if d == 0 {
                    break;
                }
            }
            let state = serde_json::from_str(&buf);
            if state.is_err() {
                eprintln!("Error during parsing new state:\n{}\n{:?}", buf, state);
            } else {
                debug!("New state after tx execuction:\n{:?}", state)
            }
            state
        } else {
            serde_json::from_reader(reader)
        };

        Ok(ExecutionResult {
            trace: instructions,
            new_state: new_state?,
        })
    }
}

#[derive(Debug)]
pub struct Execution {
    pub genesis: Genesis,
    pub input: EvmInput,
    pub result: Result<ExecutionResult, crate::Error>,
}

impl Execution {
    /// Transforms the Execution into a new evm to be executed
    pub fn into_evm(self) -> Evm {
        Evm {
            genesis: self.genesis,
        }
    }

    /// Updates the environment based on the execution result, returns an error if the execution did not
    /// succeed
    pub fn into_evm_updated(mut self) -> Result<Evm, crate::Error> {
        let res = self.result?;

        for InstructionContext {
            executed_on,
            instruction,
        } in res.trace
        {
            if let Instruction::SStore { addr, value } = instruction {
                self.genesis
                    .update_account_storage(&executed_on, addr, value)?;
            }
        }

        // jsut overwrite, we have to iterate each account anyway
        for (addr, acc_state) in res.new_state.accounts {
            if let Some(acc) = self.genesis.alloc.get_mut(&addr) {
                acc.balance = acc_state.balance;
            } else {
                // new account created during execution
                self.genesis.add_account(addr, acc_state);
            }
        }

        self.genesis
            .alloc
            .get_mut(&self.input.sender)
            .ok_or_else(|| {
                crate::Error::custom("Could not find sender for nonce update".to_string())
            })?
            .nonce += 1.into();

        Ok(Evm {
            genesis: self.genesis,
        })
    }

    pub fn is_err(&self) -> bool {
        self.result.is_err()
    }
}

#[derive(Debug, Deserialize)]
pub struct State {
    root: Hash,
    accounts: HashMap<Address, Account>,
}

#[derive(Debug)]
pub struct ExecutionResult {
    pub trace: Vec<InstructionContext>,
    pub new_state: State,
}

// I just want a named boolean
enum Prefixed {
    Yes,
    No,
}

fn encode(input: &[u8], prefixed: &Prefixed) -> String {
    let mut s = String::with_capacity((input.len() * 2) + 2);
    if let Prefixed::Yes = prefixed {
        s.push_str("0x");
    }
    for byte in input {
        s.push_str(&format!("{:0>2x}", byte));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{evmtrace::Instruction, genesis::Account};
    use ethereum_newtypes::WU256;
    use std::rc::Rc;

    #[test]
    fn vm_execution() {
        let result = execute_test_case()
            .result
            .expect("Detected error while executing evm");
        let writes = vec![InstructionContext {
            executed_on: Rc::new("0x0ad62f08b3b9f0ecc7251befbeff80c9bb488fe9".into()),
            instruction: Instruction::SStore {
                addr: 0.into(),
                value: "0xDFA72DE72F96CF5B127B070E90D68EC9710797C".into(),
            },
        }];
        assert_eq!(writes, result.trace);
    }

    #[test]
    fn vm_update_state() {
        let update = execute_test_case()
            .into_evm_updated()
            .expect("Error while updating file");
        assert_eq!(
            update.genesis.alloc[&"0x0ad62f08b3b9f0ecc7251befbeff80c9bb488fe9".into()].storage
                [&0.into()],
            WU256::from("0xDFA72DE72F96CF5B127B070E90D68EC9710797C"),
        );
    }

    // see https://github.com/ethereum/go-ethereum/issues/17969
    #[test]
    fn deseriaize_malformed_account() {
        let bytes = include_bytes!("../tests/files/corrupted_geth.json");
        let state: State = serde_json::from_slice(bytes).unwrap();
        assert_eq!(
            state.accounts[&WU256::from("0xccfaee7dd7e330960d5241a980415cc94dbe59a4").into()]
                .storage,
            HashMap::new()
        );
    }

    fn execute_test_case() -> Execution {
        let mut evm = Evm::new();

        evm.genesis.add_account(
            "0x0dfa72de72f96cf5b127b070e90d68ec9710797c".into(),
            Account::new(0x10.into(), None, 0x2.into(), None),
        );

        let code = hexdecode::decode("60806040526004361061004b5763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416637c52e3258114610050578063e9ca826c14610080575b600080fd5b34801561005c57600080fd5b5061007e73ffffffffffffffffffffffffffffffffffffffff60043516610095565b005b34801561008c57600080fd5b5061007e610145565b60005473ffffffffffffffffffffffffffffffffffffffff1633146100b657fe5b600154604080517f338ccd7800000000000000000000000000000000000000000000000000000000815273ffffffffffffffffffffffffffffffffffffffff84811660048301529151919092169163338ccd7891602480830192600092919082900301818387803b15801561012a57600080fd5b505af115801561013e573d6000803e3d6000fd5b5050505050565b6000805473ffffffffffffffffffffffffffffffffffffffff1916331790555600a165627a7a72305820b376cbf41ad45cba2c20890893f93f24efe850bf7eaf35fd12a0474576b4ac2d0029".as_bytes()).expect("Could not parse code array");
        evm.genesis.add_account(
            "0x0ad62f08b3b9f0ecc7251befbeff80c9bb488fe9".into(),
            Account::new(
                0x0.into(),
                Some(code.into()),
                0x1.into(),
                Some(hashmap! {
                    0x0.into() => "0xdfa72de72f96cf5b127b070e90d68ec9710797c".into(),
                    0x1.into() => "0x6c249452ee469d839942e05b8492dbb9f9c70ac".into(),
                }),
            ),
        );

        let data = Bytes::from_hex_str("0xe9ca826c000000").expect("Could not parse input");
        let input = EvmInput {
            input_data: data,
            sender: "0xdfa72de72f96cf5b127b070e90d68ec9710797c".into(),
            receiver: "0x0ad62f08b3b9f0ecc7251befbeff80c9bb488fe9".into(),
            gas: 10_000,
            value: 0.into(),
        };
        evm.execute(input)
    }
}
