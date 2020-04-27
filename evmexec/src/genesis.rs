use std::{
    collections::HashMap,
    io::{Seek, SeekFrom, Write},
};

use ethereum_newtypes::{wu256_from_usize_str, Address, Bytes, Hash, WU256};
use log::debug;
use serde::{Deserialize, Deserializer};
use serde_json::Value;
use tempfile::{Builder, NamedTempFile};

use crate::Error;

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Config {
    pub eip150_block: u32,
    pub eip155_block: u32,
    pub eip158_block: u32,
    pub homestead_block: u32,
    pub dao_fork_block: u32,
    pub byzantium_block: u32,
    pub constantinople_block: u32,
}

#[derive(Debug, PartialEq, Deserialize, Serialize)]
pub struct Account {
    #[serde(deserialize_with = "wu256_from_usize_str")]
    pub balance: WU256,
    pub code: Bytes,
    pub nonce: WU256,
    #[serde(deserialize_with = "ok_or_default")]
    pub storage: HashMap<WU256, WU256>,
}

fn ok_or_default<'de, D>(deserializer: D) -> Result<HashMap<WU256, WU256>, D::Error>
where
    D: Deserializer<'de>,
{
    let v: Value = Deserialize::deserialize(deserializer)?;
    Ok(HashMap::deserialize(v).unwrap_or(HashMap::new()))
}

impl Account {
    pub fn new(
        balance: WU256,
        code: Option<Bytes>,
        nonce: WU256,
        storage: Option<HashMap<WU256, WU256>>,
    ) -> Self {
        let code = if let Some(c) = code { c } else { vec![].into() };
        let storage = if let Some(s) = storage {
            s
        } else {
            HashMap::new()
        };
        Self {
            balance,
            code,
            nonce,
            storage,
        }
    }
}

impl Config {
    pub fn byzantium() -> Self {
        let eip150_block = 0;
        let eip158_block = 0;
        let eip155_block = 0;
        let homestead_block = 0;
        let dao_fork_block = 0;
        let byzantium_block = 2000;
        let constantinople_block = 2000;

        Self {
            eip150_block,
            eip155_block,
            eip158_block,
            homestead_block,
            dao_fork_block,
            byzantium_block,
            constantinople_block,
        }
    }
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Genesis {
    pub difficulty: WU256,
    pub coinbase: Address,
    pub timestamp: WU256,
    pub number: WU256,
    pub gas_limit: WU256,
    pub extra_data: WU256,
    pub mixhash: Hash,
    pub parent_hash: Hash,
    pub nonce: WU256,
    pub alloc: HashMap<Address, Account>,
    pub config: Config,
}

impl Default for Genesis {
    fn default() -> Self {
        Self::new()
    }
}

impl Genesis {
    pub fn new() -> Self {
        let coinbase = Address::new(0.into());
        let gas_limit = 0x003D_0900.into();
        let timestamp = 0x0.into();
        let difficulty = 0x1.into();
        let number = 0x0.into();
        let config = Config::byzantium();
        let extra_data = 0.into();
        let mixhash = 0.into();
        let parent_hash = 0.into();
        let nonce = 0.into();
        let alloc = HashMap::new();

        Self {
            coinbase,
            gas_limit,
            timestamp,
            difficulty,
            number,
            extra_data,
            mixhash,
            parent_hash,
            nonce,
            alloc,
            config,
        }
    }

    /// create a temporary file for holding the configuration
    pub fn export(&self) -> Result<NamedTempFile, Error> {
        let mut named_tempfile = Builder::new()
            .prefix("genesis-state-")
            .suffix(".json")
            .rand_bytes(32)
            .tempfile()?;

        if cfg!(feature = "verbose") {
            debug!(
                "Generated new genesis file:\n{}",
                serde_json::to_string(&self)?
            );
        }

        write!(named_tempfile, "{}", serde_json::to_string(&self)?)?;
        named_tempfile.seek(SeekFrom::Start(0))?;

        Ok(named_tempfile)
    }

    pub fn add_account(&mut self, addr: Address, acc: Account) -> Option<Account> {
        self.alloc.insert(addr, acc)
    }

    pub fn update_account_storage(
        &mut self,
        account: &Address,
        addr: WU256,
        value: WU256,
    ) -> Result<(), crate::Error> {
        let account = self
            .alloc
            .get_mut(account)
            .ok_or_else(|| crate::Error::custom("Trying to update unknown accout".to_string()))?;
        account.storage.insert(addr, value);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{fs::File, io::Read};

    #[test]
    fn create_simple_genesis_() {
        let g = Genesis::new();
        let mut f = g.export().expect("Could not export genesis file");
        let mut s = String::new();
        f.read_to_string(&mut s)
            .expect("Could not read into Buffer");

        let correct = "{\"difficulty\":\"0x01\",\"coinbase\":\"0x0000000000000000000000000000000000000000\",\"timestamp\":\"0x00\",\"number\":\"0x00\",\"gasLimit\":\"0x3d0900\",\"extraData\":\"0x00\",\"mixhash\":\"0x0000000000000000000000000000000000000000000000000000000000000000\",\"parentHash\":\"0x0000000000000000000000000000000000000000000000000000000000000000\",\"nonce\":\"0x00\",\"alloc\":{},\"config\":{\"eip150Block\":0,\"eip155Block\":0,\"eip158Block\":0,\"homesteadBlock\":0,\"daoForkBlock\":0,\"byzantiumBlock\":2000,\"constantinopleBlock\":2000}}";

        assert_eq!(s, correct);
    }

    #[test]
    fn read_temp_file() {
        let g = Genesis::new();
        let fpath = g
            .export()
            .expect("Could not export genesis file")
            .into_temp_path();
        let mut f = File::open(fpath).expect("Could not open tmp file");
        let mut s = String::new();
        f.read_to_string(&mut s)
            .expect("Could not read into Buffer");

        let correct = "{\"difficulty\":\"0x01\",\"coinbase\":\"0x0000000000000000000000000000000000000000\",\"timestamp\":\"0x00\",\"number\":\"0x00\",\"gasLimit\":\"0x3d0900\",\"extraData\":\"0x00\",\"mixhash\":\"0x0000000000000000000000000000000000000000000000000000000000000000\",\"parentHash\":\"0x0000000000000000000000000000000000000000000000000000000000000000\",\"nonce\":\"0x00\",\"alloc\":{},\"config\":{\"eip150Block\":0,\"eip155Block\":0,\"eip158Block\":0,\"homesteadBlock\":0,\"daoForkBlock\":0,\"byzantiumBlock\":2000,\"constantinopleBlock\":2000}}";

        assert_eq!(s, correct);
    }

    #[test]
    fn deseriaize_accounts() {
        let states: HashMap<Address, Account> = serde_json::from_str(&STATE_EXAMPLE).unwrap();
        let mut correct = HashMap::new();

        let acc_1 = Account {
            balance: 0.into(),
            nonce : 1.into(),
            code: Bytes::from_hex_str("60806040526004361061004b5763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416637c52e3258114610050578063e9ca826c14610080575b600080fd5b34801561005c57600080fd5b5061007e73ffffffffffffffffffffffffffffffffffffffff60043516610095565b005b34801561008c57600080fd5b5061007e610145565b60005473ffffffffffffffffffffffffffffffffffffffff1633146100b657fe5b600154604080517f338ccd7800000000000000000000000000000000000000000000000000000000815273ffffffffffffffffffffffffffffffffffffffff84811660048301529151919092169163338ccd7891602480830192600092919082900301818387803b15801561012a57600080fd5b505af115801561013e573d6000803e3d6000fd5b5050505050565b6000805473ffffffffffffffffffffffffffffffffffffffff1916331790555600a165627a7a72305820b376cbf41ad45cba2c20890893f93f24efe850bf7eaf35fd12a0474576b4ac2d0029").unwrap(),
            storage: HashMap::new(),
        };
        correct.insert("0ad62f08b3b9f0ecc7251befbeff80c9bb488fe9".into(), acc_1);

        let acc_2 = Account {
            balance: 16.into(),
            nonce: 1.into(),
            code: vec![].into(),
            storage: HashMap::new(),
        };
        correct.insert("0dfa72de72f96cf5b127b070e90d68ec9710797c".into(), acc_2);

        let acc_3 = Account {
            balance: 1048576.into(),
            nonce: 1.into(),
            code: Bytes::from_hex_str("606060405260043610603e5763ffffffff7c0100000000000000000000000000000000000000000000000000000000600035041663338ccd7881146043575b600080fd5b3415604d57600080fd5b606c73ffffffffffffffffffffffffffffffffffffffff60043516606e565b005b6000543373ffffffffffffffffffffffffffffffffffffffff908116911614609257fe5b8073ffffffffffffffffffffffffffffffffffffffff166108fc3073ffffffffffffffffffffffffffffffffffffffff16319081150290604051600060405180830381858888f19350505050151560e857600080fd5b505600a165627a7a72305820d94e263975863b2024dc4bfaba0287941709bc576381ae567f9683d8fc2052940029").unwrap(),
            storage: hashmap!(
                0.into() => "940ad62f08b3b9f0ecc7251befbeff80c9bb488fe9".into(),
            ),
        };
        correct.insert("86c249452ee469d839942e05b8492dbb9f9c70ac".into(), acc_3);

        assert_eq!(correct, states);
    }

    const STATE_EXAMPLE: &'static str = r#"{
    "0ad62f08b3b9f0ecc7251befbeff80c9bb488fe9": {
        "balance": "0",
        "nonce": 1,
        "root": "0fbf6822b39f67831c32e34b61de28604106292b61d87acc5d74a987f320ff2a",
        "codeHash": "870095b70f331f4ba54e5fba6ca45ae54a80e81cd9d279105af5be8a0fd1a2ca",
        "code": "60806040526004361061004b5763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416637c52e3258114610050578063e9ca826c14610080575b600080fd5b34801561005c57600080fd5b5061007e73ffffffffffffffffffffffffffffffffffffffff60043516610095565b005b34801561008c57600080fd5b5061007e610145565b60005473ffffffffffffffffffffffffffffffffffffffff1633146100b657fe5b600154604080517f338ccd7800000000000000000000000000000000000000000000000000000000815273ffffffffffffffffffffffffffffffffffffffff84811660048301529151919092169163338ccd7891602480830192600092919082900301818387803b15801561012a57600080fd5b505af115801561013e573d6000803e3d6000fd5b5050505050565b6000805473ffffffffffffffffffffffffffffffffffffffff1916331790555600a165627a7a72305820b376cbf41ad45cba2c20890893f93f24efe850bf7eaf35fd12a0474576b4ac2d0029",
        "storage": {}
    },
    "0dfa72de72f96cf5b127b070e90d68ec9710797c": {
        "balance": "16",
        "nonce": 1,
        "root": "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421",
        "codeHash": "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
        "code": "",
        "storage": {}
    },
    "86c249452ee469d839942e05b8492dbb9f9c70ac": {
        "balance": "1048576",
        "nonce": 1,
        "root": "d80f75b929e8c410d0edeba934c1b41b338a362cd75b92c2dcbb8d0a0cf55961",
        "codeHash": "097398617ee709f79e1f68999b9371d7bf2dea11f988ac67213b3bd3f607d9d8",
        "code": "606060405260043610603e5763ffffffff7c0100000000000000000000000000000000000000000000000000000000600035041663338ccd7881146043575b600080fd5b3415604d57600080fd5b606c73ffffffffffffffffffffffffffffffffffffffff60043516606e565b005b6000543373ffffffffffffffffffffffffffffffffffffffff908116911614609257fe5b8073ffffffffffffffffffffffffffffffffffffffff166108fc3073ffffffffffffffffffffffffffffffffffffffff16319081150290604051600060405180830381858888f19350505050151560e857600080fd5b505600a165627a7a72305820d94e263975863b2024dc4bfaba0287941709bc576381ae567f9683d8fc2052940029",
        "storage": {
            "0000000000000000000000000000000000000000000000000000000000000000": "940ad62f08b3b9f0ecc7251befbeff80c9bb488fe9"
        }
    }
}"#;

}
