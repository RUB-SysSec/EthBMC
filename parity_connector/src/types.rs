use ethereum_newtypes::WU256;
use serde::ser::{Serialize, Serializer};

/// An enum to select the block to fetch from the blockchain
#[derive(Clone, Copy, Debug, Deserialize)]
pub enum BlockSelector {
    Earliest,
    Latest,
    Pending,
    Specific(usize),
}

impl Serialize for BlockSelector {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            BlockSelector::Earliest => serializer.serialize_str("earliest"),
            BlockSelector::Latest => serializer.serialize_str("latest"),
            BlockSelector::Pending => serializer.serialize_str("pending"),
            BlockSelector::Specific(u) => serializer.serialize_str(&format!("0x{:x}", u)),
        }
    }
}

/// A rust representation of an ethereum block, reduced to the fields used by ethAEG
implement_return_struct!(
    #[serde(rename_all = "camelCase")]
    pub struct Block {
        gas_limit: WU256,
        number: WU256,
        miner: WU256,
        hash: WU256,
        timestamp: WU256,
        difficulty: WU256,
    }
);

/// A rust representation of an account storaage
#[derive(Debug, Serialize, Deserialize)]
pub struct Storage(pub Vec<Vec<WU256>>);
