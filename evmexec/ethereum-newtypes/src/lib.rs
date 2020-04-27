extern crate hexdecode;
extern crate serde;
extern crate uint;

use std::{fmt, io};

use serde::{
    de::{self, Visitor},
    Deserialize, Deserializer, Serialize, Serializer,
};
use uint::U256;

#[macro_use]
mod macros;

/// A wrapper around U256, pads to even length by default
impl_u256_newtype!(pub struct WU256(pub U256));

/// An ethereum account address, pads to 20 byte hex representation by default
impl_u256_newtype!(pub struct Address(pub U256));

/// An ethereum Hash, pads to 32 byte hex representation by default
impl_u256_newtype!(pub struct Hash(pub U256));

/// A wrapper around a byte array
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct Bytes(pub Vec<u8>);

// ====================================
// U256 wrapper
// ====================================
impl WU256 {
    pub fn new(addr: U256) -> Self {
        WU256(addr)
    }
}

/// A utility function for deserializing a wrapper type from a usize str representation
pub fn wu256_from_usize_str<'de, D>(deserializer: D) -> Result<WU256, D::Error>
where
    D: Deserializer<'de>,
{
    let s = String::deserialize(deserializer)?;
    let u: U256 = U256::from_dec_str(&s).map_err(|e| de::Error::custom(format!("{:?}", e)))?;
    Ok(WU256::from(u))
}

// oad to even length
impl fmt::LowerHex for WU256 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let mut padding = 2;
        while padding <= self.0.bits() / 4 && padding < 64 {
            padding += 2;
        }
        write!(
            formatter,
            "0x{:0>padding$}",
            format!("{:x}", self.0),
            padding = padding
        )
    }
}

impl<'a> From<&'a str> for WU256 {
    fn from(value: &'a str) -> Self {
        match hexdecode::decode(value.as_bytes()) {
            Ok(bytes) => {
                let mut val = U256::from(0);
                for (i, byte) in bytes.iter().enumerate() {
                    if i > 31 {
                        panic!("Trying to cast bigger then 32 byte value.");
                    }
                    val = (val * U256::from(256)) | (U256::from(255) & U256::from(*byte));
                }
                val.into()
            }
            Err(e) => panic!("{:?}", e),
        }
    }
}
// ====================================
// U256 wrapper end
// ====================================

// ====================================
// Address
// ====================================
impl Address {
    pub fn new(addr: U256) -> Self {
        assert!(addr.bits() <= 160, "{:x} needs {} bit", addr, addr.bits());
        Address(addr)
    }
}

// we pad to 40 byte addresses by default
impl fmt::LowerHex for Address {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "0x{:0>40}", format!("{:x}", self.0))
    }
}

impl From<WU256> for Address {
    fn from(value: WU256) -> Self {
        Address::new(value.0)
    }
}

impl<'a> From<&'a str> for Address {
    fn from(value: &'a str) -> Self {
        match hexdecode::decode(value.as_bytes()) {
            Ok(bytes) => {
                let mut val = U256::from(0);
                for (i, byte) in bytes.iter().enumerate() {
                    if i > 19 {
                        panic!("Trying to cast bigger then 20 byte value.");
                    }
                    val = (val * U256::from(256)) | (U256::from(255) & U256::from(*byte));
                }
                val.into()
            }
            Err(e) => panic!("{:?}", e),
        }
    }
}
// ====================================
// Address end
// ====================================

// ====================================
// Hash
// ====================================
impl fmt::LowerHex for Hash {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "0x{:0>64}", format!("{:x}", self.0))
    }
}

impl Hash {
    pub fn new(hash: U256) -> Self {
        Hash(hash)
    }
}
// ====================================
// Hash end
// ====================================

// ====================================
// Bytes
// ====================================
impl Bytes {
    pub fn from_hex_str(input: &str) -> Result<Self, io::Error> {
        hexdecode::decode(input.as_bytes()).map(|v: Vec<u8>| v.into())
    }

    pub fn to_hex(&self) -> String {
        let mut s = String::with_capacity((self.0.len() * 2) + 3);
        s.push_str("0x");
        for byte in &self.0 {
            s.push_str(&format!("{:02x}", byte));
        }
        s
    }

    // some common convenience methods
    pub fn as_slice(&self) -> &[u8] {
        self.0.as_slice()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl fmt::Debug for Bytes {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl AsRef<[u8]> for Bytes {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl From<Vec<u8>> for Bytes {
    fn from(value: Vec<u8>) -> Self {
        Bytes(value)
    }
}

impl fmt::Display for Bytes {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_hex())
    }
}

// serialze
impl Serialize for Bytes {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&format!("{}", self))
    }
}

impl<'de> Deserialize<'de> for Bytes {
    fn deserialize<D>(deserializer: D) -> Result<Bytes, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct BytesVisitor;

        impl<'de> Visitor<'de> for BytesVisitor {
            type Value = Bytes;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("Hex encoded byte array.")
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                hexdecode::decode(value.as_bytes())
                    .map(|v: Vec<_>| v.into())
                    .map_err(|e| de::Error::custom(format!("{:?}", e)))
            }
        }

        deserializer.deserialize_str(BytesVisitor)
    }
}
// ====================================
// Bytes end
// ====================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_u256_test() {
        assert_eq!(&format!("{:x}", WU256::from(0x1)), "0x01");
        assert_eq!(&format!("{:x}", WU256::from(0x1111)), "0x1111");
        assert_eq!(&format!("{:x}", WU256::from(0x11111)), "0x011111");
    }

    #[test]
    fn deserialize_test() {
        let value = WU256::from(
            U256::from_dec_str("685244925327644839234826974078916142077323599782").unwrap(),
        );
        let json_string = serde_json::to_string(&value).unwrap();
        let deserialized: WU256 = serde_json::from_str(&json_string).unwrap();
        assert_eq!(
            WU256::from(
                U256::from_dec_str("685244925327644839234826974078916142077323599782").unwrap()
            ),
            deserialized,
        );
    }
}
