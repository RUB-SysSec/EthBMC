extern crate ethereum_newtypes;
extern crate hexdecode;
extern crate regex;
extern crate serde;
extern crate serde_json;
extern crate subprocess;
extern crate tempfile;
extern crate uint;

#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate serde_derive;
#[macro_use]
#[cfg(test)]
extern crate maplit;

pub mod evm;
pub mod evmtrace;
pub mod genesis;

use std::io;

macro_rules! impl_error {
    (
        $(#[$struct_attr:meta])*
        pub enum Error {
            $( $enum_variant_name:ident($error_type:path), )+
        }
    ) => {
        // meta attributes
        $(#[$struct_attr])*
        // enum definition
        pub enum Error {
            $( $enum_variant_name($error_type), )+
        }

        // impl error conversion for each type
        $(
            impl From<$error_type> for Error {
                fn from(error: $error_type) -> Self {
                    Error::$enum_variant_name(error)
                }
            }
        )+
    };
}

impl_error!(
    #[derive(Debug)]
    pub enum Error {
        Io(io::Error),
        SerdeJson(serde_json::Error),
        Custom(String),
    }
);

impl Error {
    fn custom(s: String) -> Self {
        Error::Custom(s)
    }
}
