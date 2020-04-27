// some helper macros for deriving traits, why is this a thing?
macro_rules! impl_from_trait {
    ($name:ident from $type:ty) => {
        impl From<$type> for $name {
            fn from(value: $type) -> Self {
                Self::new(value.into())
            }
        }
    };
}

macro_rules! impl_visitor_fumc {
    ($func_name:ident for $name:ident from $type:ty) => {
        fn $func_name<E>(self, value: $type) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            Ok($name::from(value))
        }
    }
}

macro_rules! impl_u256_newtype {
    (
        $(#[$struct_attr:meta])*
        pub struct $name:ident(pub U256)
    ) => {

        // definition
        $(#[$struct_attr])*
        #[derive(Debug, Clone, Hash, PartialEq, Eq)]
        pub struct $name(pub U256);


        // from traits
        impl From<U256> for $name {
            fn from(value: U256) -> Self {
                Self::new(value)
            }
        }

        impl<'a> From<&'a U256> for $name {
            fn from(value: &'a U256) -> Self {
                Self::new(value.into())
            }
        }

        impl From<[u8; 32]> for $name {
            fn from(value: [u8; 32]) -> Self {
                Self::new(value.into())
            }
        }

        impl<'a> From<&'a [u8; 32]> for $name {
            fn from(value: &'a [u8; 32]) -> Self {
                Self::new(value.into())
            }
        }

        impl_from_trait!($name from usize);
        impl_from_trait!($name from u64);
        impl_from_trait!($name from u32);
        impl_from_trait!($name from u16);
        impl_from_trait!($name from u8);

        impl_from_trait!($name from isize);
        impl_from_trait!($name from i64);
        impl_from_trait!($name from i32);
        impl_from_trait!($name from i16);
        impl_from_trait!($name from i8);

        impl ::std::ops::AddAssign for $name {
            fn add_assign(&mut self, other: $name) {
                self.0.add_assign(other.0)
            }
        }

        impl ::std::ops::SubAssign for $name {
            fn sub_assign(&mut self, other: $name) {
                self.0.sub_assign(other.0)
            }
        }

        // serialze
        impl Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                serializer.serialize_str(&format!("{:x}", self)) // this assures we use padded value only
            }
        }


        // deserialize
        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> Result<$name, D::Error>
            where
                D: Deserializer<'de>,
            {
                struct ValVisitor;

                impl<'de> Visitor<'de> for ValVisitor {
                    type Value = $name;

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_str("expected hex encoded U256 value.")
                    }

                    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
                    where
                        E: de::Error,
                    {
                        let bytes: Vec<u8> = hexdecode::decode(&value).map_err(|e| de::Error::custom(format!("{:?}", e)))?;

                        let mut val = U256::from(0);
                        for (i, byte) in bytes.iter().enumerate() {
                            if i > 31 {
                                return Err(de::Error::custom(format!("Trying to deserialize bigger then 32 byte value: {:?}", bytes)));
                            }
                            val = (val * U256::from(256)) | (U256::from(255) & U256::from(*byte));
                        }
                        Ok(val.into())
                    }


                    fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
                    where
                        E: de::Error,
                    {
                        self.visit_str(value.as_ref())
                    }

                    impl_visitor_fumc!(visit_u64 for $name from u64);
                    impl_visitor_fumc!(visit_u32 for $name from u32);
                    impl_visitor_fumc!(visit_u16 for $name from u16);
                    impl_visitor_fumc!(visit_u8 for $name from u8);

                    impl_visitor_fumc!(visit_i64 for $name from i64);
                    impl_visitor_fumc!(visit_i32 for $name from i32);
                    impl_visitor_fumc!(visit_i16 for $name from i16);
                    impl_visitor_fumc!(visit_i8 for $name from i8);
                }

                deserializer.deserialize_any(ValVisitor)
            }
        }

    }
}
