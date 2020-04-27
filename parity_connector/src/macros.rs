#[macro_export]
macro_rules! implement_return_struct {
    // capture members as ident and tt see:
    // https://danielkeep.github.io/tlborm/book/mbe-min-captures-and-expansion-redux.html
    (
        $(#[$struct_attr:meta])*
        pub struct $name:ident {
            $( $field_name:ident: $type:tt, )+
        }
    ) => {
        #[derive(Deserialize, Debug)]
        $(#[$struct_attr])*
        pub struct $name {
            $( $field_name: $type, )+
        }

        impl $name {
            $( impl_getter!($field_name : $type); )+
        }
    };
    (
        $(#[$struct_attr:meta])*
        struct $name:ident {
            $( $field_name:ident: $type:tt, )+
        }
    ) => {
        #[derive(Deserialize, Debug)]
        $(#[$struct_attr])*
        struct $name {
            $( $field_name: $type, )+
        }

        impl $name {
            $( impl_getter!(pub $field_name : $type); )+
        }
    };
}

#[allow(unused_macros)] // because reasons
macro_rules! impl_getter {
    // SerializableU256 to U256
    (pub $field_name:ident : SerializableU256) => {
        pub fn $field_name(&self) -> &U256 {
            self.$field_name.as_ref()
        }
    };
    ($field_name:ident : SerializableU256) => {
        pub fn $field_name(&self) -> &U256 {
            self.$field_name.as_ref()
        }
    };
    // fallback
    ($field_name:ident : $type:ty) => {
        pub fn $field_name(&self) -> &$type {
            &self.$field_name
        }
    };
    (pub $field_name:ident : $type:ty) => {
        pub fn $field_name(&self) -> &$type {
            &self.$field_name
        }
    };
}
