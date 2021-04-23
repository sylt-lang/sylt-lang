use lingon::random::{Uniform, Distribute};
use sylt_macro::{sylt_link, sylt_link_gen};
use crate::*;

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    random
    [] -> Type::Float => {
        Ok(Value::Float(Uniform.sample().into()))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    random_2 as rand
    [] -> Type::Float => {
        Ok(Value::Float(Uniform.sample().into()))
    },
);

sylt_link_gen!("sylt::lingon_sylt");
