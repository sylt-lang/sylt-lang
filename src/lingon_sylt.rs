use lingon::random::{Uniform, Distribute};
use sylt_macro::{sylt_link, sylt_link_gen};
use crate::*;

sylt_macro::extern_function!(
    random
    [] -> Type::Float => {
        Ok(Value::Float(Uniform.sample().into()))
    },
);

sylt_macro::extern_function!(
    random_2
    [] -> Type::Float => {
        Ok(Value::Float(Uniform.sample().into()))
    },
);

sylt_link_gen!("sylt::lingon_sylt");
