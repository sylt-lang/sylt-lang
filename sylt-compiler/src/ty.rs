use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub enum Type {
    Unknown,

    #[allow(dead_code)]
    Ty,
    #[allow(dead_code)]
    Invalid,

    Void,
    Int,
    Float,
    Bool,
    Str,
    Tuple(Vec<usize>),
    List(usize),
    Set(usize),
    Dict(usize, usize),
    Function(Vec<usize>, usize),
    Blob(String, BTreeMap<String, usize>),
    Enum(String, BTreeMap<String, usize>),
}
