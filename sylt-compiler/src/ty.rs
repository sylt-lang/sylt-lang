// TODO(ed, er): If you see these during code-review, remind us to remove it.
#![allow(dead_code)]

use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub enum Type {
    Unknown,

    Ty,
    Void,
    Int,
    Float,
    Bool,
    Str,
    Tuple(Vec<usize>),
    // Union(BTreeSet<usize>),
    List(usize),
    Set(usize),
    Dict(usize, usize),
    Function(Vec<usize>, usize),
    Blob(String, BTreeMap<String, usize>),

    Invalid,
}
