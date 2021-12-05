use crate::typechecker::TyID;
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
    Tuple(Vec<TyID>),
    List(TyID),
    Set(TyID),
    Dict(TyID, TyID),
    Function(Vec<TyID>, TyID),
    Blob(String, BTreeMap<String, TyID>),
    Enum(String, BTreeMap<String, TyID>),
}
