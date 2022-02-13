use std::collections::BTreeMap;
use sylt_common::TyID;
use sylt_parser::{Identifier, Span};

#[derive(Debug, Clone)]
pub enum Type {
    Unknown,

    #[allow(dead_code)]
    Ty,
    #[allow(dead_code)]
    Invalid,

    Void,
    Nil,
    Int,
    Float,
    Bool,
    Str,
    Tuple(Vec<TyID>),
    List(TyID),
    Set(TyID),
    Dict(TyID, TyID),
    Function(Vec<TyID>, TyID),
    Blob(Identifier, BTreeMap<String, (Span, TyID)>, Vec<TyID>),
    Enum(Identifier, BTreeMap<String, (Span, TyID)>, Vec<TyID>),
}
