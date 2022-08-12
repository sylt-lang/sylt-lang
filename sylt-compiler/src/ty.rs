use std::collections::BTreeMap;
use sylt_common::TyID;
use sylt_parser::Span;

#[derive(Debug, Clone)]
pub enum Purity {
    Pure,
    Impure,
    Undefined,
}

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
    Function(Vec<TyID>, TyID, Purity, Vec<(Vec<TyID>, TyID)>),
    Blob(String, Span, BTreeMap<String, (Span, TyID)>, Vec<TyID>),
    ExternBlob(
        String,
        Span,
        BTreeMap<String, (Span, TyID)>,
        Vec<TyID>,
        usize,
    ),
    Enum(String, Span, BTreeMap<String, (Span, TyID)>, Vec<TyID>),
}
