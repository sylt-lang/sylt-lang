use std::collections::HashMap;

use sylt_common::{Error, FileOrLib};
use sylt_parser::{Span, AST};

use crate::NamespaceID;

type ResolveResult<T> = Result<T, Vec<Error>>;

struct Var {
    id: usize,
    definition: Span,
    usage: Vec<Span>,
}

type Ref = usize;
type Namespace = usize;

pub enum BinOp {
    // Comp
    Equals,
    NotEquals,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    // Misc
    In,
    AssertEq,
    // Mul
    Add,
    Sub,
    Mul,
    Div,
    // Bool
    And,
    Or,
}

pub enum UniOp {
    Neg,
    NotEquals,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    In,
    Add,
    Sub,
    Mul,
    Div,
}

pub enum Collection {
    Tuple,
    List,
    Set,
    Dict,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfBranch {
    pub condition: Option<Expression>,
    pub body: Vec<Statement>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CaseBranch {
    pub pattern: Identifier,
    pub variable: Option<Identifier>,
    pub body: Vec<Statement>,
}

pub enum Expression {
    Read {
        var: Ref,
        span: Span,
    },
    Variant {
        variant: String,
        span: Span,
    },
    Call {
        value: Expression,
        args: Vec<(Expression, Span)>,
        span: Span,
    },
    BlobAccess {
        value: Expression,
        field: String,
        span: Span,
    },

    BinOp {
        a: Expression,
        b: Expression,
        op: BinOp,
        span: Span,
    },
    UniOp {
        a: Expression,
        op: UniOp,
        span: Span,
    },

    If {
        branches: Vec<IfBranch>,
        span: Span,
    },
    Case {
        to_match: Box<Expression>,
        branches: Vec<CaseBranch>,
        fall_through: Option<Vec<Statement>>,
    },
    Function {
        name: String,
        params: Vec<(String, Span, Type)>,
        ret: Type,

        body: Vec<Statement>,
        pure: bool,
    },
    Blob {
        blob: TypeAssignable,
        fields: Vec<(String, Expression)>, // Keep calling order
    },

    Collection {
        collection: Collection,
        values: Vec<Expression>,
        span: Span,
    },

    Float(f64),
    Int(i64),
    Str(String),
    Bool(bool),
    Nil,
}

pub struct Type {
}

pub fn resolve<'a>(tree: &'a AST, namespace_to_file: &HashMap<NamespaceID, FileOrLib>) -> _ {}
