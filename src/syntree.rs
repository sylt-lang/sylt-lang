use std::path::PathBuf;
use std::collections::HashMap;
use super::Type as runtimeType;

#[derive(Debug, Copy, Clone)]
struct Span {
    // TODO(ed): Do this more intelligent, so
    // we can show ranges. Maybe even go back
    // to offsets from start of the file.
    line: usize,
}

#[derive(Debug, Clone)]
struct Prog {
    files: Vec<(PathBuf, Module)>,
}

#[derive(Debug, Clone)]
struct Module {
    span: Span,
    statements: Vec<Statement>,
}

#[derive(Debug, Copy, Clone)]
enum VarKind {
    Const,
    Mutable,
    GlobalConst,
    GlobalMutable,
}

#[derive(Debug, Copy, Clone)]
enum AssignmentOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug, Clone)]
enum StatementKind {
    Use {
        file: Identifier,
    },

    Blob {
        name: Identifier,
        fields: HashMap<Identifier, Type>,
    },

    Print {
        expr: Expression,
    },

    Assignment {
        target: Assignable,
        kind: AssignmentOp,
        value: Expression,
    },

    Definition {
        ident: Identifier,
        value: Expression,
        kind: VarKind,
    },

    If {
        condition: Expression,
        pass: Vec<Statement>,
        fail: Vec<Statement>,
    },

    Loop {
        condition: Expression,
        body: Vec<Statement>,
    },

    Ret {
        value: Option<Expression>,
    },

    Block {
        statements: Vec<Statement>,
    },

    Assert {
        expression: Expression,
    },

    StatementExpression {
        value: Expression,
    },
}

#[derive(Debug, Clone)]
struct Statement {
    span: Span,
    kind: StatementKind,
}

#[derive(Debug, Clone)]
struct Identifier {
    span: Span,
    name: String,
}

#[derive(Debug, Clone)]
enum AssignableKind {
    Identifier(Identifier),
    Access(Identifier),
    Index(Expression),
}

#[derive(Debug, Clone)]
struct Assignable {
    span: Span,
    expression: Vec<AssignableKind>,
}

#[derive(Debug, Clone)]
enum ExpressionKind {
    Increment(Assignable),
    Decrement(Assignable),
    Add(Box<Expression>, Box<Expression>),
    Sub(Box<Expression>, Box<Expression>),
    Mul(Box<Expression>, Box<Expression>),
    Div(Box<Expression>, Box<Expression>),

    Eq(Box<Expression>, Box<Expression>),
    Neq(Box<Expression>, Box<Expression>),
    Gt(Box<Expression>, Box<Expression>),
    Gteq(Box<Expression>, Box<Expression>),
    Lt(Box<Expression>, Box<Expression>),
    Lteq(Box<Expression>, Box<Expression>),

    And(Box<Expression>, Box<Expression>),
    Or(Box<Expression>, Box<Expression>),
    Neg(Box<Expression>, Box<Expression>),

    Call {
        function: usize,
        args: Vec<Expression>,
    },

    Group(Box<Expression>),

    // Composite
    Function {
        name: Identifier,
        args: Vec<(Identifier, Type)>,
        ret: Type,

        body: Vec<Statement>,
    },
    Tuple(Vec<Expression>),
    List(Vec<Expression>),
    Set(Vec<Expression>),
    Dict {
        keys: Vec<Expression>,
        values: Vec<Expression>,
    },

    // Simple
    Float(f64),
    Int(i64),
    String(String),
    Bool(bool),
    Nil,

}

#[derive(Debug, Clone)]
struct Expression {
    span: Span,
    kind: ExpressionKind,
}

#[derive(Debug, Clone)]
enum TypeKind {
    Resolved(runtimeType),
    Unresolved(String),
}

#[derive(Debug, Clone)]
struct Type {
    span: Span,
    kind: TypeKind,
}
