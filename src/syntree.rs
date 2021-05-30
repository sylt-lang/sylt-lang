use std::path::PathBuf;
use std::collections::HashMap;
use super::Type as runtimeType;

struct Range {
    start: usize,
    end: usize,
}

struct Prog {
    files: Vec<(PathBuf, Module)>,
}

struct Module {
    range: Range,
    statements: Vec<Statement>,
}

enum VarKind {
    Const,
    Mutable,
    GlobalConst,
    GlobalMutable,
}

enum AssignmentOp {
    Add,
    Sub,
    Mul,
    Div,
}

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

struct Statement {
    range: Range,
    kind: StatementKind,
}

struct Identifier {
    range: Range,
    name: String,
}

enum AssignableKind {
    Identifier(Identifier),
    Access(Identifier),
    Index(Expression),
}

struct Assignable {
    range: Range,
    expression: Vec<AssignableKind>,
}

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

struct Expression {
    range: Range,
    kind: ExpressionKind,
}

enum TypeKind {
    Resolved(runtimeType),
    Unresolved(String),
}

struct Type {
    range: Range,
    kind: TypeKind,
}
