use std::path::{PathBuf, Path};
use std::collections::HashMap;
use crate::error::Error;
use crate::tokenizer::{TokenStream, Token};
use super::Type as runtimeType;

#[derive(Debug, Copy, Clone)]
pub struct Span {
    // TODO(ed): Do this more intelligent, so
    // we can show ranges. Maybe even go back
    // to offsets from start of the file.
    line: usize,
}

#[derive(Debug, Clone)]
pub struct Prog {
    files: Vec<(PathBuf, Module)>,
}

#[derive(Debug, Clone)]
pub struct Module {
    span: Span,
    statements: Vec<Statement>,
}

#[derive(Debug, Copy, Clone)]
pub enum VarKind {
    Const,
    Mutable,
    GlobalConst,
    GlobalMutable,
}

#[derive(Debug, Copy, Clone)]
pub enum AssignmentOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug, Clone)]
pub enum StatementKind {
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
pub struct Statement {
    span: Span,
    kind: StatementKind,
}

#[derive(Debug, Clone)]
pub struct Identifier {
    span: Span,
    name: String,
}

#[derive(Debug, Clone)]
pub enum AssignableKind {
    Identifier(Identifier),
    Access(Identifier),
    Index(Expression),
}

#[derive(Debug, Clone)]
pub struct Assignable {
    span: Span,
    expression: Vec<AssignableKind>,
}

#[derive(Debug, Clone)]
pub enum ExpressionKind {
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
pub struct Expression {
    span: Span,
    kind: ExpressionKind,
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    Resolved(runtimeType),
    Unresolved(String),
}

#[derive(Debug, Clone)]
pub struct Type {
    span: Span,
    kind: TypeKind,
}

type Tokens = [(Token, usize)];

#[derive(Debug, Copy, Clone)]
struct Context<'a> {
    pub tokens: &'a Tokens,
    pub curr: usize,
    pub file: &'a Path,
}

impl<'a> Context<'a> {

    fn new(tokens: &'a [(Token, usize)], file: &'a Path) -> Self {
        Self { tokens, curr: 0, file, }
    }

    fn span(&self) -> Span {
        Span { line: self.peek().1 }
    }

    fn line(&self) -> usize {
        self.span().line
    }

    fn skip(&self, n: usize) -> Self {
        let mut new = self.clone();
        new.curr += n;
        new
    }

    fn peek(&self) -> &(Token, usize) {
        &self.tokens.get(self.curr).unwrap_or(&(Token::EOF, 0))
    }

    fn token(&self) -> &Token {
        &self.peek().0
    }

    fn eat(&self) -> (&Token, Span, Context) {
        (self.token(), self.span(), self.skip(1))
    }
}

macro_rules! syntax_error {
    ($ctx:expr, $( $msg:expr ),* ) => {
        {
            let msg = format!($( $msg ),*).into();
            Error::SyntaxError {
                file: $ctx.file.to_path_buf(),
                line: $ctx.line(),
                token: $ctx.token().clone(),
                message: Some(msg),
            }
        }
    };
}

macro_rules! raise_syntax_error {
    ($ctx:expr, $( $msg:expr ),* ) => {
        return Err(($ctx.skip(1), vec![syntax_error!($ctx, $( $msg ),*)]))
    };
}

fn expression<'t>(ctx: Context<'t>) -> Result<(Context<'t>, Expression), (Context<'t>, Vec<Error>)> {
    use Token as T;
    use ExpressionKind::*;
    let span = ctx.span();
    Ok(match ctx.token() {
        T::Float(v) => (ctx.skip(1), Expression { span, kind: Float(*v), }),
        T::Int(v) => (ctx.skip(1), Expression { span, kind: Int(*v), }),
        _ => {
            raise_syntax_error!(ctx.skip(1), "Failed to parse expression");
        }
    })
}

fn outer_statement<'t>(ctx: Context<'t>) -> Result<(Context<'t>, Statement), (Context<'t>, Vec<Error>)> {
    let span = ctx.span();
    let (ctx, value) = expression(ctx)?;

    use StatementKind::*;
    Ok((ctx, Statement { span, kind: StatementExpression { value } }))
}

pub fn construct(tokens: &Tokens) -> Result<Module, Vec<Error>> {
    let path = PathBuf::from("hello.sy");
    let mut ctx = Context::new(tokens, &path);
    let mut errors = Vec::new();
    let mut statements = Vec::new();
    while !matches!(ctx.token(), Token::EOF) {
        if matches!(ctx.peek().0, Token::Newline) {
            ctx = ctx.skip(1);
            continue;
        }
        println!("A {:?}", ctx.peek());
        ctx = match outer_statement(ctx) {
            Ok((_ctx, statement)) => {
                statements.push(statement);
                _ctx
            }
            Err((_ctx, mut errs)) => {
                errors.append(&mut errs);
                _ctx
            }
        }
    }

    if errors.is_empty() {
        Ok(Module { span: Span { line: 0 }, statements })
    } else {
        Err(errors)
    }
}
