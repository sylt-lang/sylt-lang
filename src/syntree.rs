use crate::error::Error;
use crate::rc::Rc;
use crate::tokenizer::file_to_tokens;
use crate::tokenizer::Token;
use crate::Next;
use crate::Type as RuntimeType;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::path::{Path, PathBuf};

type T = Token;

#[derive(Debug, Copy, Clone)]
/// A location in a file containing source code.
pub struct Span {
    // TODO(ed): Do this more intelligent, so
    // we can show ranges. Maybe even go back
    // to offsets from start of the file.
    pub line: usize,
}

/// Contains modules.
#[derive(Debug, Clone)]
pub struct Prog {
    pub modules: Vec<(PathBuf, Module)>,
}

/// Contains statements.
#[derive(Debug, Clone)]
pub struct Module {
    pub span: Span,
    pub statements: Vec<Statement>,
}

/// The precedence of an operator.
///
/// A higher precedence means that something should be more tightly bound. For
/// example, multiplication has higher precedence than addition and as such is
/// evaluated first.
///
/// Prec-variants can be compared to each other. A proc-macro ensures that the
/// comparison follows the ordering here such that
/// `prec_i < prec_j` for all `j > i`.
#[derive(sylt_macro::Next, PartialEq, PartialOrd, Clone, Copy, Debug)]
pub enum Prec {
    No,
    Assert,
    BoolOr,
    BoolAnd,
    Comp,
    Term,
    Factor,
    Index,
    Arrow,
}

/// Variables can be any combination of `{Force,}{Const,Mutable}`.
///
/// Forced variable kinds are a signal to the type checker that the type is
/// assumed and shouldn't be checked.
#[derive(Debug, Copy, Clone)]
pub enum VarKind {
    Const,
    Mutable,
    ForceConst,
    ForceMutable,
}

impl VarKind {
    pub fn immutable(&self) -> bool {
        matches!(self, VarKind::Const | VarKind::ForceConst)
    }

    pub fn force(&self) -> bool {
        matches!(self, VarKind::ForceConst | VarKind::ForceMutable)
    }
}

/// The different kinds of assignment operators: `+=`, `-=`, `*=`, `/=` and `=`.
#[derive(Debug, Copy, Clone)]
pub enum Op {
    Nop,
    Add,
    Sub,
    Mul,
    Div,
}

/// The different kinds of [Statement]s.
///
/// There are both shorter statements like `a = b + 1` as well as longer
/// statements like `if a { ... } else { ...}`. The variants here include
/// examples of how they look in the code.
///
/// Note that this shouldn't be read as a formal language specification.
#[derive(Debug, Clone)]
pub enum StatementKind {
    /// "Imports" another file.
    ///
    /// `use <file>`.
    Use {
        file: Identifier,
    },

    /// Defines a new Blob.
    ///
    /// `A :: Blob { <field>.. }`.
    Blob {
        name: String,
        fields: HashMap<String, Type>,
    },

    /// Prints to standard out.
    ///
    /// `print <expression>`.
    Print {
        value: Expression,
    },

    /// Assigns to a variable (`a = <expression>`), optionally with an operator
    /// applied (`a += <expression>`)
    Assignment {
        kind: Op,
        target: Assignable,
        value: Expression,
    },

    /// Defines a new variable.
    ///
    /// Example: `a := <expression>`.
    ///
    /// Valid definition operators are `::`, `:=` and `: <type> =`.
    Definition {
        ident: Identifier,
        kind: VarKind,
        ty: Type,
        value: Expression,
    },

    /// Makes your code go either here or there.
    ///
    /// `if <expression> <statement> [else <statement>]`.
    If {
        condition: Expression,
        pass: Box<Statement>,
        fail: Box<Statement>,
    },

    /// Do something as long as something else evaluates to true.
    ///
    /// `loop <expression> <statement>`.
    Loop {
        condition: Expression,
        body: Box<Statement>,
    },

    /// Returns a value from a function.
    ///
    /// `ret <expression>`.
    Ret {
        value: Expression,
    },

    // TODO(ed): break and continue

    /// Groups together statements that are executed after another.
    ///
    /// `{ <statement>.. }`.
    Block {
        statements: Vec<Statement>,
    },

    /// A free-standing expression. It's just a `<expression>`.
    StatementExpression {
        value: Expression,
    },

    /// Throws an error if it is ever evaluated.
    ///
    /// `<!>`.
    Unreachable,

    EmptyStatement,
}

/// What makes up a program. Contains any [StatementKind].
#[derive(Debug, Clone)]
pub struct Statement {
    pub span: Span,
    pub kind: StatementKind,
}

#[derive(Debug, Clone)]
pub struct Identifier {
    pub span: Span,
    pub name: String,
}

/// The different kinds of [Assignable]s.
///
/// Assignables are the left hand side of a [StatementKind::Assignment].
///
/// # Example
///
/// The recursive structure means that `a[2].b(1).c(2, 3)` is evaluated to
/// ```ignored
/// Access(
///     Index(
///         Read(a), 2
///     ),
///     Access(
///         Call(
///             Read(b), [1]
///         ),
///         Call(
///             Read(c), [2, 3]
///         )
///     )
/// )
/// ```
#[derive(Debug, Clone)]
pub enum AssignableKind {
    Read(Identifier),
    /// A function call.
    Call(Box<Assignable>, Vec<Expression>),
    Access(Box<Assignable>, Identifier),
    Index(Box<Assignable>, Box<Expression>),
}

/// Something that can be assigned to. The assignable value can be read if the
/// assignable is in an expression. Contains any [AssignableKind].
///
/// Note that assignables can occur both in the left hand side and the right hand
/// side of assignment statements, so something like `a = b` will be evaluated as
/// ```ignored
/// Statement::Assignment(
///     Assignable::Read(a),
///     Expression::Get(Assignable::Read(b))
/// )
/// ```
#[derive(Debug, Clone)]
pub struct Assignable {
    pub span: Span,
    pub kind: AssignableKind,
}

/// The different kinds of [Expression]s.
///
/// Expressions are recursive and evaluate to some kind of value.
#[derive(Debug, Clone)]
pub enum ExpressionKind {
    /// Read from an [Assignable]. Variables, function calls, module accesses,
    /// blob fields, list indexing, tuple indexing and dict indexing end up here.
    Get(Assignable),

    /// `a + b`
    Add(Box<Expression>, Box<Expression>),
    /// `a - b`
    Sub(Box<Expression>, Box<Expression>),
    /// `a * b`
    Mul(Box<Expression>, Box<Expression>),
    /// `a / b`
    Div(Box<Expression>, Box<Expression>),
    /// `-a`
    Neg(Box<Expression>),

    /// `a == b`
    Eq(Box<Expression>, Box<Expression>),
    /// `a != b`
    Neq(Box<Expression>, Box<Expression>),
    /// `a > b`
    Gt(Box<Expression>, Box<Expression>),
    /// `a >= b`
    Gteq(Box<Expression>, Box<Expression>),
    /// `a < b`
    Lt(Box<Expression>, Box<Expression>),
    /// `a <= b`
    Lteq(Box<Expression>, Box<Expression>),
    /// `a <=> b`
    AssertEq(Box<Expression>, Box<Expression>),

    /// `a in b`
    In(Box<Expression>, Box<Expression>),

    /// `a && b`
    And(Box<Expression>, Box<Expression>),
    /// `a || b`
    Or(Box<Expression>, Box<Expression>),
    /// `!a`
    Not(Box<Expression>),

    /// Functions and closures.
    Function {
        name: String,
        params: Vec<(Identifier, Type)>,
        ret: Type,

        body: Box<Statement>,
    },
    /// A new instance of a blob.
    Instance {
        blob: Assignable,
        fields: Vec<(String, Expression)>, // Keep calling order
    },
    /// `(a, b, ..)`
    Tuple(Vec<Expression>),
    /// `[a, b, ..]`
    List(Vec<Expression>),
    /// `{a, b, ..}`
    Set(Vec<Expression>),
    /// `{ a: b, c: d, .. }`
    // Has to have even length, listed { k1, v1, k2, v2 }
    Dict(Vec<Expression>),

    Float(f64),
    Int(i64),
    Str(String),
    Bool(bool),
    Nil,
}

/// Expressions evaluate to values. Contains any [ExpressionKind].
#[derive(Debug, Clone)]
pub struct Expression {
    pub span: Span,
    pub kind: ExpressionKind,
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    /// An unspecified type that is left to the type checker.
    Implied,
    /// A specified type by the user.
    Resolved(RuntimeType),
    /// I.e. blobs.
    UserDefined(Assignable),
    /// A type that can be either `a` or `b`.
    Union(Box<Type>, Box<Type>),
    /// `(params, return)`.
    Fn(Vec<Type>, Box<Type>),
    /// Tuples can mix types since the length is constant.
    Tuple(Vec<Type>),
    /// Lists only contain a single type.
    List(Box<Type>),
    /// Sets only contain a single type.
    Set(Box<Type>),
    /// `(key, value)`.
    Dict(Box<Type>, Box<Type>),
}

/// A parsed type. Contains any [TypeKind].
#[derive(Debug, Clone)]
pub struct Type {
    pub span: Span,
    pub kind: TypeKind,
}

/// Tokens and their line numbers.
type Tokens = [(T, usize)];

type ParseResult<'t, T> = Result<(Context<'t>, T), (Context<'t>, Vec<Error>)>;

/// Keeps track of where the parser is currently parsing.
#[derive(Debug, Copy, Clone)]
pub struct Context<'a> {
    /// All tokens to be parsed.
    pub tokens: &'a Tokens,
    /// The index of the curren token in the tokens slice.
    pub curr: usize,
    /// The file we're currently parsing.
    pub file: &'a Path,
}

impl<'a> Context<'a> {
    fn new(tokens: &'a Tokens, file: &'a Path) -> Self {
        Self {
            tokens,
            curr: 0,
            file,
        }
    }

    /// Get a [Span] representing the current location of the parser.
    fn span(&self) -> Span {
        Span {
            line: self.peek().1,
        }
    }

    /// The line currently beeing parsed.
    fn line(&self) -> usize {
        self.span().line
    }

    /// Move to the next nth token.
    fn skip(&self, n: usize) -> Self {
        let mut new = *self;
        new.curr += n;
        new
    }

    fn skip_if(&self, token: T) -> Self {
        if self.token() == &token {
            self.skip(1)
        } else {
            *self
        }
    }

    fn _skip_if_any<const N: usize>(&self, tokens: [T; N]) -> Self {
        if tokens.iter().any(|t| self.token() == t) {
            self.skip(1)
        } else {
            *self
        }
    }

    /// Eat until the next non-newline token.
    fn skip_while(&self, token: T) -> Self {
        let mut ret = *self;
        while ret.token() == &token {
            println!("wowe");
            ret = ret.skip(1);
        }
        ret
    }

    /// Return the current [Token] and line number.
    fn peek(&self) -> &(T, usize) {
        self.tokens.get(self.curr).unwrap_or(&(T::EOF, 0))
    }

    /// Return the current [Token].
    fn token(&self) -> &T {
        &self.peek().0
    }

    /// Eat a [Token] and move to the next.
    fn eat(&self) -> (&T, Span, Self) {
        (self.token(), self.span(), self.skip(1))
    }
}

//TODO(gu) None if no message?

/// Construct a syntax error at the current token with a message.
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

/// Raise a syntax error at the current token with a message.
macro_rules! raise_syntax_error {
    ($ctx:expr, $( $msg:expr ),* ) => {
        return Err(($ctx.skip(1), vec![syntax_error!($ctx, $( $msg ),*)]))
    };
}

/// Eat any one of the specified tokens and raise a syntax error if none is found.
macro_rules! expect {
    ($ctx:expr, $( $token:pat )|+ , $( $msg:expr ),+ ) => {
        {
            if !matches!($ctx.token(), $( $token )|* ) {
                raise_syntax_error!($ctx, $( $msg ),*);
            }
            $ctx.skip(1)
        }
    };

    ($ctx:expr, $( $token:pat )|+ ) => {
        expect!($ctx, $( $token )|*, concat!("Expected ", stringify!($( $token )|*)))
    };
}

/// Parse a [Type] definition, e.g. `fn int, int, bool -> bool`.
fn parse_type<'t>(ctx: Context<'t>) -> ParseResult<'t, Type> {
    use RuntimeType::{Bool, Float, Int, String, Void};
    use TypeKind::*;
    let span = ctx.span();
    let (ctx, kind) = match ctx.token() {
        T::Identifier(name) => match name.as_str() {
            "void" => (ctx.skip(1), Resolved(Void)),
            "int" => (ctx.skip(1), Resolved(Int)),
            "float" => (ctx.skip(1), Resolved(Float)),
            "bool" => (ctx.skip(1), Resolved(Bool)),
            "str" => (ctx.skip(1), Resolved(String)),
            _ => {
                let (ctx, assignable) = assignable(ctx)?;
                (ctx, UserDefined(assignable))
            }
        },

        // Function type
        T::Fn => {
            let mut ctx = ctx.skip(1);
            let mut params = Vec::new();
            // There might be multiple parameters.
            let ret = loop {
                match ctx.token() {
                    // Arrow implies only one type (the return type) is left.
                    T::Arrow => {
                        ctx = ctx.skip(1);
                        break if let Ok((_ctx, ret)) = parse_type(ctx) {
                            ctx = _ctx; // assign to outer
                            ret
                        } else {
                            // If we couldn't parse the return type, we assume `-> Void`.
                            Type {
                                span: ctx.span(),
                                kind: Resolved(Void),
                            }
                        };
                    }

                    T::EOF => {
                        raise_syntax_error!(ctx, "Didn't expect EOF in type definition");
                    }

                    // Parse a single parameter type.
                    _ => {
                        let (_ctx, param) = parse_type(ctx)?;
                        ctx = _ctx; // assign to outer
                        params.push(param);

                        ctx = if matches!(ctx.token(), T::Comma | T::Arrow) {
                            ctx.skip_if(T::Comma)
                        } else {
                            raise_syntax_error!(ctx, "Expected ',' or '->' after type parameter")
                        };
                    }
                }
            };
            (ctx, Fn(params, Box::new(ret)))
        }

        // Tuple
        T::LeftParen => {
            let mut ctx = ctx.skip(1);
            let mut types = Vec::new();
            // Tuples may (and probably will) contain multiple types.
            loop {
                match ctx.token() {
                    // Done parsing this tuple.
                    T::RightParen => {
                        ctx = ctx.skip(1);
                        break;
                    }

                    T::EOF => {
                        raise_syntax_error!(ctx, "Didn't expect EOF in type definition");
                    }

                    // Parse a single contained type.
                    _ => {
                        let (_ctx, param) = parse_type(ctx)?;
                        ctx = _ctx; // assign to outer
                        types.push(param);

                        ctx = if matches!(ctx.token(), T::Comma | T::RightParen) {
                            ctx.skip_if(T::Comma)
                        } else {
                            raise_syntax_error!(ctx, "Expected ',' or ')' after tuple field")
                        };
                    }
                }
            }
            (ctx, Tuple(types))
        }

        // List
        T::LeftBracket => {
            // Lists only contain a single type.
            let (ctx, ty) = parse_type(ctx.skip(1))?;
            let ctx = expect!(ctx, T::RightBracket, "Expected ']' after list type");
            (ctx, List(Box::new(ty)))
        }

        // Dict or set
        T::LeftBrace => {
            // { a } -> set
            // { a: b } -> dict
            // This means we can parse the first type unambiguously.
            let (ctx, ty) = parse_type(ctx.skip(1))?;
            if matches!(ctx.token(), T::Colon) {
                // Dict, parse another type.
                let (ctx, value) = parse_type(ctx.skip(1))?;
                let ctx = expect!(ctx, T::RightBrace, "Expected '}}' after dict type");
                (ctx, Dict(Box::new(ty), Box::new(value)))
            } else {
                // Set, done.
                let ctx = expect!(ctx, T::RightBrace, "Expected '}}' after set type");
                (ctx, Set(Box::new(ty)))
            }
        }

        t => {
            raise_syntax_error!(ctx, "No type starts with '{:?}'", t);
        }
    };

    // Wrap it in a syntax tree node.
    let ty = Type { span, kind };

    // Union type, `a | b`
    let (ctx, ty) = if matches!(ctx.token(), T::Pipe) {
        // Parse the other type.
        let (ctx, rest) = parse_type(ctx.skip(1))?;
        (
            ctx,
            Type {
                span,
                kind: Union(Box::new(ty), Box::new(rest)),
            },
        )
    } else {
        (ctx, ty)
    };

    // Nullable type. Compiles to `a | Void`.
    let (ctx, ty) = if matches!(ctx.token(), T::QuestionMark) {
        let void = Type {
            span: ctx.span(),
            kind: Resolved(Void),
        };
        (
            ctx.skip(1),
            Type {
                span,
                kind: Union(Box::new(ty), Box::new(void)),
            },
        )
    } else {
        (ctx, ty)
    };

    Ok((ctx, ty))
}

/// Parse a single [Statement].
fn statement<'t>(ctx: Context<'t>) -> ParseResult<'t, Statement> {
    use StatementKind::*;

    let span = ctx.span();
    let (ctx, kind) = match &ctx.tokens[ctx.curr..] {
        [(T::Newline, _), ..] => (ctx.skip(1), EmptyStatement),

        // Block: `{ <statements> }`
        [(T::LeftBrace, _), ..] => {
            let mut ctx = ctx.skip(1);
            let mut statements = Vec::new();
            // Parse multiple inner statements until } or EOF
            while !matches!(ctx.token(), T::RightBrace | T::EOF) {
                let (_ctx, stmt) = statement(ctx)?;
                ctx = _ctx; // assign to outer
                statements.push(stmt);
            }

            let ctx = expect!(ctx, T::RightBrace, "Expected }} after block statement");
            (ctx, Block { statements })
        }

        // `use a`
        [(T::Use, _), (T::Identifier(name), _), ..] => (
            ctx.skip(2),
            Use {
                file: Identifier {
                    span: ctx.skip(1).span(),
                    name: name.clone(),
                },
            },
        ),

        [(T::Unreachable, _), ..] => (ctx.skip(1), Unreachable),

        [(T::Print, _), ..] => {
            let (ctx, value) = expression(ctx.skip(1))?;
            (ctx, Print { value })
        }

        // `ret <expression>`
        [(T::Ret, _), ..] => {
            let ctx = ctx.skip(1);
            let (ctx, value) = if matches!(ctx.token(), T::Newline) {
                (
                    ctx,
                    Expression {
                        span: ctx.span(),
                        kind: ExpressionKind::Nil,
                    },
                )
            } else {
                expression(ctx)?
            };
            (ctx, Ret { value })
        }

        // `loop <expression> <statement>`, e.g. `loop a < 10 { a += 1 }`
        [(T::Loop, _), ..] => {
            let (ctx, condition) = expression(ctx.skip(1))?;
            let (ctx, body) = statement(ctx)?;
            (
                ctx,
                Loop {
                    condition,
                    body: Box::new(body),
                },
            )
        }

        // `if <expression> <statement> [else <statement>]`. Note that the else is optional.
        [(T::If, _), ..] => {
            let (ctx, condition) = expression(ctx.skip(1))?;

            let (ctx, pass) = statement(ctx)?;
            // else?
            let (ctx, fail) = if matches!(ctx.token(), T::Else) {
                let (ctx, fail) = statement(ctx.skip(1))?;
                (ctx, fail)
            } else {
                // No else so we insert an empty statement instead.
                (
                    ctx,
                    Statement {
                        span: ctx.span(),
                        kind: EmptyStatement,
                    },
                )
            };

            (
                ctx,
                If {
                    condition,
                    pass: Box::new(pass),
                    fail: Box::new(fail),
                },
            )
        }

        // Blob declaration: `A :: blob { <fields> }
        [(T::Identifier(name), _), (T::ColonColon, _), (T::Blob, _), ..] => {
            let name = name.clone();
            let mut ctx = expect!(ctx.skip(3), T::LeftBrace, "Expected '{{' to open blob");
            let mut fields = HashMap::new();
            // Parse fields: `a: int`
            loop {
                match ctx.token().clone() {
                    T::Newline => {
                        ctx = ctx.skip(1);
                    }
                    // Done with fields.
                    T::RightBrace => {
                        break;
                    }

                    // Another one.
                    T::Identifier(field) => {
                        if fields.contains_key(&field) {
                            raise_syntax_error!(ctx, "Field '{}' is declared twice", field);
                        }
                        ctx = expect!(ctx.skip(1), T::Colon, "Expected ':' after field name");
                        let (_ctx, ty) = parse_type(ctx)?;
                        ctx = _ctx; // assign to outer
                        fields.insert(field, ty);

                        if !matches!(ctx.token(), T::Comma | T::Newline | T::RightBrace) {
                            raise_syntax_error!(
                                ctx,
                                "Expected a field deliminator: newline or ','"
                            );
                        }
                        ctx = ctx.skip_if(T::Comma);
                    }

                    _ => {
                        raise_syntax_error!(ctx, "Expected field name or '}}' in blob statement");
                    }
                }
            }
            let ctx = expect!(ctx, T::RightBrace, "Expected '}}' to close blob fields");
            (ctx, Blob { name, fields })
        }

        // Constant declaration, e.g. `a :: 1`.
        [(T::Identifier(name), _), (T::ColonColon, _), ..] => {
            let ident = Identifier {
                name: name.clone(),
                span: ctx.span(),
            };
            // Skip identifier and `::`.
            let ctx = ctx.skip(2);

            // The value to assign.
            let (ctx, value) = expression(ctx)?;

            (
                ctx,
                Definition {
                    ident,
                    kind: VarKind::Const,
                    ty: Type {
                        span: ctx.span(),
                        kind: TypeKind::Implied,
                    },
                    value,
                },
            )
        }

        // Mutable declaration, e.g. `b := 2`.
        [(T::Identifier(name), _), (T::ColonEqual, _), ..] => {
            let ident = Identifier {
                name: name.clone(),
                span: ctx.span(),
            };
            // Skip identifier and `:=`.
            let ctx = ctx.skip(2);

            // The value to assign.
            let (ctx, value) = expression(ctx)?;

            (
                ctx,
                Definition {
                    ident,
                    kind: VarKind::Mutable,
                    ty: Type {
                        span: ctx.span(),
                        kind: TypeKind::Implied,
                    },
                    value,
                },
            )
        }

        // Variable declaration with specified type, e.g. `c : int = 3` or `b : int | bool : false`.
        [(T::Identifier(name), _), (T::Colon, _), ..] => {
            let ident = Identifier {
                name: name.clone(),
                span: ctx.span(),
            };
            // Skip identifier and ':'.
            let ctx = ctx.skip(2);

            let (ctx, kind, ty) = {
                let forced = matches!(ctx.token(), T::Bang); // !int
                let ctx = ctx.skip_if(T::Bang);
                let (ctx, ty) = parse_type(ctx)?;
                let kind = match (ctx.token(), forced) {
                    (T::Colon, true) => VarKind::ForceConst,
                    (T::Equal, true) => VarKind::ForceMutable,
                    (T::Colon, false) => VarKind::Const,
                    (T::Equal, false) => VarKind::Mutable,
                    (t, _) => {
                        raise_syntax_error!(
                            ctx,
                            "Expected ':' or '=' for definition, but got '{:?}'",
                            t
                        );
                    }
                };
                // Skip `:` or `=`.
                (ctx.skip(1), kind, ty)
            };

            // The value to define the variable to.
            let (ctx, value) = expression(ctx)?;

            (
                ctx,
                Definition {
                    ident,
                    kind,
                    ty,
                    value,
                },
            )
        }

        // Expression or assignment. We try assignment first.
        _ => {
            /// `a = 5`.
            fn assignment<'t>(ctx: Context<'t>) -> ParseResult<'t, StatementKind> {
                // The assignable to assign to.
                let (ctx, target) = assignable(ctx)?;
                let kind = match ctx.token() {
                    T::PlusEqual => Op::Add,
                    T::MinusEqual => Op::Sub,
                    T::StarEqual => Op::Mul,
                    T::SlashEqual => Op::Div,
                    T::Equal => Op::Nop,

                    t => {
                        raise_syntax_error!(ctx, "No assignment operation matches '{:?}'", t);
                    }
                };
                // The expression to assign the assignable to.
                let (ctx, value) = expression(ctx.skip(1))?;
                Ok((
                    ctx,
                    Assignment {
                        kind,
                        target,
                        value,
                    },
                ))
            }

            // TODO(ed): Potenitally risky - might destroy errors aswell
            if let Ok((ctx, kind)) = assignment(ctx) {
                (ctx, kind)
            } else {
                let (ctx, value) = expression(ctx)?;
                (ctx, StatementExpression { value })
            }
        }
    };

    // TODO(ed): Not sure this is right.
    // let ctx = expect!(ctx, T::Newline, "Expected newline after statement");
    let ctx = ctx.skip_if(T::Newline);
    Ok((ctx, Statement { span, kind }))
}

/// Parse an [AssignableKind::Call]
fn assignable_call<'t>(ctx: Context<'t>, callee: Assignable) -> ParseResult<'t, Assignable> {
    let span = ctx.span();
    let banger = matches!(ctx.token(), T::Bang); // `f! 1, 2
    let mut ctx = expect!(
        ctx,
        T::Bang | T::LeftParen,
        "Expected '(' or '!' when calling function"
    );
    let mut args = Vec::new();

    // Arguments
    loop {
        match (ctx.token(), banger) {
            // Done with arguments.
            (T::EOF, _)
            | (T::RightParen, false)
            | (T::Dot, true)
            | (T::Newline, true)
            | (T::Arrow, true) => {
                break;
            }

            // Parse a single argument.
            _ => {
                let (_ctx, expr) = expression(ctx)?;
                ctx = _ctx; // assign to outer
                args.push(expr);

                ctx = ctx.skip_if(T::Comma);
            }
        }
    }

    let ctx = if !banger {
        expect!(ctx, T::RightParen, "Expected ')' after calling function")
    } else {
        ctx
    };

    use AssignableKind::Call;
    //TODO ?
    let result = Assignable {
        span,
        kind: Call(Box::new(callee), args),
    };
    sub_assignable(ctx, result)
}

/// Parse an [AssignableKind::Index].
fn assignable_index<'t>(ctx: Context<'t>, indexed: Assignable) -> ParseResult<'t, Assignable> {
    let span = ctx.span();
    let mut ctx = expect!(
        ctx,
        T::LeftBracket,
        "Expected '[' when indexing"
    );

    let (_ctx, expr) = expression(ctx)?;
    ctx = _ctx; // assign to outer
    let ctx = expect!(
        ctx,
        T::RightBracket,
        "Expected ']' after index"
    );

    use AssignableKind::Index;
    let result = Assignable {
        span,
        kind: Index(Box::new(indexed), Box::new(expr)),
    };
    sub_assignable(ctx, result)
}

/// Parse an [AssignableKind::Access].
fn assignable_dot<'t>(ctx: Context<'t>, accessed: Assignable) -> ParseResult<'t, Assignable> {
    use AssignableKind::Access;
    let (ctx, ident) = if let (T::Identifier(name), span, ctx) = ctx.skip(1).eat() {
        (
            ctx,
            Identifier {
                name: name.clone(),
                span,
            }
        )
    } else {
        raise_syntax_error!(
            ctx,
            "Assignable expressions have to start with an identifier"
        );
    };

    let access = Assignable { span: ctx.span(), kind: Access(Box::new(accessed), ident) };
    sub_assignable(ctx, access)
}

/// Parse a (maybe empty) "sub-assignable", i.e. either a call or indexable.
fn sub_assignable<'t>(ctx: Context<'t>, assignable: Assignable) -> ParseResult<'t, Assignable> {
    match ctx.token() {
        T::Bang | T::LeftParen => assignable_call(ctx, assignable),
        T::LeftBracket => assignable_index(ctx, assignable),
        T::Dot => assignable_dot(ctx, assignable),
        _ => Ok((ctx, assignable))
    }
}

/// Parse an [Assignable].
///
/// [Assignable]s can be quite complex, e.g. `a[2].b(1).c(2, 3)`. They're parsed
/// one "step" at a time recursively, so this example will go through three calls
/// to [assignable].
///
/// 1. Parse `c(2, 3)` into `Call(Read(c), [2, 3])`.
/// 2. Parse `b(1).c(2, 3)` into `Access(Call(Read(b), [1]), <parsed c(2, 3)>)`.
/// 3. Parse `a[2].b(1).c(2, 3)` into `Access(Index(Read(a), 2), <parsed b(1).c(2, 3)>)`.
fn assignable<'t>(ctx: Context<'t>) -> ParseResult<'t, Assignable> {
    use AssignableKind::*;
    let outer_span = ctx.span();

    // Get the identifier.
    let ident = if let (T::Identifier(name), span) = (ctx.token(), ctx.span()) {
        Assignable {
            span: outer_span,
            kind: Read(Identifier {
                span,
                name: name.clone(),
            }),
        }
    } else {
        raise_syntax_error!(
            ctx,
            "Assignable expressions have to start with an identifier"
        );
    };

    // Parse chained [], . and ().
    sub_assignable(ctx.skip(1), ident)
}

use expression::expression;
mod expression {
    use super::*;
    use ExpressionKind::*;

    /// Parse an [ExpressionKind::Function]: `fn a: int, b: bool -> bool <statement>`
    fn function<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
        let span = ctx.span();
        let mut ctx = expect!(ctx, T::Fn, "Expected 'fn' for function expression");
        let mut params = Vec::new();
        // Parameters
        let ret = loop {
            match ctx.token() {
                T::Identifier(name) => {
                    // Parameter name
                    let ident = Identifier {
                        span: ctx.span(),
                        name: name.clone(),
                    };
                    ctx = expect!(ctx.skip(1), T::Colon, "Expected ':' after parameter name");
                    // Parameter type
                    let (_ctx, param) = parse_type(ctx)?;
                    ctx = _ctx; // assign to outer

                    params.push((ident, param));

                    ctx = if matches!(ctx.token(), T::Comma | T::Arrow | T::LeftBrace) {
                        ctx.skip_if(T::Comma)
                    } else {
                        raise_syntax_error!(ctx, "Expected ',' '{{' or '->' after type parameter")
                    };
                }

                // Parse return type
                T::Arrow => {
                    ctx = ctx.skip(1);
                    break if let Ok((_ctx, ret)) = parse_type(ctx) {
                        ctx = _ctx; // assign to outer
                        ret
                    } else {
                        use RuntimeType::Void;
                        use TypeKind::Resolved;
                        Type {
                            // If we couldn't parse the return type, we assume `-> Void`.
                            span: ctx.span(),
                            kind: Resolved(Void),
                        }
                    };
                }

                T::LeftBrace => {
                    use RuntimeType::Void;
                    use TypeKind::Resolved;
                    // No return type so we assume `-> Void`.
                    break Type {
                        span: ctx.span(),
                        kind: Resolved(Void),
                    };
                }

                t => {
                    raise_syntax_error!(ctx, "Didn't expect '{:?}' in function", t);
                }
            }
        };

        // Parse the function statement. Usually a block statement but it's not currently forced.
        let (ctx, statement) = statement(ctx)?;
        let function = Function {
            name: "lambda".into(),
            params,
            ret,
            body: Box::new(statement),
        };

        Ok((
            ctx,
            Expression {
                span,
                kind: function,
            },
        ))
    }

    /// Parse an expression until we reach a token with higher precedence.
    fn parse_precedence<'t>(ctx: Context<'t>, prec: Prec) -> ParseResult<'t, Expression> {
        // Initial value, e.g. a number value, assignable, ...
        let (mut ctx, mut expr) = prefix(ctx)?;
        while prec <= precedence(ctx.token()) {
            if let Ok((_ctx, _expr)) = infix(ctx, &expr) {
                // assign to outer
                ctx = _ctx;
                expr = _expr;
            } else {
                break;
            }
        }
        Ok((ctx, expr))
    }

    /// Return a [Token]'s precedence.
    ///
    /// See the documentation on [Prec] for how to interpret and compare the
    /// variants.
    #[rustfmt::skip]
    fn precedence(token: &T) -> Prec {
        match token {
            T::LeftBracket => Prec::Index,

            T::Star | T::Slash => Prec::Factor,

            T::Minus | T::Plus => Prec::Term,

            T::EqualEqual
            | T::Greater
            | T::GreaterEqual
            | T::Less
            | T::LessEqual
            | T::NotEqual => Prec::Comp,

            T::And => Prec::BoolAnd,
            T::Or => Prec::BoolOr,

            T::In => Prec::Index,

            T::AssertEqual => Prec::Assert,

            T::Arrow => Prec::Arrow,

            _ => Prec::No,
        }
    }

    /// Parse a single (primitive) value.
    fn value<'t>(ctx: Context<'t>) -> Result<(Context<'t>, Expression), (Context<'t>, Vec<Error>)> {
        let (token, span, ctx) = ctx.eat();
        let kind = match token.clone() {
            T::Float(f) => Float(f),
            T::Int(i) => Int(i),
            T::Bool(b) => Bool(b),
            T::Nil => Nil,
            T::String(s) => Str(s),
            t => {
                raise_syntax_error!(ctx, "Cannot parse value, '{:?}' is not a valid value", t);
            }
        };
        Ok((ctx, Expression { span, kind }))
    }

    /// Parse something that begins at the start of an expression.
    fn prefix<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
        match ctx.token() {
            T::LeftParen => grouping_or_tuple(ctx),
            T::LeftBracket => list(ctx),
            T::LeftBrace => set_or_dict(ctx),

            T::Float(_) | T::Int(_) | T::Bool(_) | T::String(_) | T::Nil => value(ctx),
            T::Minus | T::Bang => unary(ctx),

            T::Identifier(_) => {
                // Blob initializations are expressions.
                if let Ok(result) = blob(ctx) {
                    Ok(result)
                } else {
                    let span = ctx.span();
                    let (ctx, assign) = assignable(ctx)?;
                    Ok((
                        ctx,
                        Expression {
                            span,
                            kind: Get(assign),
                        },
                    ))
                }
            }

            t => {
                raise_syntax_error!(ctx, "No valid expression starts with '{:?}'", t);
            }
        }
    }

    /// Parse a unary operator followed by an expression, e.g. `-5`.
    fn unary<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
        let (op, span, ctx) = ctx.eat();
        let (ctx, expr) = parse_precedence(ctx, Prec::Factor)?;
        let expr = Box::new(expr);

        let kind = match op {
            T::Minus => Neg(expr),
            T::Bang => Not(expr),

            _ => {
                raise_syntax_error!(ctx, "Invalid unary operator");
            }
        };
        Ok((ctx, Expression { span, kind }))
    }

    /// Parse an expression starting from an infix operator. Called by `parse_precedence`.
    fn infix<'t>(ctx: Context<'t>, lhs: &Expression) -> ParseResult<'t, Expression> {
        // Parse an operator and a following expression
        // until we reach a token with higher precedence.
        let (op, span, ctx) = ctx.eat();
        let (ctx, rhs) = parse_precedence(ctx, precedence(op).next())?;

        // Left and right of the operator.
        let lhs = Box::new(lhs.clone());
        let rhs = Box::new(rhs);

        // Which expression kind to omit depends on the token.
        let kind = match op {
            // Simple arithmetic.
            T::Plus => Add(lhs, rhs),
            T::Minus => Sub(lhs, rhs),
            T::Star => Mul(lhs, rhs),
            T::Slash => Div(lhs, rhs),
            T::EqualEqual => Eq(lhs, rhs),
            T::NotEqual => Neq(lhs, rhs),
            T::Greater => Gt(lhs, rhs),
            T::GreaterEqual => Gteq(lhs, rhs),
            T::Less => Lt(lhs, rhs),
            T::LessEqual => Lteq(lhs, rhs),

            // Boolean operators.
            T::And => And(lhs, rhs),
            T::Or => Or(lhs, rhs),

            T::AssertEqual => AssertEq(lhs, rhs),

            T::In => In(lhs, rhs),

            // The cool arrow syntax. For example: `a->b(2)` compiles to `b(a, 2)`.
            T::Arrow => {
                use AssignableKind::Call;
                // Rhs has to be an ExpressionKind::Get(AssignableKind::Call).
                if let Get(Assignable { kind: Call(callee, mut args), ..  }) = rhs.kind {
                    // Insert lhs as the first argument.
                    args.insert(0, *lhs);
                    // Return the new expression.
                    Get(Assignable {
                        kind: Call(callee, args),
                        span: rhs.span,
                    })
                } else {
                    raise_syntax_error!(ctx, "Expected a call-expression after '->'");
                }
            }

            // Unknown infix operator.
            _ => {
                return Err((ctx, Vec::new()));
            }
        };

        Ok((ctx, Expression { span, kind }))
    }

    /// Parse either a grouping parenthesis or a tuple.
    ///
    /// Essentially, one-element tuples are groupings unless they end with a
    /// comma. So `(1)` is parsed as the value `1` while `(1,)` is parsed as the
    /// one-sized tuple containing `1`.
    ///
    /// `()` as well as `(,)` are parsed as zero-sized tuples.
    fn grouping_or_tuple<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
        let span = ctx.span();
        let mut ctx = expect!(ctx, T::LeftParen, "Expected '('");

        // The expressions contained in the parenthesis.
        let mut exprs = Vec::new();

        let mut is_tuple = matches!(ctx.token(), T::Comma | T::RightParen);
        loop {
            // Any initial comma is skipped since we checked it before entering the loop.
            ctx = ctx.skip_if(T::Comma);
            match ctx.token() {
                // Done.
                T::EOF | T::RightParen => {
                    break;
                }

                // Another inner expression.
                _ => {
                    let (_ctx, expr) = expression(ctx)?;
                    exprs.push(expr);
                    ctx = _ctx; // assign to outer
                    // Not a tuple, until it is.
                    is_tuple |= matches!(ctx.token(), T::Comma);
                }
            }
        }

        ctx = expect!(ctx, T::RightParen, "Expected ')'");
        let result = if is_tuple {
            Expression {
                span,
                kind: Tuple(exprs),
            }
        } else {
            exprs.remove(0)
        };
        Ok((ctx, result))
    }

    /// Parse a blob instantiation, e.g. `A { b: 55 }`.
    fn blob<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
        let span = ctx.span();
        let (ctx, blob) = assignable(ctx)?;
        let mut ctx = expect!(ctx, T::LeftBrace, "Expected '{{' after blob name");

        // The blob's fields.
        let mut fields = Vec::new();
        loop {
            match ctx.token() {
                T::Newline => {
                    ctx = ctx.skip(1);
                }

                // Done with fields.
                T::RightBrace | T::EOF => {
                    break;
                }

                // Another field, e.g. `b: 55`.
                T::Identifier(name) => {
                    // Get the field name.
                    let name = name.clone();

                    ctx = expect!(ctx.skip(1), T::Colon, "Expected ':' after field name");
                    // Get the value; `55` in the example above.
                    let (_ctx, expr) = expression(ctx)?;
                    ctx = _ctx; // assign to outer

                    if !matches!(ctx.token(), T::Comma | T::Newline | T::RightBrace) {
                        raise_syntax_error!(ctx, "Expected a delimiter: newline or ','");
                    }
                    ctx = ctx.skip_if(T::Comma);

                    fields.push((name, expr));
                }

                t => {
                    raise_syntax_error!(ctx, "Unexpected token ('{:?}') in blob initalizer", t);
                }
            }
        }
        let ctx = expect!(ctx, T::RightBrace, "Expected '}}' after blob initalizer");

        if matches!(ctx.token(), T::Else) {
            raise_syntax_error!(ctx, "Parsed a blob instance not an if-statement");
        }

        Ok((
            ctx,
            Expression {
                span,
                kind: Instance { blob, fields },
            },
        ))
    }

    // Parse a list expression, e.g. `[1, 2, a(3)]`
    fn list<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
        let span = ctx.span();
        let mut ctx = expect!(ctx, T::LeftBracket, "Expected '['");

        // `l := [\n1` is valid
        ctx = ctx.skip_while(T::Newline);

        // Inner experssions.
        let mut exprs = Vec::new();
        loop {
            match ctx.token() {
                // Done with inner expressions.
                T::EOF | T::RightBracket => {
                    break;
                }

                // Another one.
                _ => {
                    let (_ctx, expr) = expression(ctx)?;
                    exprs.push(expr);
                    ctx = _ctx; // assign to outer
                    ctx = ctx.skip_if(T::Comma);
                    ctx = ctx.skip_while(T::Newline); // newlines after expression is valid inside lists
                }
            }
        }

        ctx = expect!(ctx, T::RightBracket, "Expected ']'");
        Ok((
            ctx,
            Expression {
                span,
                kind: List(exprs),
            },
        ))
    }

    /// Parse either a set or dict expression.
    ///
    /// `{:}` is parsed as the empty dict and {} is parsed as the empty set.
    fn set_or_dict<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
        let span = ctx.span();
        let mut ctx = expect!(ctx, T::LeftBrace, "Expected '{{'");

        // The inner values of the set or dict.
        let mut exprs = Vec::new();
        // None => we don't know. Some(b) => we know b.
        let mut is_dict = None;
        loop {
            match ctx.token() {
                // Done.
                T::EOF | T::RightBrace => {
                    break;
                }

                // Free-standing colon, i.e. "empty dict pair".
                T::Colon => {
                    // Only valid if we don't know yet.
                    if let Some(is_dict) = is_dict {
                        raise_syntax_error!(
                            ctx,
                            "Empty dict pair is invalid in a {}",
                            if is_dict { "dict" } else { "set" }
                        );
                    }
                    is_dict = Some(true);
                    ctx = ctx.skip(1);
                }

                // Something that's part of an inner expression.
                _ => {
                    // Parse the expression.
                    let (_ctx, expr) = expression(ctx)?;
                    ctx = _ctx; // assign to outer
                    exprs.push(expr);

                    // If a) we know we're a dict or b) the next token is a colon, parse the value of the dict.
                    // Also, if we didn't know previously, store whether we're a dict or not.
                    if *is_dict.get_or_insert_with(|| matches!(ctx.token(), T::Colon)) {
                        ctx = expect!(ctx, T::Colon, "Expected ':' for dict pair");
                        // Parse value expression.
                        let (_ctx, expr) = expression(ctx)?;
                        ctx = _ctx; // assign to outer
                        exprs.push(expr);
                    }

                    ctx = ctx.skip_if(T::Comma);
                }
            }
        }

        ctx = expect!(ctx, T::RightBrace, "Expected '}}'");

        // If we still don't know, assume we're a set.
        let kind = if is_dict.unwrap_or(false) {
            Dict(exprs)
        } else {
            Set(exprs)
        };

        Ok((ctx, Expression { span, kind }))
    }

    /// Parse a single expression.
    ///
    /// An expression is either a function expression or a "normal"
    /// expression that follows precedence rules.

    pub fn expression<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
        match ctx.token() {
            T::Fn => function(ctx),
            _ => parse_precedence(ctx, Prec::No),
        }
    }
}

/// Parse an outer statement.
///
/// Currently all statements are valid outer statements.
fn outer_statement<'t>(ctx: Context<'t>) -> ParseResult<Statement> {
    // TODO(ed): Filter for invalid outer statements here.
    statement(ctx)
}

/// Parses a file's tokens. Returns a list of files it refers to (via `use`s) and
/// the parsed statements.
///
/// # Errors
///
/// Returns any errors that occured when parsing the file. Basic error
/// continuation is performed, so errored statements are skipped until a newline
/// or EOF.
fn module(path: &Path, tokens: &Tokens) -> (Vec<PathBuf>, Result<Module, Vec<Error>>) {
    let mut ctx = Context::new(tokens, path);
    let mut errors = Vec::new();
    let mut use_files = Vec::new();
    let mut statements = Vec::new();
    while !matches!(ctx.token(), T::EOF) {
        // Ignore newlines.
        if matches!(ctx.token(), T::Newline) {
            ctx = ctx.skip(1);
            continue;
        }
        // Parse an outer statement.
        ctx = match outer_statement(ctx) {
            Ok((ctx, statement)) => {
                use StatementKind::*;
                // Yank `use`s and add it to the used-files list.
                if let Use { file, .. } = &statement.kind {
                    let file = PathBuf::from(format!("{}.sy", file.name));
                    use_files.push(file);
                }
                // Only push non-empty statements.
                if !matches!(statement.kind, EmptyStatement) {
                    statements.push(statement);
                }
                ctx
            }
            Err((mut ctx, mut errs)) => {
                errors.append(&mut errs);

                // "Error recovery"
                while !matches!(ctx.token(), T::EOF | T::Newline) {
                    ctx = ctx.skip(1);
                }
                ctx
            }
        }
    }

    if errors.is_empty() {
        (
            use_files,
            Ok(Module {
                span: Span { line: 0 },
                statements,
            }),
        )
    } else {
        (use_files, Err(errors))
    }
}

/// Look for git conflict markers (`<<<<<<<`) in a file.
///
/// Since conflict markers might be present anywhere, we don't even try to save
/// the parsing if we find any.
///
/// # Errors
///
/// Returns a [Vec] of all errors found.
///
/// - [Error::FileNotFound] if the file couldn't be found.
/// - [Error::GitConflictError] if conflict markers were found.
/// - Any [Error::IOError] that occured when reading the file.
pub fn find_conflict_markers(file: &Path) -> Vec<Error> {
    let s = match std::fs::read_to_string(file) {
        Ok(s) => s,
        Err(e) => return vec![
            if matches!(e.kind(), std::io::ErrorKind::NotFound) {
                Error::FileNotFound(file.to_path_buf())
            } else {
                Error::IOError(Rc::new(e))
            }
        ],
    };
    let mut errs = Vec::new();
    // Search line by line and push any errors we find.
    for (i, line) in s.lines().enumerate() {
        if line.starts_with("<<<<<<<") {
            errs.push(Error::GitConflictError {
                file: file.to_path_buf(),
                start: i + 1,
            });
        }
    }
    errs
}

/// Parses the contents of a file as well as all files this file refers to and so
/// on.
///
/// Returns the resulting [Program](Prog) (list of [Module]s).
///
/// # Errors
///
/// Returns any errors that occured when parsing the file(s). Basic error
/// continuation is performed as documented in [module].
pub fn tree(path: &Path) -> Result<Prog, Vec<Error>> {
    // Files we've already parsed. This ensures circular includes don't parse infinitely.
    let mut visited = HashSet::new();
    // Files we want to parse but haven't yet.
    let mut to_visit = Vec::new();
    let root = path.parent().unwrap();
    to_visit.push(PathBuf::from(path.file_name().unwrap()));

    let mut modules = Vec::new();
    let mut errors = Vec::new();
    while let Some(file) = to_visit.pop() {
        let file = root.join(file);
        if visited.contains(&file) {
            continue;
        }
        // Look for conflict markers
        let mut conflict_errors = find_conflict_markers(&file);
        if !conflict_errors.is_empty() {
            errors.append(&mut conflict_errors);
            visited.insert(file);
            continue;
        }
        // Lex into tokens.
        match file_to_tokens(&file) {
            Ok(tokens) => {
                // Parse the module.
                let (mut next, result) = module(path, &tokens);
                match result {
                    Ok(module) => modules.push((file.clone(), module)),
                    Err(mut errs) => errors.append(&mut errs),
                }
                to_visit.append(&mut next);
            }
            Err(_) => {
                errors.push(Error::FileNotFound(file.clone()));
            }
        }
        visited.insert(file);
    }

    if errors.is_empty() {
        Ok(Prog { modules })
    } else {
        Err(errors)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::tokenizer::string_to_tokens;

    macro_rules! test {
        ($f:ident, $name:ident: $str:expr => $ans:pat) => {
            #[test]
            fn $name() {
                let tokens = string_to_tokens($str);
                let path = PathBuf::from(stringify!($name));
                let result = $f(Context::new(&tokens, &path));
                assert!(
                    result.is_ok(),
                    "\nSyntax tree test didn't parse for:\n{}\nErrs: {:?}",
                    $str,
                    result.unwrap_err().1
                );
                let (ctx, result) = result.unwrap();
                assert!(
                    matches!(result.kind, $ans),
                    "\nExpected: {}, but got: {:?}",
                    stringify!($ans),
                    result
                );
                assert_eq!(
                    ctx.curr,
                    ctx.tokens.len(),
                    "Parsed too few or too many tokens:\n{}",
                    $str
                );
            }
        };
    }

    // TODO(ed): It's really hard to write good tests, Rust refuses to deref the boxes
    // automatically.
    mod expression {
        use super::*;
        use AssignableKind::*;
        use ExpressionKind::*;

        test!(expression, value: "0" => Int(0));
        test!(expression, add: "0 + 1.0" => Add(_, _));
        test!(expression, mul: "\"abc\" * \"abc\"" => Mul(_, _));
        test!(expression, ident: "a" => Get(Assignable { kind: Read(_), .. }));
        test!(expression, access: "a.b" => Get(Assignable { kind: Access(_, _), .. }));
        test!(expression, index_ident: "a[a]" => Get(Assignable { kind: Index(_, _), .. }));
        test!(expression, index_expr: "a[1 + 2 + 3]" => Get(Assignable { kind: Index(_, _), .. }));
        test!(expression, grouping: "(0 * 0) + 1" => Add(_, _));
        test!(expression, grouping_one: "(0)" => Int(0));
        test!(expression, tuple: "(0, 0)" => Tuple(_));
        test!(expression, tuple_one: "(0,)" => Tuple(_));
        test!(expression, tuple_empty: "()" => Tuple(_));
        test!(expression, list: "[0, 0]" => List(_));
        test!(expression, set: "{1, 1}" => Set(_));
        test!(expression, dict: "{1: 1}" => Dict(_));
        test!(expression, zero_set: "{}" => Set(_));
        test!(expression, zero_dict: "{:}" => Dict(_));

        test!(expression, in_list: "a in [1, 2, 3]" => In(_, _));
        test!(expression, in_set: "2 in {1, 1, 2}" => In(_, _));
        test!(expression, in_grouping: "1 + 2 in b" => Add(_, _));
        test!(expression, in_grouping_paren: "(1 + 2) in b" => In(_, _));

        test!(expression, call_simple_paren: "a()" => Get(_));
        test!(expression, call_call: "a()()" => Get(_));
        test!(expression, call_simple_bang: "a!" => Get(_));
        test!(expression, call_chaining_paren: "a().b" => Get(_));
        test!(expression, call_chaining_bang: "a!.b" => Get(_));
        test!(expression, call_args_paren: "a(1, 2, 3)" => Get(_));
        test!(expression, call_args_bang: "a! 1, 2, 3" => Get(_));
        test!(expression, call_args_chaining_paren: "a(1, 2, 3).b" => Get(_));
        test!(expression, call_args_chaining_paren_trailing: "a(1, 2, 3,).b" => Get(_));
        test!(expression, assignable_index: "a[0]" => Get(_));
        test!(expression, assignable_index_twice: "a[0][1]" => Get(_));
        test!(expression, assignable_mixed: "a[0]()" => Get(_));
        test!(expression, assignable_mixed_many: "a()[0]()[1]()()()[2][3]" => Get(_));

        // TODO(ed): This is controverisal
        test!(expression, call_args_chaining_bang: "a! 1, 2, 3 .b" => Get(_));
        test!(expression, call_args_chaining_bang_trailing: "a! 1, 2, 3, .b" => Get(_));

        // TODO(ed): Verify 'a! -> b! -> c! == c(b(a()))' in some way
        test!(expression, call_arrow: "1 + 0 -> a! 2, 3" => Add(_, _));
        test!(expression, call_arrow_grouping: "(1 + 0) -> a! 2, 3" => Get(_));

        test!(expression, instance: "A { a: 1 + 1, b: nil }" => Instance { .. });
        test!(expression, instance_more: "A { a: 2\n c: 2 }" => Instance { .. });
        test!(expression, instance_empty: "A {}" => Instance { .. });

        // TODO(ed): Require block or allow all statements?
        test!(expression, simple: "fn -> {}" => _);
        test!(expression, argument: "fn a: int -> int ret a + 1" => _);

        test!(expression, booleans: "true && false || !false" => _);
        test!(expression, bool_and: "true && a" => _);
        test!(expression, bool_or: "a || false" => _);
        test!(expression, bool_neg: "!a" => _);
        test!(expression, bool_neg_multiple: "!a && b" => _);
        test!(expression, bool_neg_multiple_rev: "a && !b" => _);

        test!(expression, cmp_eq: "a == b" => _);
        test!(expression, cmp_neq: "a != b" => _);
        test!(expression, cmp_leq: "a <= b" => _);
        test!(expression, cmp_geq: "a >= b" => _);
        test!(expression, cmp_gt: "a > b" => _);
        test!(expression, cmp_lt: "a < b" => _);
        test!(expression, neg: "-a" => _);

        test!(expression, expr: "-a + b < 3 * true && false / 2" => _);

        test!(expression, void_simple: "fn {}" => _);
        test!(expression, void_argument: "fn a: int { ret a + 1 }" => _);
    }

    mod parse_type {
        use super::*;
        use RuntimeType as RT;
        use TypeKind::*;

        test!(parse_type, type_void: "void" => Resolved(RT::Void));
        test!(parse_type, type_int: "int" => Resolved(RT::Int));
        test!(parse_type, type_float: "float" => Resolved(RT::Float));
        test!(parse_type, type_str: "str" => Resolved(RT::String));
        test!(parse_type, type_unknown_access: "a.A | int" => Union(_, _));
        // TODO(ed): This is controverisal
        test!(parse_type, type_unknown_access_call: "a.b().A | int" => Union(_, _));
        test!(parse_type, type_unknown: "blargh" => UserDefined(_));
        test!(parse_type, type_union: "int | int" => Union(_, _));
        test!(parse_type, type_question: "int?" => Union(_, _));
        test!(parse_type, type_union_and_question: "int | void | str?" => Union(_, _));

        test!(parse_type, type_fn_no_params: "fn ->" => Fn(_, _));
        test!(parse_type, type_fn_one_param: "fn int? -> bool" => Fn(_, _));
        test!(parse_type, type_fn_two_params: "fn int | void, int? -> str?" => Fn(_, _));
        test!(parse_type, type_fn_only_ret: "fn -> bool?" => Fn(_, _));

        test!(parse_type, type_tuple_one: "(int)" => Tuple(_));
        test!(parse_type, type_tuple_complex: "(int | float?, str, str,)" => Tuple(_));

        test!(parse_type, type_list_one: "[int]" => List(_));
        test!(parse_type, type_list_complex: "[int | float?]" => List(_));

        test!(parse_type, type_set_one: "{int}" => Set(_));
        test!(parse_type, type_set_complex: "{int | float?}" => Set(_));

        test!(parse_type, type_dict_one: "{int : int}" => Dict(_, _));
        test!(parse_type, type_dict_complex: "{int | float? : int | int | int?}" => Dict(_, _));
    }

    mod statement {
        use super::*;

        // NOTE(ed): Expressions are valid statements! :D
        test!(statement, statement_expression: "1 + 1" => _);
        test!(statement, statement_print: "print 1" => _);
        test!(statement, statement_mut_declaration: "a := 1 + 1" => _);
        test!(statement, statement_const_declaration: "a :: 1 + 1" => _);
        test!(statement, statement_mut_type_declaration: "a :int= 1 + 1" => _);
        test!(statement, statement_const_type_declaration: "a :int: 1 + 1" => _);
        test!(statement, statement_force_mut_type_declaration: "a :!int= 1 + 1" => _);
        test!(statement, statement_force_const_type_declaration: "a :!int: 1 + 1" => _);
        test!(statement, statement_if: "if 1 { print a }" => _);
        test!(statement, statement_if_else: "if 1 { print a } else { print b }" => _);
        test!(statement, statement_loop: "loop 1 { print a }" => _);
        test!(statement, statement_ret: "ret 1 + 1" => _);
        test!(statement, statement_ret_newline: "ret \n" => _);
        test!(statement, statement_unreach: "<!>" => _);
        test!(statement, statement_blob_empty: "A :: blob {}" => _);
        test!(statement, statement_blob_comma: "A :: blob { a: int, b: int }" => _);
        test!(statement, statement_blob_newline: "A :: blob { a: int\n b: int }" => _);
        test!(statement, statement_blob_comma_newline: "A :: blob { a: int,\n b: int }" => _);
        test!(statement, statement_assign: "a = 1" => _);
        test!(statement, statement_assign_index: "a.b = 1 + 2" => _);
        test!(statement, statement_add_assign: "a += 2" => _);
        test!(statement, statement_sub_assign: "a -= 2" => _);
        test!(statement, statement_mul_assign: "a *= 2" => _);
        test!(statement, statement_div_assign: "a /= 2" => _);
        test!(statement, statement_assign_call: "a().b() += 2" => _);
        test!(statement, statement_assign_call_index: "a.c().c.b /= 4" => _);
        test!(statement, statement_idek: "a!.c!.c.b()().c = 0" => _);
    }
}
