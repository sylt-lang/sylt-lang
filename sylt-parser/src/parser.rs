use self::expression::expression;
use self::statement::outer_statement;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::path::{Path, PathBuf};
use sylt_common::error::Error;
use sylt_common::rc::Rc;
use sylt_common::Type as RuntimeType;
use sylt_tokenizer::{PlacedToken, Token, ZERO_SPAN, file_to_tokens};

pub mod expression;
pub mod statement;
pub use self::expression::{Expression, ExpressionKind};
pub use self::statement::{Statement, StatementKind};

pub use sylt_tokenizer::Span;

type T = Token;

pub trait Next {
    fn next(&self) -> Self;
}

pub trait Numbered {
    fn to_number(&self) -> usize;
}

/// Contains modules.
#[derive(Debug, Clone)]
pub struct AST {
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
    /// An arrow function call. `a -> f' b`
    ArrowCall(Box<Expression>, Box<Assignable>, Vec<Expression>),
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

type ParseResult<'t, T> = Result<(Context<'t>, T), (Context<'t>, Vec<Error>)>;

/// Keeps track of where the parser is currently parsing.
#[derive(Debug, Copy, Clone)]
pub struct Context<'a> {
    pub skip_newlines: bool,
    /// All tokens to be parsed.
    pub tokens: &'a [Token],
    /// The corresponding span for each token. Matches 1:1 with the tokens.
    pub spans: &'a [Span],
    /// The index of the curren token in the token slice.
    pub curr: usize,
    /// The file we're currently parsing.
    pub file: &'a Path,
}

impl<'a> Context<'a> {
    fn new(tokens: &'a [Token], spans: &'a [Span], file: &'a Path) -> Self {
        Self {
            skip_newlines: false,
            tokens,
            spans,
            curr: 0,
            file,
        }
    }

    /// Get a [Span] representing the current location of the parser.
    fn span(&self) -> Span {
        *self.peek().1
    }

    /// Move to the next nth token.
    fn skip(&self, n: usize) -> Self {
        let mut new = *self;
        new.curr += n;
        while self.skip_newlines && matches!(new.token(), T::Newline) {
            new.curr += 1;
        }
        new
    }

    /// Signals that newlines should be skipped until [pop_skip_newlines].
    fn push_skip_newlines(&self, skip_newlines: bool) -> (Self, bool) {
        let mut new = *self;
        new.skip_newlines = skip_newlines;
        // If currently on a newline token - we want to skip it.
        (new.skip(0), self.skip_newlines)
    }

    /// Reset to old newline skipping state.
    fn pop_skip_newlines(&self, skip_newlines: bool) -> Self {
        let mut new = *self;
        new.skip_newlines = skip_newlines;
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

    /// Return the current [Token] and [Span].
    fn peek(&self) -> (&Token, &Span) {
        let token = self.tokens.get(self.curr).unwrap_or(&T::EOF);
        let span = self.spans.get(self.curr).unwrap_or(&ZERO_SPAN);
        (token, span)
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
#[macro_export]
macro_rules! syntax_error {
    ($ctx:expr, $( $msg:expr ),* ) => {
        {
            let msg = format!($( $msg ),*).into();
            Error::SyntaxError {
                file: $ctx.file.to_path_buf(),
                span: $ctx.span(),
                message: Some(msg),
            }
        }
    };
}

/// Raise a syntax error at the current token with a message.
#[macro_export]
macro_rules! raise_syntax_error {
    ($ctx:expr, $( $msg:expr ),* ) => {
        return Err(($ctx.skip(1), vec![syntax_error!($ctx, $( $msg ),*)]))
    };
}

/// Eat any one of the specified tokens and raise a syntax error if none is found.
#[macro_export]
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

/// Parse an [AssignableKind::Call]
fn assignable_call<'t>(ctx: Context<'t>, callee: Assignable) -> ParseResult<'t, Assignable> {
    let span = ctx.span();
    let primer = matches!(ctx.token(), T::Prime); // `f' 1, 2`
    let mut ctx = expect!(
        ctx,
        T::Prime | T::LeftParen,
        "Expected '(' or '!' when calling function"
    );
    let mut args = Vec::new();

    // Arguments
    loop {
        match (ctx.token(), primer) {
            // Done with arguments.
            (T::EOF, _)
            | (T::Else, _)
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

    let ctx = if !primer {
        expect!(ctx, T::RightParen, "Expected ')' after calling function")
    } else {
        ctx
    };

    use AssignableKind::Call;
    let result = Assignable {
        span,
        kind: Call(Box::new(callee), args),
    };
    sub_assignable(ctx, result)
}

/// Parse an [AssignableKind::Index].
fn assignable_index<'t>(ctx: Context<'t>, indexed: Assignable) -> ParseResult<'t, Assignable> {
    let span = ctx.span();
    let mut ctx = expect!(ctx, T::LeftBracket, "Expected '[' when indexing");

    let (_ctx, expr) = expression(ctx)?;
    ctx = _ctx; // assign to outer
    let ctx = expect!(ctx, T::RightBracket, "Expected ']' after index");

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
            },
        )
    } else {
        raise_syntax_error!(
            ctx,
            "Assignable expressions have to start with an identifier"
        );
    };

    let access = Assignable {
        span: ctx.span(),
        kind: Access(Box::new(accessed), ident),
    };
    sub_assignable(ctx, access)
}

/// Parse a (maybe empty) "sub-assignable", i.e. either a call or indexable.
fn sub_assignable<'t>(ctx: Context<'t>, assignable: Assignable) -> ParseResult<'t, Assignable> {
    match ctx.token() {
        T::Prime | T::LeftParen => assignable_call(ctx, assignable),
        T::LeftBracket => assignable_index(ctx, assignable),
        T::Dot => assignable_dot(ctx, assignable),
        _ => Ok((ctx, assignable)),
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

/// Parses a file's tokens. Returns a list of files it refers to (via `use`s) and
/// the parsed statements.
///
/// # Errors
///
/// Returns any errors that occured when parsing the file. Basic error
/// continuation is performed, so errored statements are skipped until a newline
/// or EOF.
fn module(path: &Path, token_stream: &[PlacedToken]) -> (Vec<PathBuf>, Result<Module, Vec<Error>>) {
    let tokens: Vec<_> = token_stream.iter().map(|p| p.token.clone()).collect();
    let spans: Vec<_> = token_stream.iter().map(|p| p.span).collect();
    let mut ctx = Context::new(&tokens, &spans, path);
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
                span: Span::zero(),
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
        Err(e) => {
            return vec![if matches!(e.kind(), std::io::ErrorKind::NotFound) {
                Error::FileNotFound(file.to_path_buf())
            } else {
                Error::IOError(Rc::new(e))
            }]
        }
    };
    let mut errs = Vec::new();
    // Search line by line and push any errors we find.
    for (i, line) in s.lines().enumerate() {
        if line.starts_with("<<<<<<<") {
            errs.push(Error::GitConflictError {
                file: file.to_path_buf(),
                span: Span {
                    line: i + 1,
                    col_start: 0,
                    col_end: "<<<<<<<".len(),
                }
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
pub fn tree(path: &Path) -> Result<AST, Vec<Error>> {
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
                let (mut next, result) = module(&file, &tokens);
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
        Ok(AST { modules })
    } else {
        Err(errors)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[macro_export]
    macro_rules! test {
        ($f:ident, $name:ident: $str:expr => $ans:pat) => {
            #[test]
            fn $name() {
                let token_stream = ::sylt_tokenizer::string_to_tokens($str);
                let tokens: Vec<_> = token_stream.iter().map(|p| p.token.clone()).collect();
                let spans: Vec<_> = token_stream.iter().map(|p| p.span).collect();
                let path = ::std::path::PathBuf::from(stringify!($name));
                let result = $f($crate::Context::new(&tokens, &spans, &path));
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

    #[macro_export]
    macro_rules! fail {
        ($f:ident, $name:ident: $str:expr => $ans:pat) => {
            #[test]
            fn $name() {
                let token_stream = ::sylt_tokenizer::string_to_tokens($str);
                let tokens: Vec<_> = token_stream.iter().map(|p| p.token.clone()).collect();
                let spans: Vec<_> = token_stream.iter().map(|p| p.span).collect();
                let path = ::std::path::PathBuf::from(stringify!($name));
                let result = $f($crate::Context::new(&tokens, &spans, &path));
                assert!(
                    result.is_err(),
                    "\nSyntax tree test parsed - when it should have failed - for:\n{}\n",
                    $str,
                );
                let (_, result) = result.unwrap_err();
                assert!(
                    matches!(result, $ans),
                    "\nExpected: {}, but got: {:?}",
                    stringify!($ans),
                    result
                );
            }
        };
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
}
