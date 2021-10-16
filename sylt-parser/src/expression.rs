use sylt_common::error::Error;

use crate::statement::block;

use super::*;

#[derive(Debug, Clone, PartialEq)]
pub enum ComparisonKind {
    Equals,
    NotEquals,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    In,
}

/// The different kinds of [Expression]s.
///
/// Expressions are recursive and evaluate to some kind of value.
#[derive(Debug, Clone, PartialEq)]
pub enum ExpressionKind {
    /// Read from an [Assignable]. Variables, function calls, module accesses,
    /// blob fields, list indexing, tuple indexing and dict indexing end up here.
    Get(Assignable),

    /// A type as a value
    TypeConstant(Type),

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

    Comparison(Box<Expression>, ComparisonKind, Box<Expression>),

    /// `a <=> b`
    AssertEq(Box<Expression>, Box<Expression>),

    /// `a && b`
    And(Box<Expression>, Box<Expression>),
    /// `a || b`
    Or(Box<Expression>, Box<Expression>),
    /// `!a`
    Not(Box<Expression>),

    Parenthesis(Box<Expression>),

    /// Inline If-statements
    IfExpression {
        condition: Box<Expression>,
        pass: Box<Expression>,
        fail: Box<Expression>,
    },

    /// Functions and closures.
    Function {
        name: String,
        params: Vec<(Identifier, Type)>,
        ret: Type,

        body: Box<Statement>,
    },
    /// A blob instantiation.
    Blob {
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

impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

/// Parse an [ExpressionKind::Function]: `fn a: int, b: bool -> bool <statement>`
fn function<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
    use RuntimeType::Void;
    use TypeKind::Resolved;

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
                if name == "self" {
                    raise_syntax_error!(ctx, "\"self\" is a reserved identifier");
                }
                ctx = expect!(ctx.skip(1), T::Colon, "Expected ':' after parameter name");
                // Parameter type
                let (_ctx, param) = parse_type(ctx)?;
                ctx = _ctx; // assign to outer

                params.push((ident, param));

                ctx = if matches!(ctx.token(), T::Comma | T::Do | T::Arrow | T::LeftBrace) {
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
                    Type {
                        // If we couldn't parse the return type, we assume `-> Void`.
                        span: ctx.span(),
                        kind: Resolved(Void),
                    }
                };
            }

            T::LeftBrace | T::Do => {
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

    // Parse the function statement.
    let (ctx, mut statements) = block(ctx)?;

    // If the return type isn't void, check for and apply implicit returns.
    if !matches!(ret.kind, Resolved(Void)) {
        // If the last statement is an expression statement,
        // replace it with a return statement.
        let last_statement = statements.pop();
        if let Some(Statement {
            span,
            kind: StatementKind::StatementExpression { value },
            comments,
        }) = last_statement
        {
            statements.push(Statement {
                span,
                kind: StatementKind::Ret { value },
                comments
            });
        } else if let Some(statement) = last_statement {
            statements.push(statement);
        }
    }

    use ExpressionKind::Function;
    let function = Function {
        name: "lambda".into(),
        params,
        ret,
        body: Box::new(Statement {
            span: ctx.span(),
            kind: StatementKind::Block { statements },
            comments: Vec::new(),
        }),
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
    use Prec;

    match token {
        T::LeftBracket | T::Dot | T::LeftParen => Prec::Index,

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
    use ExpressionKind::*;
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
    use ExpressionKind::{Get, TypeConstant};

    match ctx.token() {
        T::Fn => function(ctx),

        T::LeftParen => grouping_or_tuple(ctx),
        T::LeftBracket => list(ctx),
        T::LeftBrace => set_or_dict(ctx),

        T::Colon => {
            let span = ctx.span();
            let (ctx, ty) = parse_type(ctx.skip(1))?;
            Ok((
                ctx,
                Expression {
                    span,
                    kind: TypeConstant(ty),
                },
            ))
        }

        T::Float(_) | T::Int(_) | T::Bool(_) | T::String(_) | T::Nil => value(ctx),
        T::Minus | T::Not => unary(ctx),

        T::Identifier(_) => {
            let span = ctx.span();
            match (blob(ctx), assignable(ctx)) {
                (Ok(result), _) => Ok(result),
                (_, Ok((ctx, assign))) => Ok((
                    ctx,
                    Expression {
                        span,
                        kind: Get(assign),
                    },
                )),
                (Err((_, mut blob_errs)), Err((_, mut ass_errs))) => {
                    let errs = vec![
                        syntax_error!(ctx, "Neither a blob instantiation or an identifier - check the two errors below"),
                        blob_errs.remove(0),
                        ass_errs.remove(0),
                    ];
                    return Err((ctx, errs));
                }
            }
        }

        t => {
            raise_syntax_error!(ctx, "No valid expression starts with '{:?}'", t);
        }
    }
}

/// Parse a unary operator followed by an expression, e.g. `-5`.
fn unary<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
    use ExpressionKind::{Neg, Not};

    let (op, span, ctx) = ctx.eat();
    let (ctx, expr) = parse_precedence(ctx, Prec::Factor)?;
    let expr = Box::new(expr);

    let kind = match op {
        T::Minus => Neg(expr),
        T::Not => Not(expr),

        _ => {
            raise_syntax_error!(ctx, "Invalid unary operator");
        }
    };
    Ok((ctx, Expression { span, kind }))
}

fn if_expression<'t>(ctx: Context<'t>, lhs: &Expression) -> ParseResult<'t, Expression> {
    let span = ctx.span();
    let ctx = expect!(ctx, T::If, "Expected 'if' at start of if-expression");

    use ExpressionKind::*;
    let (ctx, condition) = parse_precedence(ctx, Prec::No)?;

    let ctx = expect!(
        ctx,
        T::Else,
        "Expected 'else' after if-expression condition"
    );
    let (ctx, rhs) = parse_precedence(ctx, Prec::No)?;
    let condition = Box::new(condition.clone());
    let pass = Box::new(lhs.clone());
    let fail = Box::new(rhs);
    Ok((
        ctx,
        Expression {
            span,
            kind: IfExpression {
                condition,
                pass,
                fail,
            },
        },
    ))
}

fn arrow_call<'t>(ctx: Context<'t>, lhs: &Expression) -> ParseResult<'t, Expression> {
    let ctx = expect!(ctx, T::Arrow, "Expected '->' in arrow function call");
    let (ctx, rhs) = expression(ctx)?;

    use ExpressionKind::*;
    use AssignableKind::{Call, ArrowCall};

    fn prepend_expresion<'t>(ctx: Context<'t>, lhs: Expression, rhs: Expression) -> ParseResult<'t, Expression> {
        let span = ctx.span();
        let kind = match rhs.kind {
            Get(Assignable {
                kind: Call(callee, args),
                ..
            }) => Get(Assignable {
                kind: ArrowCall(Box::new(lhs), callee, args),
                span: rhs.span,
            }),

            Get(Assignable {
                kind: ArrowCall(pre, callee, args),
                ..
            }) => {
                let (_, pre) = prepend_expresion(ctx, lhs, *pre)?;
                Get(Assignable {
                    kind: ArrowCall(Box::new(pre), callee, args),
                    span: rhs.span,
                })
            }

            _ => { raise_syntax_error!(ctx, "Expected a call-expression after '->'"); }
        };
        Ok((ctx, Expression { span, kind }))
    }

    prepend_expresion(ctx, lhs.clone(), rhs)
}

/// Parse an expression starting from an infix operator. Called by `parse_precedence`.
fn infix<'t>(ctx: Context<'t>, lhs: &Expression) -> ParseResult<'t, Expression> {
    use ComparisonKind::*;
    use ExpressionKind::*;

    // If there is no precedence it's the start of an expression.
    // All valid operators have a precedence value that is differnt
    // from `Prec::no`.
    match (ctx.token(), precedence(ctx.skip(1).token())) {
        (T::If, Prec::No) => {
            return if_expression(ctx, lhs);
        }
        // The cool arrow syntax. For example: `a->b(2)` compiles to `b(a, 2)`.
        // #NotLikeOtherOperators
        (T::Arrow, _) => {
            return arrow_call(ctx, lhs);
        }

        (T::Prime | T::LeftParen | T::LeftBracket | T::Dot, _) => {
            let (ctx, ass) = sub_assignable(ctx, Assignable {
                span: ctx.span(),
                kind: AssignableKind::Expression(Box::new(lhs.clone()))
            })?;
            return Ok((ctx, Expression {
                span: ctx.span(),
                kind: Get(ass),
            }));
        }
        _ => {}
    }

    // Parse an operator and a following expression
    // until we reach a token with higher precedence.
    //
    // The operator has to be checked before - this
    // removes an O(x^n).
    let (op, span, ctx) = ctx.eat();

    match op {
        T::Plus
        | T::Minus
        | T::Star
        | T::Slash
        | T::EqualEqual
        | T::NotEqual
        | T::Greater
        | T::GreaterEqual
        | T::Less
        | T::LessEqual

        | T::And
        | T::Or

        | T::AssertEqual

        | T::In
        => {}

        // Unknown infix operator.
        _ => {
            return Err((ctx, Vec::new()));
        }
    };


    let (ctx, rhs) = parse_precedence(ctx, precedence(op).next())?;

    // Left and right of the operator.
    let lhs = Box::new(lhs.clone());
    let rhs = Box::new(rhs);

    // Which expression kind to emit depends on the token.
    let kind = match op {
        // Simple arithmetic.
        T::Plus => Add(lhs, rhs),
        T::Minus => Sub(lhs, rhs),
        T::Star => Mul(lhs, rhs),
        T::Slash => Div(lhs, rhs),

        // Comparisons
        T::EqualEqual => Comparison(lhs, Equals, rhs),
        T::NotEqual => Comparison(lhs, NotEquals, rhs),
        T::Greater => Comparison(lhs, Greater, rhs),
        T::GreaterEqual => Comparison(lhs, GreaterEqual, rhs),
        T::Less => Comparison(lhs, Less, rhs),
        T::LessEqual => Comparison(lhs, LessEqual, rhs),
        T::In => Comparison(lhs, In, rhs),

        // Boolean operators.
        T::And => And(lhs, rhs),
        T::Or => Or(lhs, rhs),

        T::AssertEqual => AssertEq(lhs, rhs),

        // Unknown infix operator.
        _ => {
            unreachable!();
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
    let ctx = expect!(ctx, T::LeftParen, "Expected '('");
    let (mut ctx, skip_newlines) = ctx.push_skip_newlines(true);

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

    let ctx = ctx.pop_skip_newlines(skip_newlines);
    let ctx = expect!(ctx, T::RightParen, "Expected ')'");

    use ExpressionKind::{Parenthesis, Tuple};
    let result = if is_tuple {
        Expression {
            span,
            kind: Tuple(exprs),
        }
    } else {
        Expression {
            span,
            kind: Parenthesis(Box::new(exprs.remove(0))),
        }
    };
    Ok((ctx, result))
}

/// Parse a blob instantiation, e.g. `A { b: 55 }`.
fn blob<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
    let span = ctx.span();
    let (ctx, blob) = assignable(ctx)?;
    let ctx = expect!(ctx, T::LeftBrace, "Expected '{{' after blob name");
    let (mut ctx, skip_newlines) = ctx.push_skip_newlines(true);

    // The blob's fields.
    let mut fields = Vec::new();
    loop {
        match ctx.token() {
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

                if !matches!(ctx.token(), T::Comma | T::RightBrace) {
                    raise_syntax_error!(
                        ctx,
                        "Expected a field delimiter ',' - but got {:?}",
                        ctx.token()
                    );
                }
                ctx = ctx.skip_if(T::Comma);

                fields.push((name, expr));
            }

            t => {
                raise_syntax_error!(ctx, "Unexpected token ('{:?}') in blob initalizer", t);
            }
        }
    }

    let ctx = ctx.pop_skip_newlines(skip_newlines);
    let ctx = expect!(ctx, T::RightBrace, "Expected '}}' after blob initalizer");

    if matches!(ctx.token(), T::Else) {
        raise_syntax_error!(ctx, "Parsed a blob not an if-statement");
    }

    use ExpressionKind::Blob;
    Ok((
        ctx,
        Expression {
            span,
            kind: Blob { blob, fields },
        },
    ))
}

// Parse a list expression, e.g. `[1, 2, a(3)]`
fn list<'t>(ctx: Context<'t>) -> ParseResult<'t, Expression> {
    let span = ctx.span();
    let ctx = expect!(ctx, T::LeftBracket, "Expected '['");
    let (mut ctx, skip_newlines) = ctx.push_skip_newlines(true);

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
            }
        }
    }

    let ctx = ctx.pop_skip_newlines(skip_newlines);
    let ctx = expect!(ctx, T::RightBracket, "Expected ']'");
    use ExpressionKind::List;
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
    let ctx = expect!(ctx, T::LeftBrace, "Expected '{{'");
    let (mut ctx, skip_newlines) = ctx.push_skip_newlines(true);

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
                ctx = ctx.skip(1).skip_if(T::Comma);
            }

            // Something that's part of an inner expression.
            _ => {
                // Parse the expression.
                let (_ctx, expr) = detail_if_error!(expression(ctx), "failed to parse dict or set")?;
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

                if !matches!(ctx.token(), T::Comma | T::RightBrace) {
                    raise_syntax_error!(
                        ctx,
                        "Expected an element delimiter ',' but got {:?}",
                        ctx.token()
                    );
                }
                ctx = ctx.skip_if(T::Comma);
            }
        }
    }

    let ctx = ctx.pop_skip_newlines(skip_newlines);
    let ctx = expect!(ctx, T::RightBrace, "Expected '}}'");

    use ExpressionKind::{Dict, Set};
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
    parse_precedence(ctx, Prec::No)
}

// NOTE(ed): It's really hard to write good tests, Rust refuses to deref the boxes
// automatically.
//
// Faulty syntax should be tested in the small language tests.
#[cfg(test)]
mod test {
    use super::ExpressionKind::*;
    use crate::expression;
    use crate::expression::ComparisonKind;
    use crate::{test, fail};
    use crate::Assignable;
    use crate::AssignableKind::*;

    test!(expression, value: "0" => Int(0));
    test!(expression, add: "0 + 1.0" => Add(_, _));
    test!(expression, mul: "\"abc\" * \"abc\"" => Mul(_, _));
    test!(expression, ident: "a" => Get(Assignable { kind: Read(_), .. }));
    test!(expression, access: "a.b" => Get(Assignable { kind: Access(_, _), .. }));
    test!(expression, index_ident: "a[a]" => Get(Assignable { kind: Index(_, _), .. }));
    test!(expression, index_expr: "a[1 + 2 + 3]" => Get(Assignable { kind: Index(_, _), .. }));
    test!(expression, grouping: "(0 * 0) + 1" => Add(_, _));
    test!(expression, grouping_one: "(0)" => Parenthesis(_));
    test!(expression, tuple: "(0, 0)" => Tuple(_));
    test!(expression, tuple_one: "(0,)" => Tuple(_));
    test!(expression, tuple_empty: "()" => Tuple(_));
    test!(expression, list: "[0, 0]" => List(_));
    test!(expression, set: "{1, 1}" => Set(_));
    test!(expression, dict: "{1: 1}" => Dict(_));
    test!(expression, zero_set: "{}" => Set(_));
    test!(expression, zero_dict: "{:}" => Dict(_));

    test!(expression, in_list: "a in [1, 2, 3]" => Comparison(_, ComparisonKind::In, _));
    test!(expression, in_set: "2 in {1, 1, 2}" => Comparison(_, ComparisonKind::In, _));
    test!(expression, in_grouping: "1 + 2 in b" => Add(_, _));
    test!(expression, in_grouping_paren: "(1 + 2) in b" => Comparison(_, ComparisonKind::In, _));

    test!(expression, call_simple_paren: "a()" => Get(_));
    test!(expression, call_call: "a()()" => Get(_));
    test!(expression, call_simple_bang: "a'" => Get(_));
    test!(expression, call_chaining_paren: "a().b" => Get(_));
    test!(expression, call_chaining_bang: "a'.b" => Get(_));
    test!(expression, call_args_paren: "a(1, 2, 3)" => Get(_));
    test!(expression, call_args_bang: "a' 1, 2, 3" => Get(_));
    test!(expression, call_args_chaining_paren: "a(1, 2, 3).b" => Get(_));
    test!(expression, call_args_chaining_paren_trailing: "a(1, 2, 3,).b" => Get(_));
    test!(expression, assignable_index: "a[0]" => Get(_));
    test!(expression, assignable_index_twice: "a[0][1]" => Get(_));
    test!(expression, assignable_mixed: "a[0]()" => Get(_));
    test!(expression, assignable_mixed_many: "a()[0]()[1]()()()[2][3]" => Get(_));
    test!(expression, assignable_expression: "[0][0]" => Get(_));
    test!(expression, assignable_expression_many: "[0][0][0][0][0]" => Get(_));
    test!(expression, assignable_expression_blob: "A {}.a" => Get(_));
    test!(expression, assignable_expression_fn: "(fn do 2 end)()" => Get(_));
    test!(expression, assignable_expression_fn_no_paren: "fn do 2 end()" => Get(_));
    test!(expression, assignable_expression_dict: "{1:2}[1]" => Get(_));

    // TODO(ed): This is controverisal
    test!(expression, call_args_chaining_bang: "a' 1, 2, 3 .b" => Get(_));
    test!(expression, call_args_chaining_bang_trailing: "a' 1, 2, 3, .b" => Get(_));

    test!(expression, call_arrow: "1 + 0 -> a' 2, 3" => Add(_, _));
    test!(expression, call_arrow_grouping: "(1 + 0) -> a' 2, 3" => Get(_));

    test!(expression, blob: "A { a: 1 + 1, b: nil }" => Blob { .. });
    test!(expression, blob_more: "A { a: 2, \n c: 2 }" => Blob { .. });
    test!(expression, blob_empty: "A {}" => Blob { .. });

    test!(expression, simple: "fn -> do end" => _);
    test!(expression, argument: "fn a: int -> int do ret a + 1 end" => _);

    test!(expression, booleans: "true and false or not false" => _);
    test!(expression, bool_and: "true and a" => _);
    test!(expression, bool_or: "a or false" => _);
    test!(expression, bool_neg: "not a" => _);
    test!(expression, bool_neg_multiple: "not a and b" => _);
    test!(expression, bool_neg_multiple_rev: "a and not b" => _);

    test!(expression, cmp_eq: "a == b" => _);
    test!(expression, cmp_neq: "a != b" => _);
    test!(expression, cmp_leq: "a <= b" => _);
    test!(expression, cmp_geq: "a >= b" => _);
    test!(expression, cmp_gt: "a > b" => _);
    test!(expression, cmp_lt: "a < b" => _);
    test!(expression, neg: "-a" => _);

    test!(expression, expr: "-a + b < 3 * true and false / 2" => _);

    test!(expression, type_expr_int: ":int" => _);
    test!(expression, type_expr_void: ":void" => _);
    test!(expression, type_expr_float: ":float" => _);
    test!(expression, type_expr_str: ":str" => _);
    test!(expression, type_expr_custom: ":A" => _);
    test!(expression, type_expr_custom_chaining: ":A.b.C" => _);

    test!(expression, void_simple: "fn do end" => _);
    test!(expression, void_argument: "fn a: int do ret a + 1 end" => _);

    test!(expression, if_expr: "a if b else c" => IfExpression { .. });
    test!(expression, if_expr_more: "1 + 1 + 1 if b else 2 + 2 + 2" => IfExpression { .. });

    fail!(expression, fn_self_arg: "fn self: int do 1 end" => _);
}

impl PrettyPrint for Expression {
    fn pretty_print(&self, f: &mut std::fmt::Formatter<'_>, indent: usize) -> std::fmt::Result {
        use ExpressionKind as EK;
        write_indent(f, indent)?;
        match &self.kind {
            EK::Get(e) => {
                write!(f, "Get ")?;
                e.pretty_print(f, indent)?;
                write!(f, "\n")?;
            }
            EK::TypeConstant(ty) => {
                write!(f, "Type {}\n", ty)?;
            }
            EK::Add(a, b) => {
                write!(f, "Add\n")?;
                a.pretty_print(f, indent + 1)?;
                b.pretty_print(f, indent + 1)?;
            }
            EK::Sub(a, b) => {
                write!(f, "Sub\n")?;
                a.pretty_print(f, indent + 1)?;
                b.pretty_print(f, indent + 1)?;
            }
            EK::Mul(a, b) => {
                write!(f, "Mul\n")?;
                a.pretty_print(f, indent + 1)?;
                b.pretty_print(f, indent + 1)?;
            }
            EK::Div(a, b) => {
                write!(f, "Div\n")?;
                a.pretty_print(f, indent + 1)?;
                b.pretty_print(f, indent + 1)?;
            }
            EK::Neg(a) => {
                write!(f, "Neg\n")?;
                a.pretty_print(f, indent + 1)?;
            }
            EK::Comparison(a, k, b) => {
                write!(f, "Comparsion {:?}\n", k)?;
                a.pretty_print(f, indent + 1)?;
                b.pretty_print(f, indent + 1)?;
            }
            EK::AssertEq(a, b) => {
                write!(f, "AssertEq\n")?;
                a.pretty_print(f, indent + 1)?;
                b.pretty_print(f, indent + 1)?;
            }
            EK::And(a, b) => {
                write!(f, "And\n")?;
                a.pretty_print(f, indent + 1)?;
                b.pretty_print(f, indent + 1)?;
            }
            EK::Or(a, b) => {
                write!(f, "Or\n")?;
                a.pretty_print(f, indent + 1)?;
                b.pretty_print(f, indent + 1)?;
            }
            EK::Not(a) => {
                write!(f, "Not\n")?;
                a.pretty_print(f, indent + 1)?;
            }
            EK::Parenthesis(expr) => {
                write!(f, "Paren\n")?;
                expr.pretty_print(f, indent + 1)?;
            }
            EK::IfExpression { condition, pass, fail } => {
                write!(f, "IfExpression\n")?;
                write_indent(f, indent)?;
                write!(f, "condition:\n")?;
                condition.pretty_print(f, indent + 1)?;
                write_indent(f, indent)?;
                write!(f, "pass:\n")?;
                pass.pretty_print(f, indent + 1)?;
                write_indent(f, indent)?;
                write!(f, "fail:\n")?;
                fail.pretty_print(f, indent + 1)?;
            }
            EK::Function { name, params, ret, body } => {
                write!(f, "Fn {} ", name)?;
                for (i, (name, ty)) in params.iter().enumerate() {
                    if i != 0 { write!(f, ", ")?; }
                    write!(f, "{}: {}", name.name, ty)?;
                }
                write!(f, " -> {}", ret)?;
                write!(f, "\n")?;
                body.pretty_print(f, indent + 1)?;
            }
            EK::Blob { blob, fields } => {
                write!(f, "Blob ")?;
                blob.pretty_print(f, indent + 1)?;
                write!(f, "\n")?;
                for (field, value) in fields.iter() {
                    write_indent(f, indent)?;
                    write!(f, ".{}:\n", field)?;
                    value.pretty_print(f, indent + 1)?;
                }
            }
            EK::Tuple(values) => {
                write!(f, "Tuple\n")?;
                values.iter().try_for_each(|v| v.pretty_print(f, indent + 1))?;
            }
            EK::List(values) => {
                write!(f, "List\n")?;
                values.iter().try_for_each(|v| v.pretty_print(f, indent + 1))?;
            }
            EK::Set(values) => {
                write!(f, "Set\n")?;
                values.iter().try_for_each(|v| v.pretty_print(f, indent + 1))?;
            }
            EK::Dict(values) => {
                write!(f, "Dict\n")?;
                values.iter().try_for_each(|v| v.pretty_print(f, indent + 1))?;
            }
            EK::Float(_)
            | EK::Int(_)
            | EK::Str(_)
            | EK::Bool(_)
            | EK::Nil => { write!(f, "{:?}\n", self.kind)?; }
        }
        Ok(())
    }
}

