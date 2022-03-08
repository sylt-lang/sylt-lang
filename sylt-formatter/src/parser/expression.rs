use sylt_tokenizer::Token as T;

use crate::parser::{ParseErr, ParseErrType};

use super::{Context, ParseResult, Span};

/// An expression in sylt
#[derive(Debug)]
pub enum Expression {
    /// An integer value
    Int { span: Span, value: i64 },
    /// A floating point value
    Float { span: Span, value: f64 },
    /// A boolean value
    Bool { span: Span, value: bool },
    /// A string
    String { span: Span, value: String },
    /// Nil value (lua construct)
    Nil { span: Span },

    /// Negative expression
    ///
    /// `-value`
    Negative { span: Span, value: Box<Expression> },
    /// Negated expression
    ///
    /// `not value`
    Negated { span: Span, value: Box<Expression> },

    /// Add two values
    ///
    /// `lhs + rhs`
    Add {
        span: Span,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    /// Subtraction between two values
    ///
    /// `lhs - rhs`
    Sub {
        span: Span,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    /// Multiply two values
    ///
    /// `lhs * rhs`
    Mul {
        span: Span,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    /// Division between two values
    ///
    /// `lhs / rhs`
    Div {
        span: Span,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },

    /// Boolean and between values
    ///
    /// `lhs and rhs`
    And {
        span: Span,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    /// Boolean and between values
    ///
    /// `lhs and rhs`
    Or {
        span: Span,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },

    /// If values are equal
    ///
    /// `lhs == rhs`
    Equal {
        span: Span,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    /// If values are inequal
    ///
    /// `lhs != rhs`
    NotEqual {
        span: Span,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    /// If lhs is greater than rhs
    ///
    /// `lhs > rhs`
    Greater {
        span: Span,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    /// If lhs is greater than or equals rhs
    ///
    /// `lhs >= rhs`
    GreaterEqual {
        span: Span,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    /// If lhs is less than rhs
    ///
    /// `lhs < rhs`
    Less {
        span: Span,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    /// If lhs is less than or equals rhs
    ///
    /// `lhs <= rhs`
    LessEqual {
        span: Span,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    /// If lhs is contained within rhs, used in sets for instance
    ///
    /// `lhs in rhs`
    In {
        span: Span,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },

    /// Assert equality between lhs and rhs
    ///
    /// `lhs <=> rhs`
    AssertEq {
        span: Span,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
}

pub fn parse<'a>(ctx: Context<'a>) -> ParseResult<'a, Expression> {
    parse_precedence(ctx, Prec::No)
}

fn parse_precedence<'a>(ctx: Context<'a>, prec: Prec) -> ParseResult<'a, Expression> {
    // Initial value, e.g. a number value, assignable, ...
    let (mut ctx, mut expr) = prefix(ctx)?;

    while {
        let token = ctx.peek();
        prec <= precedence(token) && valid_infix(token)
    } {
        let (_ctx, _expr) = infix(ctx, expr)?;
        // assign to outer
        expr = _expr;
        ctx = _ctx;
    }
    Ok((ctx, expr))
}

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

/// Parse something that begins at the start of an expression.
fn prefix<'a>(ctx: Context<'a>) -> ParseResult<'a, Expression> {
    match ctx.peek() {
        h @ T::Minus | h @ T::Not => {
            let prefix_span = ctx.span();
            let (ctx, expr) = non_prefix(ctx.forward(1))?;
            let negated = match h {
                T::Minus => Expression::Negative {
                    span: prefix_span.start..expr_span(&expr).end,
                    value: Box::new(expr),
                },
                T::Not => Expression::Negated {
                    span: prefix_span.start..expr_span(&expr).end,
                    value: Box::new(expr),
                },
                _ => unreachable!(),
            };

            Ok((ctx, negated))
        }

        _ => non_prefix(ctx),
    }
}

/// Parse an expression that is not prefixed
fn non_prefix<'a>(ctx: Context<'a>) -> ParseResult<'a, Expression> {
    match ctx.peek() {
        //T::Fn | T::Pu => function(ctx),
        //T::If => if_expression(ctx),
        //T::Case => case_expression(ctx),

        //T::LeftParen => grouping_or_tuple(ctx),
        //T::LeftBracket => list(ctx),
        //T::LeftBrace => set_or_dict(ctx),
        T::Float(_) | T::Int(_) | T::Bool(_) | T::String(_) | T::Nil => value(ctx),

        // T::Identifier(_) => {
        //     let span = ctx.span();
        //
        //     // Do some probing
        //     let is_blob = match type_assignable(ctx) {
        //         Ok((ctx, _)) => matches!(ctx.token(), T::LeftBrace),
        //         _ => false,
        //     };
        //
        //     if is_blob {
        //         match blob(ctx) {
        //             Ok(x) => Ok(x),
        //             Err((ctx, errs)) => Err((skip_until!(ctx, T::RightBrace), errs)),
        //         }
        //     } else {
        //         let (ctx, assign) = assignable(ctx)?;
        //         Ok((ctx, Expression::new(span, Get(assign))))
        //     }
        // }

        _t => Err((
            ctx,
            ParseErr {
                err_type: ParseErrType::Undefined {
                    message: "Unexpected prefix token".to_string(),
                },
                inner_span: ctx.span().clone(),
            },
        )),
    }
}

fn value<'a>(ctx: Context<'a>) -> ParseResult<'a, Expression> {
    use Expression as E;

    let (ctx, token, span) = ctx.eat();
    let span = span.clone();

    Ok((
        ctx,
        match token {
            T::Float(value) => E::Float { value: *value, span },
            T::Bool(value) => E::Bool { value: *value, span },
            T::Int(value) => E::Int { value: *value, span },
            T::String(s) => E::String { value: s.clone(), span },
            T::Nil => E::Nil { span },
            _ => unreachable!(),
        },
    ))
}

fn valid_infix<'t>(token: &T) -> bool {
    matches!(
        token,
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
            | T::Arrow
            | T::Prime
            | T::LeftParen
            | T::LeftBracket
            | T::Dot
    )
}

fn infix<'t>(ctx: Context<'t>, lhs: Expression) -> ParseResult<'t, Expression> {
    use Expression::*;

    // If there is no precedence it's the start of an expression.
    // All valid operators have a precedence value that is differnt
    // from `Prec::no`.
    // match (ctx.peek(), precedence(ctx.peek_ahead(1))) {
    //     // The cool arrow syntax. For example: `a->b(2)` compiles to `b(a, 2)`.
    //     // #NotLikeOtherOperators
    //     (T::Arrow, _) => {
    //         return arrow_call(ctx, lhs);
    //     }
    //
    //     (T::Prime | T::LeftParen | T::LeftBracket | T::Dot, _) => {
    //         let (ctx, ass) = sub_assignable(
    //             ctx,
    //             Assignable {
    //                 span: ctx.span(),
    //                 kind: AssignableKind::Expression(Box::new(lhs.clone())),
    //             },
    //         )?;
    //         return Ok((ctx, Expression::new(ctx.span(), Get(ass))));
    //     }
    //     _ => {}
    // }

    // Parse an operator and a following expression
    // until we reach a token with higher precedence.
    //
    // The operator has to be checked before - this
    // removes an O(x^n).
    let (ctx, op, _span) = ctx.eat();

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
        | T::In => {}

        // Unknown infix operator.
        _ => {
            // raise_syntax_error!(ctx.prev(), "Not a valid infix operator");
            return Err((
                ctx,
                ParseErr {
                    err_type: ParseErrType::Undefined {
                        message: "Unexpected infix token".to_string(),
                    },
                    inner_span: ctx.span().clone(),
                },
            ));
        }
    };

    let (ctx, rhs) = parse_precedence(ctx, precedence(op).next())?;

    // Left and right of the operator.
    let lhs = Box::new(lhs);
    let rhs = Box::new(rhs);

    // Which expression kind to emit depends on the token.
    let expr = match op {
        // Simple arithmetic.
        T::Plus => Add { span: combine_expr_spans(&lhs, &rhs), lhs, rhs },
        T::Minus => Sub { span: combine_expr_spans(&lhs, &rhs), lhs, rhs },
        T::Star => Mul { span: combine_expr_spans(&lhs, &rhs), lhs, rhs },
        T::Slash => Div { span: combine_expr_spans(&lhs, &rhs), lhs, rhs },

        // Comparisons
        T::EqualEqual => Equal { span: combine_expr_spans(&lhs, &rhs), lhs, rhs },
        T::NotEqual => NotEqual { span: combine_expr_spans(&lhs, &rhs), lhs, rhs },
        T::Greater => Greater { span: combine_expr_spans(&lhs, &rhs), lhs, rhs },
        T::GreaterEqual => GreaterEqual { span: combine_expr_spans(&lhs, &rhs), lhs, rhs },
        T::Less => Less { span: combine_expr_spans(&lhs, &rhs), lhs, rhs },
        T::LessEqual => LessEqual { span: combine_expr_spans(&lhs, &rhs), lhs, rhs },
        T::In => In { span: combine_expr_spans(&lhs, &rhs), lhs, rhs },

        // Boolean operators
        T::And => And { span: combine_expr_spans(&lhs, &rhs), lhs, rhs },
        T::Or => Or { span: combine_expr_spans(&lhs, &rhs), lhs, rhs },

        // Assert equality
        T::AssertEqual => AssertEq { span: combine_expr_spans(&lhs, &rhs), lhs, rhs },

        // Unknown infix operator.
        _ => {
            return Err((
                ctx,
                ParseErr {
                    err_type: ParseErrType::Undefined {
                        message: "Unexpected infix operator".to_string(),
                    },
                    inner_span: ctx.span().clone(),
                },
            ))
        }
    };

    Ok((ctx, expr))
}

fn expr_span<'a>(expr: &'a Expression) -> &'a Span {
    match expr {
        Expression::Int { span, .. }
        | Expression::Float { span, .. }
        | Expression::Bool { span, .. }
        | Expression::String { span, .. }
        | Expression::Nil { span }
        | Expression::Negative { span, .. }
        | Expression::Negated { span, .. }
        | Expression::Sub { span, .. }
        | Expression::Div { span, .. }
        | Expression::Mul { span, .. }
        | Expression::And { span, .. }
        | Expression::Or { span, .. }
        | Expression::Equal { span, .. }
        | Expression::NotEqual { span, .. }
        | Expression::Greater { span, .. }
        | Expression::GreaterEqual { span, .. }
        | Expression::Less { span, .. }
        | Expression::LessEqual { span, .. }
        | Expression::In { span, .. }
        | Expression::AssertEq { span, .. }
        | Expression::Add { span, .. } => span,
    }
}

fn combine_expr_spans<'a>(first: &'a Expression, second: &'a Expression) -> Span {
    let first_span = expr_span(first);
    let second_span = expr_span(second);

    first_span.start..second_span.end
}

pub trait Next {
    fn next(&self) -> Self;
}

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
