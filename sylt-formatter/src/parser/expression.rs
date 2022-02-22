use sylt_tokenizer::Token as T;

use super::{Context, ParseResult, Prec, Span};

/// An expression in sylt
#[derive(Debug)]
pub enum Expression<'a> {
    /// An integer value
    Int(i64, &'a Span),

    /// A floating point value
    Float(f64, &'a Span),

    /// A boolean value
    Bool(bool, &'a Span),

    /// A string
    String(String, &'a Span),

    /// Nil value (lua construct)
    Nil(&'a Span),

    /// Negated expression
    Negation(Box<Expression<'a>>, &'a Span),

    /// The sum of multiple values
    Sum(Vec<Expression<'a>>, &'a Span),

    /// The product of multiple values
    Product(Vec<Expression<'a>>, &'a Span),
}

impl<'a> Expression<'a> {
    pub fn parse(ctx: Context<'a>) -> ParseResult<'a, Expression<'a>> {
        Self::parse_precedence(ctx, Prec::No)
    }

    fn parse_precedence(ctx: Context<'a>, prec: Prec) -> ParseResult<'a, Expression<'a>> {
        // Initial value, e.g. a number value, assignable, ...
        let (mut expr, mut ctx) = prefix(ctx)?;

        while {
            let token = ctx.peek();
            prec <= precedence(token) && valid_infix(token)
        } {
            let (_expr, _ctx) = infix(ctx, &expr)?;
            // assign to outer
            expr = _expr;
            ctx = _ctx;
        }
        Ok((expr, ctx))
    }

    fn parse_prefix(ctx: Context<'a>) -> ParseResult<'a, Option<Expression<'a>>> {
        todo!()
    }

    fn parse_infix(ctx: Context<'a>) -> ParseResult<'a, Expression<'a>> {
        todo!()
    }
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
        //T::Fn | T::Pu => function(ctx),
        //T::If => if_expression(ctx),
        //T::Case => case_expression(ctx),

        //T::LeftParen => grouping_or_tuple(ctx),
        //T::LeftBracket => list(ctx),
        //T::LeftBrace => set_or_dict(ctx),
        T::Float(_) | T::Int(_) | T::Bool(_) | T::String(_) | T::Nil => value(ctx),
        //T::Minus | T::Not => unary(ctx),

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
        t => {
            panic!()
            // raise_syntax_error!(ctx, "No valid expression starts with '{:?}'", t);
        }
    }
}

fn value<'a>(ctx: Context<'a>) -> ParseResult<'a, Expression> {
    use Expression as E;

    let (ctx, token, span) = ctx.eat();

    Ok((
        match token {
            T::Float(v) => E::Float(*v, span),
            T::Bool(v) => E::Bool(*v, span),
            T::Int(v) => E::Int(*v, span),
            T::String(s) => E::String(s.clone(), span),
            T::Nil => E::Nil(span),
            _ => unreachable!(),
        },
        ctx,
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

fn infix<'t>(ctx: Context<'t>, lhs: &Expression) -> ParseResult<'t, Expression<'t>> {
    // // If there is no precedence it's the start of an expression.
    // // All valid operators have a precedence value that is differnt
    // // from `Prec::no`.
    // match (ctx.token(), precedence(ctx.skip(1).token())) {
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
    //
    // // Parse an operator and a following expression
    // // until we reach a token with higher precedence.
    // //
    // // The operator has to be checked before - this
    // // removes an O(x^n).
    // let (op, span, ctx) = ctx.eat();
    //
    // match op {
    //     T::Plus
    //     | T::Minus
    //     | T::Star
    //     | T::Slash
    //     | T::EqualEqual
    //     | T::NotEqual
    //     | T::Greater
    //     | T::GreaterEqual
    //     | T::Less
    //     | T::LessEqual
    //     | T::And
    //     | T::Or
    //     | T::AssertEqual
    //     | T::In => {}
    //
    //     // Unknown infix operator.
    //     _ => {
    //         raise_syntax_error!(ctx.prev(), "Not a valid infix operator");
    //     }
    // };
    //
    // let (ctx, rhs) = parse_precedence(ctx, precedence(op).next())?;
    //
    // // Left and right of the operator.
    // let lhs = Box::new(lhs.clone());
    // let rhs = Box::new(rhs);
    //
    // // Which expression kind to emit depends on the token.
    // let kind = match op {
    //     // Simple arithmetic.
    //     T::Plus => Add(lhs, rhs),
    //     T::Minus => Sub(lhs, rhs),
    //     T::Star => Mul(lhs, rhs),
    //     T::Slash => Div(lhs, rhs),
    //
    //     // Comparisons
    //     T::EqualEqual => Comparison(lhs, Equals, rhs),
    //     T::NotEqual => Comparison(lhs, NotEquals, rhs),
    //     T::Greater => Comparison(lhs, Greater, rhs),
    //     T::GreaterEqual => Comparison(lhs, GreaterEqual, rhs),
    //     T::Less => Comparison(lhs, Less, rhs),
    //     T::LessEqual => Comparison(lhs, LessEqual, rhs),
    //     T::In => Comparison(lhs, In, rhs),
    //
    //     // Boolean operators.
    //     T::And => And(lhs, rhs),
    //     T::Or => Or(lhs, rhs),
    //
    //     T::AssertEqual => AssertEq(lhs, rhs),
    //
    //     // Unknown infix operator.
    //     _ => {
    //         unreachable!();
    //     }
    // };
    //
    // Ok((ctx, Expression::new(span, kind)))
    panic!()
}
