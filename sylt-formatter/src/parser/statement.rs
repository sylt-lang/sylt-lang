use std::ops::Range;

use sylt_tokenizer::Token as T;

use super::{expression::Expression, ty::Type, Context, ParseResult, Span};

/// A statement in sylt
#[derive(Debug)]
pub enum Statement<'a> {
    /// A definition of a variable
    ///
    /// Ex: `var :: <expr>`
    Definition {
        /// The variable name
        var: (&'a String, &'a Range<usize>),
        ty: Option<Type>,
        expr: Expression,
        mutable: bool,
        span: Span,
    },
}

impl<'a> Statement<'a> {
    /// Parse a statement
    pub fn parse(ctx: Context<'a>) -> ParseResult<'a, Statement> {
        let old_ctx = ctx;

        let (ctx, token, _) = ctx.eat();

        match token {
            T::Identifier(_name) => {
                let token = ctx.token();

                match token {
                    T::Colon | T::ColonColon | T::ColonEqual => definition(old_ctx),

                    T::Equal => assignment(old_ctx),

                    T::PlusEqual | T::MinusEqual | T::StarEqual | T::SlashEqual => {
                        op_assignment(old_ctx)
                    }

                    _ => todo!(),
                }
            }

            _ => todo!(),
        }
    }
}

fn definition<'a>(ctx: Context<'a>) -> ParseResult<'a, Statement> {
    let (ctx, token, initial_span) = ctx.eat();

    let var = match token {
        T::Identifier(name) => (name, initial_span),
        _ => todo!(),
    };

    let (ctx, token, _span) = ctx.eat();

    let (ctx, mutable, ty) = match token {
        T::ColonColon => (ctx, false, None),
        T::ColonEqual => (ctx, true, None),

        T::Colon => {
            let (ctx, ty) = Type::parse(ctx)?;

            let (ctx, token, _span) = ctx.eat();
            let mutable = match token {
                T::Colon => false,
                T::Equal => true,
                _ => todo!(),
            };
            (ctx, mutable, Some(ty))
        }

        _ => todo!(),
    };

    let (ctx, expr) = Expression::parse(ctx)?;

    Ok((
        ctx,
        Statement::Definition {
            var,
            mutable,
            ty,
            span: initial_span.start..expr.span().end,
            expr,
        },
    ))
}

fn assignment(ctx: Context) -> ! {
    todo!()
}

fn op_assignment(ctx: Context) -> ! {
    todo!()
}

pub type Block<'a> = (Vec<Statement<'a>>, Span);
