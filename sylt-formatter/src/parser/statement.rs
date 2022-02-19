use std::ops::Range;

use sylt_tokenizer::Token;

use super::{expression::Expression, Context, ParseResult};

/// A statement in sylt
#[derive(Debug)]
pub enum Statement<'a> {
    /// A definition of a variable
    ///
    /// Ex: `var :: <expr>`
    Definition {
        /// The variable name
        var: (&'a String, &'a Range<usize>),

        /// The expression defines the variable
        expr: Expression<'a>,
    },
}

impl<'a> Statement<'a> {
    pub fn parse(ctx: Context<'a>) -> ParseResult<'a, Statement> {
        let (ctx, token, name_span) = ctx.eat();

        let name = if let Token::Identifier(name) = token {
            name
        } else {
            panic!();
        };

        let (ctx, token, span) = ctx.eat();
        assert!(matches!(token, Token::ColonColon));

        let (expression, ctx) = Expression::parse(ctx)?;

        Ok((
            Statement::Definition { var: (name, name_span), expr: expression },
            ctx,
        ))
    }
}
