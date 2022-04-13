use sylt_tokenizer::Token as T;

use crate::{expect, parser::Context};

use super::{statement::Statement, ParseResult};

/// A sylt module (a sylt file)
#[derive(Debug)]
pub struct Module<'a> {
    statements: Vec<Statement<'a>>,
}

impl<'a> Module<'a> {
    /// Parse a sylt module (sylt file)
    pub fn parse(tokens: &'a [(T, super::Span)]) -> ParseResult<'a, Self> {
        let ctx = Context::new(tokens);

        let mut statements: Vec<Statement> = Vec::new();

        let mut ctx = ctx;

        loop {
            let (next_ctx, statement) = Statement::parse(ctx)?;
            statements.push(statement);
            ctx = next_ctx;

            expect!(ctx, T::Newline | T::EOF);

            ctx = ctx.skip_ws();

            if matches!(ctx.token(), T::EOF) {
                break Ok((ctx, Module { statements }));
            }
        }
    }
}
