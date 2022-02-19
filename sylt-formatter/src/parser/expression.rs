use std::ops::Range;

use sylt_tokenizer::Token;

use super::{Context, ParseResult};

/// An expression in sylt
#[derive(Debug)]
pub enum Expression<'a> {
    /// An integer value
    Int(i64, &'a Range<usize>),

    /// A floating point value
    Float(f64, &'a Range<usize>),
}

impl<'a> Expression<'a> {
    pub fn parse(ctx: Context<'a>) -> ParseResult<'a, Expression<'a>> {
        match ctx.eat() {
            (ctx, Token::Int(v), span) => Ok((Expression::Int(*v, span), ctx)),
            _ => panic!(),
        }
    }
}
