//! This is the parser for the sylt formatter.
//!
//! The parser uses recursive descent to parse.

use std::ops::Range;

use sylt_tokenizer::Token;

use super::{expression::Expression, statement::Statement};

/// The context of the parser.
#[derive(Clone, Copy, Debug)]
pub struct Context<'a> {
    /// The token position
    position: usize,

    /// The tokens
    tokens: &'a [(Token, Range<usize>)],
}

impl<'a> Context<'a> {
    /// Create a new context
    pub fn new(tokens: &'a [(Token, Range<usize>)]) -> Self {
        Self { position: 0, tokens }
    }

    /// Peek at the current token
    pub fn peek(self) -> &'a Token {
        self.peek_ahead(0)
    }

    /// Peek a some tokens ahead
    pub fn peek_ahead(self, lookahead: usize) -> &'a Token {
        &self.tokens[self.position + lookahead].0
    }

    /// Get the span of the current token
    pub fn span(self) -> &'a Range<usize> {
        self.span_ahead(0)
    }

    /// Get the span of a few tokens ahead
    pub fn span_ahead(self, lookahead: usize) -> &'a Range<usize> {
        &self.tokens[self.position + lookahead].1
    }

    /// Return a context advanced by 1 token as well as the token and span
    /// advanced
    pub fn eat(self) -> (Self, &'a Token, &'a Range<usize>) {
        (
            Self { position: self.position + 1, tokens: self.tokens },
            self.peek(),
            self.span(),
        )
    }
}

/// A sylt module (a sylt file)
#[derive(Debug)]
pub struct Module<'a> {
    statements: Vec<Statement<'a>>,
}

/// A parse error
#[derive(Debug)]
pub struct ParseErr {}

pub trait Parseable<'a, T> {
    fn parse(ctx: Context) -> ParseResult<'a, T>;
}

/// Parse a sylt module (sylt file)
pub fn parse_module<'a>(tokens: &'a [(Token, Range<usize>)]) -> Result<Module<'a>, ParseErr> {
    let ctx = Context::new(tokens);
    let (statement, ctx) = parse_statement(ctx).unwrap();

    Ok(Module { statements: vec![statement] })
}

/// The type of result for parsing
pub type ParseResult<'a, T: 'a> = Result<(T, Context<'a>), (ParseErr, Context<'a>)>;

/// Parse a statement
fn parse_statement<'a>(ctx: Context<'a>) -> ParseResult<'a, Statement> {
    let (ctx, token, name_span) = ctx.eat();

    let name = if let Token::Identifier(name) = token {
        name
    } else {
        panic!();
    };

    let (ctx, token, span) = ctx.eat();
    assert!(matches!(token, Token::ColonColon));

    let (expression, ctx) = parse_expression(ctx)?;

    Ok((
        Statement::Definition { var: (name, name_span), expr: expression },
        ctx,
    ))
}

/// Parse an expression
fn parse_expression<'a>(ctx: Context<'a>) -> ParseResult<'a, Expression> {
    match ctx.eat() {
        (ctx, Token::Int(v), span) => Ok((Expression::Int(*v, span), ctx)),
        _ => panic!(),
    }
}
