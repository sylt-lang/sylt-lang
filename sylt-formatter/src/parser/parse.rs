//! This is the parser for the sylt formatter.
//!
//! The parser uses recursive descent to parse.

use std::ops::Range;

use sylt_tokenizer::Token;

use super::statement::Statement;

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

/// Parse a sylt module (sylt file)
pub fn parse_module<'a>(tokens: &'a [(Token, Range<usize>)]) -> Result<Module<'a>, ParseErr> {
    let ctx = Context::new(tokens);
    let (statement, ctx) = Statement::parse(ctx).unwrap();

    Ok(Module { statements: vec![statement] })
}

/// The type of result for parsing
pub type ParseResult<'a, T> = Result<(T, Context<'a>), (ParseErr, Context<'a>)>;

pub type Span = Range<usize>;

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
