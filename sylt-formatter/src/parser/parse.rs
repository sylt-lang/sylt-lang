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

    pub fn forward(self, steps: usize) -> Self {
        Self {
            position: self.position + steps,
            tokens: self.tokens,
        }
    }
}

/// A sylt module (a sylt file)
#[derive(Debug)]
pub struct Module<'a> {
    statements: Vec<Statement<'a>>,
}

#[derive(Debug)]
pub enum ParseErrType {
    Undefined { message: String },
}

/// A parse error
#[derive(Debug)]
pub struct ParseErr {
    pub err_type: ParseErrType,
    pub inner_span: Span,
}

impl ParseErr {
    pub fn message(&self) -> String {
        match &self.err_type {
            ParseErrType::Undefined { message } => message.clone(),
        }
    }
}

/// Parse a sylt module (sylt file)
pub fn parse_module<'a>(tokens: &'a [(Token, Range<usize>)]) -> ParseResult<'a, Module> {
    let ctx = Context::new(tokens);
    let (ctx, statement) = Statement::parse(ctx)?;

    Ok((ctx, Module { statements: vec![statement] }))
}

/// The type of result for parsing
pub type ParseResult<'a, T> = Result<(Context<'a>, T), (Context<'a>, ParseErr)>;

pub type Span = Range<usize>;
