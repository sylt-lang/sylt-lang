//! This is the parser for the sylt formatter.
//!
//! The parser uses recursive descent to parse.

use std::ops::Range;

use sylt_tokenizer::Token;

/// The zero span, from 0 to 0, used as a placeholder for non-existant tokesn
const zero_span: Span = 0..0;

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

    /// Get the current token of the context
    pub fn token(self) -> &'a Token {
        self.peek_ahead(0)
    }

    /// Peek at the next token
    pub fn peek(self) -> &'a Token {
        self.peek_ahead(1)
    }

    /// Peek a number of tokens ahead
    pub fn peek_ahead(self, lookahead: usize) -> &'a Token {
        self.get_token(self.position + lookahead)
    }

    /// Get the span of the current token
    pub fn span(self) -> &'a Range<usize> {
        self.span_ahead(0)
    }

    /// Get the span of a few tokens ahead
    pub fn span_ahead(self, lookahead: usize) -> &'a Range<usize> {
        self.get_span(self.position + lookahead)
    }

    /// Return a context advanced by 1 token as well as the token and span advanced
    pub fn eat(self) -> (Self, &'a Token, &'a Range<usize>) {
        (
            Self { position: self.position + 1, tokens: self.tokens },
            self.token(),
            self.span(),
        )
    }

    /// The context forwarded by 1 token
    pub fn step(self) -> Self {
        self.forward(1)
    }

    /// The context forwarded by a number of tokens
    pub fn forward(self, steps: usize) -> Self {
        Self {
            position: self.position + steps,
            tokens: self.tokens,
        }
    }

    /// Get the next context with a non-white space token
    pub fn skip_ws(self) -> Self {
        let mut i = self.position;
        while matches!(self.get_token(i), Token::Newline) {
            i += 1;
        }
        Self { position: i, ..self }
    }

    /// Get the current token
    fn get_token(self, i: usize) -> &'a Token {
        &self.get(i).0
    }

    /// Get the current span
    fn get_span(self, i: usize) -> &'a Span {
        &self.get(i).1
    }

    /// Get the current token and span
    fn get(self, i: usize) -> &'a (Token, Span) {
        &self.tokens.get(i).unwrap_or(&(Token::EOF, zero_span))
    }
}

/// Expect a token pattern at the current token of the context
#[macro_export]
macro_rules! expect {
    ($ctx:expr, $($tokens:pat)|+ ) => {
        if !matches!($ctx.token(), $($tokens)|+) {
            return Err((
                $ctx,
                crate::parser::ParseErr {
                    err_type: crate::parser::ParseErrType::UnexpectedToken {
                        got: format!("{:?}", $ctx.token()),
                        expected: String::from(stringify!($($tokens)|+)),
                    },
                    inner_span: $ctx.span().clone(),
                },
            ));
        };
    };
}

#[derive(Debug)]
pub enum ParseErrType {
    /// Undefined parse error type, this should be avoided
    Undefined { message: String },

    /// An unexpected token was reached
    UnexpectedToken { got: String, expected: String },
}

/// A parse error
#[derive(Debug)]
pub struct ParseErr {
    pub err_type: ParseErrType,
    pub inner_span: Span,
}

impl ParseErr {
    pub fn message(&self) -> String {
        use ParseErrType as PET;

        match &self.err_type {
            PET::Undefined { message } => message.clone(),
            PET::UnexpectedToken { got, expected } => format!(
                "Found unexpected token. Got {:?}, expected {:?}",
                got, expected
            ),
        }
    }
}

/// The type of result for parsing
pub type ParseResult<'a, T> = Result<(Context<'a>, T), (Context<'a>, ParseErr)>;

pub type Span = Range<usize>;
