//! This is the parser for the sylt formatter.
//!
//! The parser uses recursive descent to parse.

use std::ops::Range;

use sylt_tokenizer::Token;

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

    /// Peek at the current token
    pub fn token(self) -> &'a Token {
        self.peek_ahead(0)
    }

    pub fn peek(self) -> &'a Token {
        self.peek_ahead(1)
    }

    /// Peek a some tokens ahead
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

    /// Return a context advanced by 1 token as well as the token and span
    /// advanced
    pub fn eat(self) -> (Self, &'a Token, &'a Range<usize>) {
        (
            Self { position: self.position + 1, tokens: self.tokens },
            self.token(),
            self.span(),
        )
    }

    pub fn step(self) -> Self {
        self.forward(1)
    }

    pub fn forward(self, steps: usize) -> Self {
        Self {
            position: self.position + steps,
            tokens: self.tokens,
        }
    }

    pub fn skip_ws(self) -> Self {
        let mut i = self.position;
        while matches!(self.get_token(i), Token::Newline) {
            i += 1;
        }
        Self { position: i, ..self }
    }

    fn get_token(self, i: usize) -> &'a Token {
        &self.get(i).0
    }

    fn get_span(self, i: usize) -> &'a Span {
        &self.get(i).1
    }

    fn get(self, i: usize) -> &'a (Token, Span) {
        &self.tokens.get(i).unwrap_or(&(Token::EOF, zero_span))
    }
}

#[macro_export]
macro_rules! expect {
    ($ctx:expr, $($tokens:pat)|+ ) => {
        if !matches!($ctx.token(), $($tokens)|+) {
            return Err((
                $ctx,
                crate::parser::ParseErr {
                    err_type: crate::parser::ParseErrType::Undefined {
                        message: format!(
                            "Expected {:?}, got {:?}",
                            stringify!($($tokens)|+),
                            $ctx.token()
                        ),
                    },
                    inner_span: $ctx.span().clone(),
                },
            ));
        };
    };
}

#[derive(Debug)]
pub enum ParseErrType {
    Undefined { message: String },
    UnexpectedToken { expected: Token, got: Token },
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
            // TODO(emanuel): Use nicer way of displaying unexpected token.
            PET::UnexpectedToken { expected, got, .. } => {
                format!("Unexpected token. Expected {:?}, got {:?}", expected, got)
            }
        }
    }
}

/// The type of result for parsing
pub type ParseResult<'a, T> = Result<(Context<'a>, T), (Context<'a>, ParseErr)>;

pub type Span = Range<usize>;
