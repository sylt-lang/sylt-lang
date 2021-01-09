use std::fs;
use logos::{Logos, Span};

#[derive(Logos, Debug, PartialEq, Clone)]
pub enum Token {
    #[regex(r"[[:alpha:]][[:alnum:]]*", |lex| lex.slice().to_string())]
    Identifier(String),

    #[regex(r#""[^"]*""#, |lex| lex.slice().to_string())]
    String(String),

    #[regex(r"[\d]+\.[\d]*|[\d]*\.[\d]+", |lex| lex.slice().parse(), priority=2)]
    Float(f64),
    #[regex(r"[\d]+", |lex| lex.slice().parse())]
    Int(i64),

    #[regex(r"true|false", |lex| lex.slice().parse(), priority=2)]
    Bool(bool),

    #[token("if")]
    If,
    #[token("for")]
    For,
    #[token("in")]
    In,
    #[token("loop")]
    Loop,

    // TODO(ed): Remove
    #[token("print")]
    Print,

    #[token("+")]
    Plus,
    #[token("++")]
    PlusPlus,
    #[token("-")]
    Minus,
    #[token("--")]
    MinusMinus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("+=")]
    PlusEqual,
    #[token("-=")]
    MinusEqual,
    #[token("*=")]
    StarEqual,
    #[token("/=")]
    SlashEqual,

    #[token(":")]
    Colon,
    #[token("::")]
    ColonColon,
    #[token("=")]
    Equal,
    #[token("==")]
    EqualEqual,

    #[token("(")]
    LeftParen,
    #[token(")")]
    RightParen,

    #[token("[")]
    LeftBracket,
    #[token("]")]
    RightBracket,

    #[token("{")]
    LeftBrace,
    #[token("}")]
    RightBrace,

    #[token(">")]
    Greater,
    #[token(">=")]
    GreaterEqual,
    #[token("<")]
    Less,
    #[token("<=")]
    LessEqual,

    #[token(".")]
    Dot,
    #[token("->")]
    Arrow,
    #[token("\n")]
    Newline,

    #[regex(r"[ \t\r]", logos::skip)]
    Whitespace,

    EOF,

    #[error]
    Error,
}

pub type PlacedToken = (Token, Span);
pub type TokenStream = Vec<PlacedToken>;
pub fn file_to_tokens(filename: &str) -> TokenStream {
    let content = fs::read_to_string(filename).unwrap();
    let lexer = Token::lexer(&content);
    lexer.spanned().collect()
}
