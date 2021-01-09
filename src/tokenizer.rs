use std::fs;
use logos::{Logos, Span};

#[derive(Logos, Debug, PartialEq, Clone)]
pub enum Token {
    #[regex(r"[A-Za-z_][A-Za-z0-9_]*", |lex| lex.slice().to_string())]
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
    #[token("!=")]
    NotEqual,
    #[token("<=>")]
    AssertEqual,

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

    #[token("&&")]
    And,
    #[token("||")]
    Or,
    #[token("!")]
    Not,

    #[token(".")]
    Dot,
    #[token("->")]
    Arrow,
    #[token("\n")]
    Newline,

    #[regex(r"//[^\n]*\n", logos::skip)]
    Comment,

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

#[cfg(test)]
mod tests {
    use super::Token;
    use logos::Logos;

    fn lex(s: &str) -> Vec<Token> {
        Token::lexer(s).collect()
    }

    fn lex_once(s: &str) -> Token {
        let mut lexer = Token::lexer(s);
        let res = lexer.next().unwrap();
        assert_eq!(lexer.next(), None);
        res
    }

    #[test]
    fn test_lex_once() {
        lex_once("1");
    }

    #[test]
    #[should_panic]
    fn test_lex_once_panic() {
        lex_once("1 2");
    }

    #[test]
    fn number() {
        assert_eq!(lex_once("1"), Token::Int(1));
        assert_eq!(lex_once("1.1"), Token::Float(1.1));
        assert_eq!(lex_once("123"), Token::Int(123));
        assert_eq!(lex_once(".1"), Token::Float(0.1));
        assert_eq!(lex_once("1."), Token::Float(1.0));
    }

    #[test]
    fn identifiers() {
        let ident_cmp = |s| assert_eq!(lex_once(s), Token::Identifier(String::from(s)));
        ident_cmp("a");
        ident_cmp("aaaaaaaa");
        ident_cmp("a1");
        ident_cmp("a_");
        ident_cmp("_a");
        ident_cmp("__");
    }

    #[test]
    fn whitespace() {
        lex_once("1 ");
        lex_once(" 1");
        lex_once(" 1 ");

        assert_eq!(lex("1 2").len(), 2);
        assert_eq!(lex("1\t2").len(), 2);
        assert_eq!(lex("1             2").len(), 2);
        assert_eq!(lex("\t1   \t  \t\t     2\t").len(), 2);
    }

    #[test]
    fn comment() {
        lex_once("// a\n1");
        assert_eq!(lex("1// a\n2").len(), 2);
        assert_eq!(lex("1\n// a\n2").len(), 3); // newline is also a token
    }
}
