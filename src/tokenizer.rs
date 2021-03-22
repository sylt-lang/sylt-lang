use logos::Logos;
use std::{fs, path::Path};

#[derive(Logos, Debug, PartialEq, Clone)]
pub enum Token {
    #[regex(r"[A-Za-z_][A-Za-z0-9_]*", |lex| lex.slice().to_string())]
    Identifier(String),

    #[regex(r#""[^"]*""#, |lex| { let mut s = lex.slice().to_string(); s.remove(0); s.pop(); s })]
    String(String),

    #[regex(r"[\d]+\.[\d]*|[\d]*\.[\d]+", |lex| lex.slice().parse(), priority=2)]
    Float(f64),
    #[regex(r"[\d]+", |lex| lex.slice().parse())]
    Int(i64),

    #[regex(r"nil")]
    Nil,

    #[regex(r"true|false", |lex| lex.slice().parse(), priority=2)]
    Bool(bool),

    #[token("if")]
    If,
    #[token("else")]
    Else,
    #[token("for")]
    For,
    #[token("break")]
    Break,
    #[token("continue")]
    Continue,
    #[token("in")]
    In,
    // #[token("loop")]
    // Loop,
    #[token("blob")]
    Blob,

    // TODO(ed): Remove
    #[token("print")]
    Print,

    #[token("yield")]
    Yield,

    #[token("ret")]
    Ret,

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
    #[token(":=")]
    ColonEqual,
    #[token("=")]
    Equal,
    #[token("==")]
    EqualEqual,
    #[token("!=")]
    NotEqual,

    #[token("<=>")]
    AssertEqual,
    #[token("<!>")]
    Unreachable,

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

    #[token("fn")]
    Fn,

    #[token("&&")]
    And,
    #[token("||")]
    Or,
    #[token("!")]
    Bang,
    #[token("?")]
    QuestionMark,
    #[token("|")]
    Pipe,

    #[token(",")]
    Comma,
    #[token(".")]
    Dot,
    #[token("->")]
    Arrow,
    #[token("\n")]
    Newline,

    #[token("use")]
    Use,

    #[token("<<<<<<<")]
    GitConflictBegin,
    #[token(">>>>>>>")]
    GitConflictEnd,

    #[regex(r"//[^\n]*", logos::skip)]
    Comment,

    #[regex(r"[ \t\r]", logos::skip)]
    Whitespace,

    EOF,

    #[error]
    Error,
}

pub type PlacedToken = (Token, usize);
pub type TokenStream = Vec<PlacedToken>;

pub fn string_to_tokens(content: &str) -> TokenStream {
    let lexer = Token::lexer(&content);

    let mut placed_tokens = lexer.spanned().peekable();

    let mut lined_tokens = Vec::new();
    let mut line: usize = 1;
    for (c_idx, c) in content.chars().enumerate() {
        if let Some((kind, t_range)) = placed_tokens.peek() {
            if t_range.start == c_idx {
                let kind = kind.clone();
                placed_tokens.next();
                lined_tokens.push((kind, line));
            }
        } else {
            break;
        }

        if c == '\n' {
            line += 1;
        }
    }

    lined_tokens
}

pub fn file_to_tokens(file: &Path) -> Result<TokenStream, std::io::Error> {
    Ok(string_to_tokens(&fs::read_to_string(file)?))
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
        assert_eq!(lex("// a\n1").len(), 2);
        assert_eq!(lex("1// a\n2").len(), 3);
        assert_eq!(lex("1\n// a\n2").len(), 4); // newline is also a token
    }
}
