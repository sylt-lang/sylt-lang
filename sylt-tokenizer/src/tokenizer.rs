use logos::Logos;
use std::{fs, path::Path};
pub use token::Token;

mod token;

#[derive(Debug, Copy, Clone)]
/// A location in a file containing source code.
pub struct Span {
    // TODO(ed): Do this more intelligent, so
    // we can show ranges. Maybe even go back
    // to offsets from start of the file.
    pub line: usize,
    pub col_start_byte: usize,
    pub col_end_byte: usize,
}

impl Span {
    pub fn zero() -> Self {
        Self {
            line: 0,
            col_start_byte: 0,
            col_end_byte: 0,
        }
    }
}

#[derive(Debug)]
pub struct PlacedToken {
    pub token: Token,
    pub span: Span,
}

pub fn string_to_tokens(content: &str) -> Vec<PlacedToken> {
    // Map with side-effects intended
    let mut line = 1;
    let mut last_newline_byte = 0; // 1?
    Token::lexer(&content)
        .spanned()
        .map(|(token, range)| {
            let is_newline = token == Token::Newline;
            let res = PlacedToken {
                token,
                span: Span {
                    line,
                    col_start_byte: range.start - last_newline_byte,
                    col_end_byte: range.end - last_newline_byte,
                }
            };
            if is_newline {
                line += 1;
                last_newline_byte = range.start;
            }
            res
        })
        .collect()
}

pub fn file_to_tokens(file: &Path) -> Result<Vec<PlacedToken>, std::io::Error> {
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
