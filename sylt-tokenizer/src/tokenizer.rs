use logos::Logos;
use std::{fs, path::Path};
pub use token::Token;

mod token;

#[derive(Debug, Copy, Clone, PartialEq)]
/// A location in a file containing source code.
pub struct Span {
    // TODO(ed): Do this more intelligent, so
    // we can show ranges. Maybe even go back
    // to offsets from start of the file.
    pub line: usize,
    /// The first column that this Span contains.
    pub col_start: usize,
    /// The first column that this Span doesn't contain.
    pub col_end: usize,
}

pub static ZERO_SPAN: Span = Span {
    line: 0,
    col_start: 0,
    col_end: 0,
};

impl Span {
    pub fn zero() -> Self {
        Self {
            line: 0,
            col_start: 0,
            col_end: 0,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct PlacedToken {
    pub token: Token,
    pub span: Span,
}

pub fn string_to_tokens(content: &str) -> Vec<PlacedToken> {
    // A list containing which char index a specific byte index is at.
    //
    // Since &str contains UTF-8, a byte offset (which is what the lexer gives
    // us) won't necessarily match up with the char index. For example, given
    // the string "123", '3' has both byte index 3 and char index 3. However, in
    // the string "ä23", '3' has char index 3 as before, but byte index 4 since
    // 'ä' contains two bytes.
    //
    // This list ensures that the byte offset the lexer gives us can be matched
    // with a char index. None means that the byte offset points inside a char
    // which should not be possible.
    let mut char_at_byte = vec![None; content.len()];
    for (i, (pos, _)) in content.char_indices().enumerate() {
        char_at_byte[pos] = Some(i + 1);
    }
    // Push a last value since the byte offset end is exclusive.
    char_at_byte.push(Some(content.chars().count() + 1));

    // We also need to keep track of the current line and which char index the
    // previous newline was at. Given a char index we can then subtract the last
    // newline char index and get the column in the current line of the char.
    let mut line = 1;
    let mut last_newline = 0;

    Token::lexer(&content)
        .spanned()
        // Contains side-effects.
        .map(|(token, byte_range)| {
            let is_newline = token == Token::Newline;
            let col_start = char_at_byte[byte_range.start].unwrap() - last_newline;
            let col_end = char_at_byte[byte_range.end].unwrap() - last_newline;
            let placed_token = PlacedToken {
                token,
                span: Span {
                    line,
                    col_start,
                    col_end,
                },
            };
            if is_newline {
                last_newline = char_at_byte[byte_range.start].unwrap();
                line += 1;
            }
            placed_token
        })
        .collect()
}

pub fn file_to_tokens(file: &Path) -> Result<Vec<PlacedToken>, std::io::Error> {
    Ok(string_to_tokens(&fs::read_to_string(file)?))
}

#[cfg(test)]
mod tests {
    use crate::{Token, string_to_tokens};
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

    fn vecs_match<T: PartialEq<T>>(a: &Vec<T>, b: &Vec<T>) -> bool {
        if a.len() == b.len() {
            a.iter().zip(b.iter()).all(|(a, b)| a == b)
        } else {
            false
        }
    }

    macro_rules! assert_placed_eq {
        ($a:expr, $( ($token:expr, $line:expr, $range:expr) ),+ $(,)? ) => {
            let a = $a;
            let b = vec![ $(
                $crate::PlacedToken {
                    token: $token,
                    span: $crate::Span {
                        line: $line,
                        col_start: $range.start,
                        col_end: $range.end,
                    }
                }
            ),*];
            if !vecs_match(&a, &b) {
                panic!("\n{:?}\ndoes not match\n{:?}", a, b);
            }
        };
    }

    #[test]
    fn simple_span() {
        assert_placed_eq!(
            string_to_tokens("1"),
            (Token::Int(1), 1, 1..2),
        );
        assert_placed_eq!(
            string_to_tokens("1\n"),
            (Token::Int(1),  1, 1..2),
            (Token::Newline, 1, 2..3),
        );
        assert_placed_eq!(
            string_to_tokens("1\n23\n456"),
            (Token::Int(1),   1, 1..2),
            (Token::Newline,  1, 2..3),
            (Token::Int(23),  2, 1..3),
            (Token::Newline,  2, 3..4),
            (Token::Int(456), 3, 1..4),
        );
    }

    #[test]
    fn span_with_non_ascii() {
        // The 'ö' is an error but we want to check that its span is a single char.
        assert_placed_eq!(
            string_to_tokens("wow\nwöw\n"),
            (Token::Identifier(String::from("wow")), 1, 1..4),
            (Token::Newline,                         1, 4..5),

            (Token::Identifier(String::from("w")),   2, 1..2),
            (Token::Error,                           2, 2..3),
            (Token::Identifier(String::from("w")),   2, 3..4),
            (Token::Newline,                         2, 4..5),
        );
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
