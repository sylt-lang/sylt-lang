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
    /// The first column that this Span contains.
    pub col_start: usize,
    /// The first column that this Span doesn't contain.
    pub col_end: usize,
}

impl Span {
    pub fn zero() -> Self {
        Self {
            line: 0,
            col_start: 0,
            col_end: 0,
        }
    }
}

#[derive(Debug)]
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
    char_at_byte.push(Some(content.chars().count()));

    // We also need to keep track of the current line and which char index the
    // previous newline was at. Given a char index we can then subtract the last
    // newline char index and get the column in the current line of the char.
    let mut line = 1;
    let mut last_newline = 0;

    Token::lexer(&content)
        .spanned()
        .map(|(token, range)| {
            let is_newline = token == Token::Newline;
            let placed_token = PlacedToken {
                token,
                span: Span {
                    line,
                    col_start: char_at_byte[range.start].unwrap() - last_newline,
                    col_end: char_at_byte[range.end].unwrap() - last_newline,
                }
            };
            if is_newline {
                line += 1;
                last_newline = char_at_byte[range.start].unwrap();
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
