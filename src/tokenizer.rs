use std::{env, fs};

#[derive(Debug)]
pub enum TokenKind {
    Identifier(String), String(String), Float(f64), Int(i64), Bool(bool),

    If, For, In, Loop,

    Plus, Minus, Star, Slash,
    PlusPlus, MinusMinus,
    PlusEqual, MinusEqual, StarEqual, SlashEqual,

    Colon, ColonColon,
    Equal, EqualEqual,

    LeftParen, RightParen,

    LeftBracket, RightBracket,

    LeftBrace, RightBrace,

    Greater, Less,
    GreaterEqual, LessEqual,

    Arrow,
    Newline,

    Error,
    EOF,
}

#[derive(Debug)]
pub struct Token <'a> {
    kind: TokenKind,

    row: i32,
    col: i32,
    filename: &'a str,
}

use std::iter::Peekable;
use std::str::Chars;

fn parse_number(c: char, chars: &mut Peekable<Chars>) -> TokenKind {
    let mut number = String::from(c);
    loop {
        if let Some(c) = chars.peek() {
            match *c {
                '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8'| '9' | '.' => {}
                _ => { break; }
            }
        }
        number.push(chars.next().unwrap());
    }
    if number.contains(".") {
        return TokenKind::Float(number.parse::<f64>().unwrap());
    } else {
        return TokenKind::Int(number.parse::<i64>().unwrap());
    }
}

pub fn file_to_tokens(filename: &str) -> Vec<Token> {
    let content = fs::read_to_string(filename).unwrap();

    let mut tokens = Vec::new();

    let mut row = 1;
    let mut col = 0;

    let mut chars = content.chars().peekable();
    while let Some(c) = chars.next() {
        let mut kind = match c {
            '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8'| '9' | '.' => {
                parse_number(c, &mut chars)
            }
            _ => {
                TokenKind::Error
            }
        };

        tokens.push(Token{kind, row, col, filename});
    }

    tokens.push(Token{kind: TokenKind::EOF, row, col, filename});

    return tokens;
}
