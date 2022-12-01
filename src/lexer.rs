use logos::Logos;

#[derive(Logos, Debug, PartialEq)]
pub enum Token<'t> {
    #[regex("[a-z_][a-zA-Z0-9_]*", |lex| lex.slice())]
    Name(&'t str),

    #[regex("[A-Z][a-zA-Z0-9_]*", |lex| lex.slice())]
    ProperName(&'t str),

    // `X.`, `.Y`, `X.Y`, `XeY` and `Xe-Y`
    #[regex(r"([\d]+\.[\d]*|[\d]*\.[\d]+)|[\d]+e(-|\+)?[\d]+", |lex| lex.slice(), priority=2)]
    Float(&'t str),

    #[regex(r"[\d]+", |lex| lex.slice())]
    Int(&'t str),

    // Keywords
    #[token("type")]
    KwType,
    #[token("->")]
    KwArrow,

    // Operators
    #[token("!")]
    OpNeg,
    #[token("+")]
    OpAdd,
    #[token("-")]
    OpSub,
    #[token("*")]
    OpMul,
    #[token("/")]
    OpDiv,
    #[token("'")]
    OpCall,

    #[token("(")]
    LParen,
    #[token(")")]
    RParen,

    #[token(".")]
    Period,

    #[regex(r"[ \t\n\f]+", logos::skip)]
    #[error]
    Error,
}

impl<'t> Token<'t> {
    pub fn describe(&self) -> String {
        match self {
            Token::Name(n) => format!("name {:?}", n),
            Token::ProperName(n) => format!("proper name {:?}", n),
            Token::Float(n) => format!("float {:?}", n),
            Token::Int(n) => format!("int {:?}", n),
            Token::KwType => "keyword `type`".to_string(),
            Token::KwArrow => "keyword `->`".to_string(),
            Token::OpNeg => "operator `!`".to_string(),
            Token::OpAdd => "operator `+`".to_string(),
            Token::OpSub => "operator `-`".to_string(),
            Token::OpMul => "operator `*`".to_string(),
            Token::OpDiv => "operator `/`".to_string(),
            Token::OpCall => "operator `'`".to_string(),
            Token::LParen => "a `(`".to_string(),
            Token::RParen => "a `)`".to_string(),
            Token::Period => "a `.`".to_string(),
            Token::Error => "ERROR!".to_string(),
        }
    }
}

