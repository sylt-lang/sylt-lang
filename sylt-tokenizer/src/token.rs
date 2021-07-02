use logos::Logos;

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
    #[token("is")]
    Is,
    #[token("else")]
    Else,
    #[token("break")]
    Break,
    #[token("continue")]
    Continue,
    #[token("in")]
    In,
    #[token("loop")]
    Loop,
    #[token("blob")]
    Blob,

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

    #[token("#")]
    Hash,
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
    #[token("'")]
    Prime,

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
