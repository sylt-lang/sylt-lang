use logos::Logos;

#[derive(Logos, Debug, PartialEq, Clone)]
pub enum Token {
    #[regex(r"[A-Za-z_][A-Za-z0-9_]*", |lex| lex.slice().to_string())]
    Identifier(String),

    #[token("void")]
    VoidType,
    #[token("bool")]
    BoolType,
    #[token("int")]
    IntType,
    #[token("float")]
    FloatType,
    #[token("str")]
    StrType,

    #[regex(r#""[^"]*""#, |lex| { let mut s = lex.slice().to_string(); s.remove(0); s.pop(); s })]
    String(String),

    // `X.`, `.Y`, `X.Y`, `XeY` and `Xe-Y`
    #[regex(r"([\d]+\.[\d]*|[\d]*\.[\d]+)|[\d]+e(-|\+)?[\d]+", |lex| lex.slice().parse(), priority=2)]
    Float(f64),
    #[regex(r"[\d]+", |lex| lex.slice().parse())]
    Int(i64),

    #[regex(r"nil")]
    Nil,

    #[regex(r"true|false", |lex| lex.slice().parse(), priority=2)]
    Bool(bool),

    #[token("if")]
    If,
    #[token("elif")]
    Elif,
    #[token("else")]
    Else,
    #[token("case")]
    Case,
    #[token("is")]
    Is,
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
    #[token("externblob")]
    ExternBlob,
    #[token("enum")]
    Enum,

    #[token("ret")]
    Ret,

    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
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

    #[token("do")]
    Do,
    #[token("end")]
    End,

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
    #[token("pu")]
    Pu,

    #[token("and")]
    And,
    #[token("or")]
    Or,
    #[token("not")]
    Not,
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
    #[token("from")]
    From,
    #[token("as")]
    As,
    #[token("external")]
    External,

    #[token("<<<<<<<")]
    GitConflictBegin,
    #[token(">>>>>>>")]
    GitConflictEnd,

    #[regex(r"//[^\n]*", |lex| lex.slice()[2..].trim().to_string())]
    Comment(String),

    #[regex(r"[ \t\r]+", logos::skip)]
    Whitespace,

    EOF,

    #[error]
    Error,
}
