use logos::Logos;

#[derive(Logos, Debug, PartialEq, Clone, Copy)]
pub enum Token<'t> {
  #[regex("[a-z_][a-zA-Z0-9_]*", |lex| lex.slice())]
  Name(&'t str),

  #[regex("[A-Z][a-zA-Z0-9_]*", |lex| lex.slice())]
  ProperName(&'t str),

  #[regex(r"[\d]+", |lex| lex.slice())]
  Int(&'t str),

  // `X.`, `.Y`, `X.Y`, `XeY` and `Xe-Y`
  #[regex(r"([\d]+\.[\d]*|[\d]*\.[\d]+)|[\d]+e(-|\+)?[\d]+", |lex| lex.slice(), priority=2)]
  Real(&'t str),

  // TODO replace the \\ and \" with the right strings
  #[regex(r#""[^(\\.)"]*""#, |lex| lex.slice().strip_prefix("\"").unwrap().strip_suffix("\"").unwrap(), priority=2)]
  Str(&'t str),

  // Keywords
  #[token("->")]
  KwArrow,
  #[token("def")]
  KwDef,
  #[token("enum")]
  KwEnum,
  #[token("type")]
  KwType,
  #[token("foreign")]
  KwForiegn,

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
  #[token(":")]
  Colon,
  #[token("=")]
  Equal,
  #[token("|")]
  Pipe,

  #[regex(r"[ \t\n\f]+", logos::skip)]
  #[regex(r"--.*\n", logos::skip)]
  #[error]
  Error,
}

impl<'t> Token<'t> {
  pub fn describe(&self) -> String {
    match self {
      Token::Name(n) => format!("name {:?}", n),
      Token::ProperName(n) => format!("proper name {:?}", n),
      Token::Int(n) => format!("int {:?}", n),
      Token::Real(n) => format!("real {:?}", n),
      Token::Str(s) => format!("str {:?}", s),

      Token::KwArrow => "keyword `->`".to_string(),
      Token::KwDef => "keyword `def`".to_string(),
      Token::KwEnum => "keyword `enum`".to_string(),
      Token::KwType => "keyword `type`".to_string(),
      Token::KwForiegn => "keyword `foreign`".to_string(),

      Token::OpNeg => "operator `!`".to_string(),
      Token::OpAdd => "operator `+`".to_string(),
      Token::OpSub => "operator `-`".to_string(),
      Token::OpMul => "operator `*`".to_string(),
      Token::OpDiv => "operator `/`".to_string(),
      Token::OpCall => "operator `'`".to_string(),

      Token::LParen => "a `(`".to_string(),
      Token::RParen => "a `)`".to_string(),
      Token::Period => "a `.`".to_string(),
      Token::Colon => "a `:`".to_string(),
      Token::Equal => "a `=`".to_string(),
      Token::Pipe => "a `|`".to_string(),

      Token::Error => "invalid token".to_string(),
    }
  }
}
