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

  // TODO replace the \\ and \" with the right strings? Do I need to do this or can I let Lua do
  // it?
  #[regex(r#""[^(\\.)"]*""#, |lex| lex.slice().strip_prefix("\"").unwrap().strip_suffix("\"").unwrap(), priority=2)]
  Str(&'t str),

  #[token("true")]
  True,

  #[token("false")]
  False,

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
  #[token("let")]
  KwLet,
  #[token("in")]
  KwIn,
  #[token("@")]
  KwAtSign,

  #[regex(r#"-\[\["#, |lex| {
      match lex.remainder().find("]]-") {
          None => Err("Expected a closing ]]-"),
          Some(end) => {
              lex.bump(end + 3);
              Ok(lex.slice().strip_prefix("-[[").unwrap().strip_suffix("]]-").unwrap().trim())
          }
      }
    }, priority=2)]
  ForiegnBlock(&'t str),

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

  #[token("{")]
  LCurl,
  #[token("}")]
  RCurl,

  #[token(",")]
  Comma,
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
      Token::True => format!("boolean value 'true'"),
      Token::False => format!("boolean value 'false'"),

      Token::KwArrow => "keyword `->`".to_string(),
      Token::KwDef => "keyword `def`".to_string(),
      Token::KwEnum => "keyword `enum`".to_string(),
      Token::KwType => "keyword `type`".to_string(),
      Token::KwForiegn => "keyword `foreign`".to_string(),
      Token::ForiegnBlock(_) => "a foreign block".to_string(),
      Token::KwLet => "keyword `let`".to_string(),
      Token::KwIn => "keyword `in`".to_string(),
      Token::KwAtSign => "keyword `@`".to_string(),

      Token::OpNeg => "operator `!`".to_string(),
      Token::OpAdd => "operator `+`".to_string(),
      Token::OpSub => "operator `-`".to_string(),
      Token::OpMul => "operator `*`".to_string(),
      Token::OpDiv => "operator `/`".to_string(),
      Token::OpCall => "operator `'`".to_string(),

      Token::LParen => "a `(`".to_string(),
      Token::RParen => "a `)`".to_string(),
      Token::LCurl => "a `{`".to_string(),
      Token::RCurl => "a `}`".to_string(),
      Token::Comma => "a `,`".to_string(),
      Token::Period => "a `.`".to_string(),
      Token::Colon => "a `:`".to_string(),
      Token::Equal => "a `=`".to_string(),
      Token::Pipe => "a `|`".to_string(),

      Token::Error => "invalid token".to_string(),
    }
  }
}
