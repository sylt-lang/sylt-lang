use crate::ast::*;
use crate::error::*;
use crate::lexer::Token;

use logos::Logos;

pub struct Lex<'t> {
  lexer: logos::Lexer<'t, Token<'t>>,
  buffer: (Span, Option<Token<'t>>),
}

pub fn err_eof<'t, A>(span: Span) -> PRes<A> {
  Err(Error::SynEoF { span })
}

pub fn err_msg<'t, A>(msg: &'static str, span: Span) -> PRes<A> {
  Err(Error::SynMsg { msg, span, token: None })
}

pub fn err_msg_token<'t, A>(msg: &'static str, token: Option<Token<'t>>, span: Span) -> PRes<A> {
  Err(Error::SynMsg { msg, span, token: token.map(|t| t.describe()) })
}

impl<'t> Lex<'t> {
  pub fn new(lexer: logos::Lexer<'t, Token<'t>>) -> Self {
    let mut lexer = Self { lexer, buffer: (Span(0, 0), None) };
    lexer.feed();
    lexer
  }

  fn feed(&mut self) -> (Span, Option<Token<'t>>) {
    let t = self.lexer.next();
    let s = {
      let s = self.lexer.span();
      Span(s.start, s.end)
    };
    let out = self.buffer;
    self.buffer = (s, t);
    out
  }

  pub fn span(&self) -> Span {
    self.buffer.0
  }

  pub fn token(&self) -> Option<Token<'t>> {
    self.buffer.1
  }

  pub fn peek(&self) -> (Span, Option<Token<'t>>) {
    self.buffer
  }

  pub fn next(&mut self) -> (Span, Option<Token<'t>>) {
    if self.buffer.1.is_none() {
      self.feed();
    }
    self.feed()
  }

  pub fn is_eof(&self) -> bool {
    self.buffer.1.is_none()
  }
}

pub type PRes<A> = Result<A, Error>;

macro_rules! expect {
  ($lex:expr, $pat:pat, $msg:literal) => {{
    if !matches!($lex.token(), Some($pat)) {
      return err_msg_token($msg, $lex.token(), $lex.span());
    }
    $lex.feed()
  }};
}

macro_rules! some {
  ($lex:expr, $expr:expr, $msg:literal) => {
    match $expr {
      Some(x) => x,
      None => return err_msg_token($msg, $lex.token(), $lex.span()),
    }
  };
}

#[derive(PartialEq, PartialOrd, Clone, Copy, Debug)]
enum Prec {
  // Tightest binding
  Factor,
  Term,
  Comp,
  BoolAnd,
  BoolOr,
  Call,

  No,
  // Weakest binding
}

fn next_prec(p: Prec) -> Prec {
  // To change associativeity, simply change from `Prec::A -> Prec::B` to `Prec::A -> Prec::A`, or vise versa.
  match p {
    Prec::Factor => Prec::Factor,
    Prec::Term => Prec::Factor,
    Prec::Comp => Prec::Term,
    Prec::BoolAnd => Prec::Comp,
    Prec::BoolOr => Prec::BoolAnd,

    Prec::Call => Prec::BoolOr,

    Prec::No => Prec::Call,
  }
}

fn op_to_prec(t: BinOp) -> Prec {
  match t {
    BinOp::Add(_) => Prec::Term,
    BinOp::Sub(_) => Prec::Comp,

    BinOp::Mul(_) => Prec::Factor,
    BinOp::Div(_) => Prec::Factor,

    BinOp::Call(_) => Prec::Call,
  }
}

pub fn parse<'t>(source: &'t str) -> Result<Vec<Def<'t>>, Vec<Error>> {
  let mut lex = Lex::new(Token::lexer(source));
  let mut errs = vec![];
  let mut defs = vec![];
  while !lex.is_eof() {
    match def(&mut lex) {
      Err(err) => {
        errs.push(err);
        while !matches!(
          lex.token(),
          None | Some(Token::KwDef | Token::KwType | Token::KwEnum)
        ) {
          lex.next();
        }
      }
      Ok(def) => defs.push(def),
    }
  }
  if errs.is_empty() {
    Ok(defs)
  } else {
    Err(errs)
  }
}

pub fn expr<'t>(lex: &mut Lex<'t>) -> PRes<Expr<'t>> {
  fn parse_precedence<'t>(lex: &mut Lex<'t>, prec: Prec) -> PRes<Expr<'t>> {
    fn prefix<'t>(lex: &mut Lex<'t>) -> PRes<Expr<'t>> {
      let (span, token) = lex.next();
      Ok(match token {
        None => return err_eof(span),
        Some(Token::OpNeg) => Expr::Un(UnOp::Neg(span), Box::new(prefix(lex)?)),
        Some(Token::Name(str)) => Expr::Var(Name(str, span), span),
        Some(Token::True) => Expr::EBool(true, span),
        Some(Token::False) => Expr::EBool(false, span),
        Some(Token::Int(i)) => Expr::EInt(i.parse().expect("Error in Int regex!"), span),
        Some(Token::Real(r)) => Expr::EReal(r.parse().expect("Error in Real regex!"), span),
        Some(Token::Str(s)) => Expr::EStr(s, span),
        Some(Token::ProperName(ty_name)) => {
          expect!(lex, Token::Colon, "Expected ':' in this enum constructor");
          if let (inner_span, Some(Token::ProperName(const_name))) = lex.next() {
            let ty_name = ProperName(ty_name, span);
            let const_name = ProperName(const_name, inner_span);
            let value = if let (_, Some(Token::RParen)) = lex.peek() {
              None
            } else {
              Some(Box::new(expr(lex)?))
            };
            Expr::EnumConst { ty_name, const_name, value }
          } else {
            return err_msg(
              "Expected another proper name and then a valid expression in this enum constructor",
              span,
            );
          }
        }
        Some(Token::LParen) => {
          let expr = expr(lex)?;
          expect!(
            lex,
            Token::RParen,
            "Expected a closing parenthasis after the inner expression"
          );
          expr
        }
        t => return err_msg_token("Not a valid start of the expression", t, span),
      })
    }

    fn maybe_op<'t>(span: Span, token: &Token<'t>) -> Option<BinOp> {
      Some(match token {
        Token::OpAdd => BinOp::Add(span),
        Token::OpSub => BinOp::Sub(span),

        Token::OpMul => BinOp::Mul(span),
        Token::OpDiv => BinOp::Div(span),
        Token::OpCall => BinOp::Call(span),

        _ => return None,
      })
    }

    let mut lhs = prefix(lex)?;
    loop {
      let (span, token) = lex.peek();
      match token.as_ref().and_then(|t| maybe_op(span, t)) {
        Some(op) if op_to_prec(op) <= prec => {
          lex.next();
          let rhs = parse_precedence(lex, next_prec(op_to_prec(op)))?;
          lhs = Expr::Bin(op, Box::new(lhs), Box::new(rhs));
        }
        _ => {
          break Ok(lhs);
        }
      }
    }
  }

  parse_precedence(lex, Prec::No)
}

pub fn type_<'t>(lex: &mut Lex<'t>) -> PRes<Option<Type<'t>>> {
  fn peek_term<'t>(lex: &mut Lex<'t>) -> PRes<Option<Type<'t>>> {
    let (span, head) = lex.peek();
    Ok(Some(match head {
      Some(Token::Name("_")) => {
        lex.next();

        Type::TEmpty(span)
      }
      Some(Token::Name(name)) => {
        lex.next();

        let name = Name(name, span);
        Type::TVar(name, span)
      }
      Some(Token::ProperName(name)) => {
        lex.next();

        let name = ProperName(name, span);
        let mut args = vec![];

        loop {
          match peek_term(lex)? {
            None => break,
            Some(res) => args.push(res),
          }
        }

        Type::TCustom { name, args, span }
      }
      Some(Token::LParen) => {
        lex.next();
        let inner = some!(
          lex,
          type_(lex)?,
          "Expected a type inside parentheses after seeing `(`"
        );
        expect!(
          lex,
          Token::RParen,
          "Expected a closing parenthasis after the inner type"
        );
        inner
      }

      _ => return Ok(None),
    }))
  }

  let mut ty = match peek_term(lex)? {
    Some(ty) => ty,
    None => return Ok(None),
  };
  while let Some(Token::KwArrow) = lex.token() {
    lex.next();
    let res = some!(lex, type_(lex)?, "Expected a type to follow `->`");
    let span = ty.span().merge(res.span());
    ty = Type::TFunction(Box::new(ty), Box::new(res), span);
  }
  Ok(Some(ty))
}

pub fn def<'t>(lex: &mut Lex<'t>) -> PRes<Def<'t>> {
  fn def_<'t>(lex: &mut Lex<'t>) -> PRes<Option<Def<'t>>> {
    let start = lex.span();
    if !matches!(lex.token(), Some(Token::KwDef)) {
      return Ok(None);
    };
    lex.next();

    let name = match expect!(lex, Token::Name(_), "Expected a name for the def") {
      (span, Some(Token::Name(str))) => Name(str, span),
      _ => unreachable!("Checked in the expect before"),
    };

    expect!(lex, Token::Colon, "Expected a `:` after the def name");
    let ty = if matches!(lex.token(), Some(Token::Colon)) {
      Type::TEmpty(lex.span())
    } else {
      some!(lex, type_(lex)?, "Expected a type or `:` for the def")
    };
    expect!(lex, Token::Colon, "Expected a `:` after the def type");
    let mut args = vec![];
    loop {
      match lex.peek() {
        (span, Some(Token::Name(str))) => {
          args.push(Name(str, span));
          lex.next();
        }
        _ => break,
      }
    }

    expect!(lex, Token::Equal, "Expected a `=` to start the def body");

    if matches!(lex.token(), Some(Token::KwForiegn)) {
      if !args.is_empty() {
        let span = args
          .iter()
          .map(|Name(_, span)| *span)
          .reduce(|a, b| a.merge(b))
          .unwrap();
        return err_msg(
          "A foreign definition may not take arguments, please remove them",
          span,
        );
      }
      lex.next();
      let end = lex.span();
      let span = start.merge(end);
      Ok(Some(Def::ForiegnDef { name, ty, span }))
    } else {
      let body = expr(lex)?;

      let end = lex.span();
      let span = start.merge(end);
      Ok(Some(Def::Def { name, ty, args, body, span }))
    }
  }

  fn ty_<'t>(lex: &mut Lex<'t>) -> PRes<Option<Def<'t>>> {
    let start = lex.span();
    if !matches!(lex.token(), Some(Token::KwType)) {
      return Ok(None);
    };
    lex.next();

    let name = match expect!(
      lex,
      Token::ProperName(_),
      "Expected a proper name for the type"
    ) {
      (span, Some(Token::ProperName(str))) => ProperName(str, span),
      _ => unreachable!("Checked in the expect before"),
    };

    let mut args = vec![];
    loop {
      match lex.peek() {
        (span, Some(Token::Name(str))) => {
          args.push(Name(str, span));
          lex.next();
        }
        _ => break,
      }
    }

    expect!(lex, Token::Equal, "Expected a `=` to start the type body");

    if matches!(lex.token(), Some(Token::KwForiegn)) {
      if !args.is_empty() {
        let span = args
          .iter()
          .map(|Name(_, span)| *span)
          .reduce(|a, b| a.merge(b))
          .unwrap();
        return err_msg(
          "A foreign type may not take arguments, please remove them",
          span,
        );
      }
      lex.next();
      let end = lex.span();
      let span = start.merge(end);
      Ok(Some(Def::ForiegnType { name, span }))
    } else {
      let body = some!(lex, type_(lex)?, "Expected a type for the body");

      let end = lex.span();
      let span = start.merge(end);
      Ok(Some(Def::Type { name, args, body, span }))
    }
  }

  fn enum_<'t>(lex: &mut Lex<'t>) -> PRes<Option<Def<'t>>> {
    let start = lex.span();
    if !matches!(lex.token(), Some(Token::KwEnum)) {
      return Ok(None);
    };
    lex.next();

    let name = match expect!(
      lex,
      Token::ProperName(_),
      "Expected a proper name for the enum"
    ) {
      (span, Some(Token::ProperName(str))) => ProperName(str, span),
      _ => unreachable!("Checked in the expect before"),
    };

    let mut args = vec![];
    loop {
      match lex.peek() {
        (span, Some(Token::Name(str))) => {
          args.push(Name(str, span));
          lex.next();
        }
        _ => break,
      }
    }

    expect!(lex, Token::Equal, "Expected a `=` to start the enum body");

    fn enum_const<'t>(lex: &mut Lex<'t>) -> PRes<EnumConst<'t>> {
      let start = lex.span();
      let tag = match expect!(
        lex,
        Token::ProperName(_),
        "Enum constructor tags have to start with a proper name"
      ) {
        (span, Some(Token::ProperName(str))) => ProperName(str, span),
        _ => unreachable!("Checked in the expect before"),
      };

      let ty = type_(lex)?;

      let end = lex.span();
      let span = start.merge(end);
      Ok(EnumConst { tag, ty, span })
    }

    let mut constructors = vec![enum_const(lex)?];
    while let Some(Token::Pipe) = lex.token() {
      lex.next();
      constructors.push(enum_const(lex)?);
    }

    let end = lex.span();
    let span = start.merge(end);
    Ok(Some(Def::Enum { name, args, constructors, span }))
  }

  fn ffi_<'t>(lex: &mut Lex<'t>) -> PRes<Option<Def<'t>>> {
    if !matches!(lex.token(), Some(Token::KwForiegn)) {
      return Ok(None);
    };
    lex.next();

    match expect!(
      lex,
      Token::ForiegnBlock(_),
      "A foreign code-block was expected after the foreign keyword"
    ) {
      (span, Some(Token::ForiegnBlock(source))) => Ok(Some(Def::ForeignBlock { span, source })),
      _ => unreachable!("Checked in the expect before"),
    }
  }

  let d = (|| {
    match def_(lex)? {
      Some(x) => return Ok(Some(x)),
      None => {}
    }
    match ty_(lex)? {
      Some(x) => return Ok(Some(x)),
      None => {}
    }
    match enum_(lex)? {
      Some(x) => return Ok(Some(x)),
      None => {}
    }
    match ffi_(lex)? {
      Some(x) => return Ok(Some(x)),
      None => {}
    }
    Ok(None)
  })()?;
  Ok(some!(lex, d, "Expected a def, but this isn't that"))
}

#[cfg(test)]
mod test {

  use super::*;
  use logos::Logos;

  macro_rules! test_p {
    ($name:ident, $parse:expr, $src:literal) => {
      #[test]
      fn $name() {
        let src = $src;
        let mut lex = Lex::new(Token::lexer($src));
        let res = $parse(&mut lex);
        assert!(res.is_ok(), "\n{:?} should parse\ngave:\n{:?}", src, res);
        assert!(
          lex.is_eof(),
          "\nDidn't parse to end of input! {:?} - {:?}\nGot: {:?}",
          src,
          lex.next(),
          res,
        );
      }
    };
  }

  macro_rules! no_test_p {
    ($name:ident, $parse:expr, $src:literal) => {
      #[test]
      fn $name() {
        let src = $src;
        let mut lex = Lex::new(Token::lexer($src));
        let res = $parse(&mut lex);
        assert!(
          res.is_err(),
          "\n{:?} should NOT parse\ngave:\n{:?}\n",
          src,
          res
        );
      }
    };
  }

  test_p!(int, expr, "1");
  test_p!(large_int, expr, "123123");
  test_p!(ident, expr, "a");
  test_p!(long_ident1, expr, "abcde");
  test_p!(long_ident2, expr, "a_b_c");
  test_p!(long_ident3, expr, "_a_b_c");
  test_p!(long_ident4, expr, "snakeCase");
  test_p!(neg1, expr, "!1");
  test_p!(neg2, expr, "!(1 + 1)");
  test_p!(add1, expr, "1 + 1");
  test_p!(add2, expr, "1 + 1 + 1 + 1");
  test_p!(sub1, expr, "1 - 1");
  test_p!(sub2, expr, "1 - 1 - 1 - 1");
  test_p!(mul1, expr, "1 * 1");
  test_p!(mul2, expr, "1 * 1 * 1 * 1");
  test_p!(div1, expr, "1 / 1");
  test_p!(div2, expr, "1 / 1 / 1 / 1");
  test_p!(mixed1, expr, "1 * (2 + 3)");
  test_p!(mixed2, expr, "1 * (2 + 3) + 1");
  test_p!(mixed3, expr, "1 * (2 + 3) + 1");
  test_p!(mixed4, expr, "a * (a + 3) + a");
  test_p!(mixed_ws1, expr, "1*(    2 +  3  )+1");
  test_p!(mixed_ws2, expr, "1   *    (    2        +3)+1");

  // :O
  test_p!(call1, expr, "a ' 1 ' 2 ' 3");
  test_p!(call2, expr, "a ' (1 + 2 + 3) ' (2 * 3) ' 3");
  test_p!(call3, expr, "f ' a + 1 ' b");
  test_p!(call4, expr, "1 + f ' a ' b");

  no_test_p!(il_ident1, expr, "A");
  no_test_p!(il_ident2, expr, "Abcedef");

  test_p!(t_int, type_, "Int");
  test_p!(t_float, type_, "Float");
  test_p!(t_string, type_, "String");
  test_p!(t_custom, type_, "Array Int");
  test_p!(t_custom_nested, type_, "Array Float Int");
  test_p!(t_with_paren1, type_, "A (B) C");
  test_p!(t_with_paren2, type_, "A (B C)");
  test_p!(t_function, type_, "A -> B -> C");
  test_p!(t_function_nested1, type_, "A -> (B F -> D) -> C");
  test_p!(t_function_nested2, type_, "A -> _");
  test_p!(t_function_nested3, type_, "A -> (B _)");
  test_p!(t_function_nested4, type_, "a -> b");
  test_p!(t_function_nested5, type_, "A a B");

  no_test_p!(ill_paren, type_, "(");

  test_p!(d_var1, def, "def a : Int : = 1");
  test_p!(d_var2, def, "def a : Int : = 1 + 1");
  test_p!(d_fun1, def, "def a : Int -> Int : a = 1 + a");
  test_p!(d_fun2, def, "def a : Array a -> List a : a = a - a");
  test_p!(d_fun3, def, "def a : Array a -> List a : a b c d e f = 1");
  test_p!(
    d_fun4,
    def,
    "def a\n:    Array a   \n -> List a : \n a b \n c d e f \n = 1"
  );
  test_p!(d_fun5, def, "def a : Array a -> List a : = foreign");

  no_test_p!(
    il_d_fun1,
    def,
    "def a : Array a -> List a : a b c d = foreign"
  );

  test_p!(d_ty1, def, "type Abc = Int");
  test_p!(d_ty2, def, "type Abc a = Int");
  test_p!(d_ty3, def, "type Abc a b c d e = Int");
  test_p!(d_ty4, def, "type A a b = B a C b");
  test_p!(d_ty5, def, "type    A long_name   b =    B long_name C b");
  test_p!(d_ty6, def, "type Int = foreign");
  no_test_p!(d_ty7, def, "type Int a b c = foreign");

  test_p!(d_enum1, def, "enum Maybe a = Just a | None");
  test_p!(d_enum2, def, "enum Either l r = Left l | Rights r");
  test_p!(d_enum3, def, "enum One = One");
  test_p!(
    d_enum4,
    def,
    "enum One a b c d e f g = One (Q a b c d e f g H) | QQ a"
  );
}
