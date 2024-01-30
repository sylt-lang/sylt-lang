use std::collections::{btree_map::Entry, BTreeMap};

use logos::Logos;

use crate::error::Error;

#[derive(Logos, Debug, PartialEq, Clone, Copy)]
#[logos(skip r"[ \t\n\f]+")]
#[logos(skip r"--.*\n")]
pub enum Token<'t> {
  #[token("binr")]
  KwBinR,

  #[token("binl")]
  KwBinL,

  #[token("unary")]
  KwUnary,

  #[regex("[a-z_][a-zA-Z0-9_]*", |lex| lex.slice())]
  Name(&'t str),

  #[token(".")]
  Dot,

  #[regex("[A-Z][a-zA-Z0-9_]*", |lex| lex.slice())]
  ProperName(&'t str),

  #[regex(r"[\d]+", |lex| lex.slice())]
  Int(&'t str),

  #[regex("[-+*/'#<>=!&$#%?~^]+")]
  Sym(&'t str),
}

#[derive(Debug, PartialEq, Clone, Copy)]
enum Oper<'t> {
  BinR(usize, &'t str, &'t str),
  BinL(usize, &'t str, &'t str),
  Un(usize, &'t str, &'t str),
}

pub fn err_msg<'t, A>(msg: String, span: core::ops::Range<usize>) -> Result<A, Error> {
  Err(Error::Special(format!("{}\nOffset: {:?}", msg, span)))
}

macro_rules! expect {
  ($lex:expr, $pat:pat, $msg:literal) => {{
    match ($lex.span(), $lex.next()) {
      (_, Some(Ok(x @ $pat))) => x,
      (s, _) => return err_msg($msg.to_string(), s),
    }
  }};
}

pub fn parse<'t>(source: &'t str) -> Result<BTreeMap<&'t str, Oper<'t>>, Error> {
  use Oper::*;
  use Token::*;
  let mut lexer = Token::lexer(source);
  let mut out = BTreeMap::new();

  loop {
    let span = lexer.span();
    let kind = if let Some(next) = lexer.next() {
      if !matches!(next, Ok(KwBinR | KwBinL | KwUnary)) {
        return err_msg(
          "Expected `binr`, `binl` or `unary` at start of statement".to_string(),
          span,
        );
      }
      next.unwrap()
    } else {
      break;
    };
    let (sym, binding, module, name) = parse_op(&mut lexer)?;
    let op = match kind {
      KwBinR => BinR(binding, module, name),
      KwBinL => BinL(binding, module, name),
      KwUnary => Un(binding, module, name),
      _ => unreachable!(),
    };
    match out.entry(sym) {
      Entry::Vacant(e) => {
        e.insert(op);
      }
      Entry::Occupied(old) => {
        return err_msg(
          format!(
            "Multiple definitions of operator `{}`\nold: {:?}\nnew: {:?}",
            sym, old, op
          ),
          span,
        );
      }
    }
  }
  Ok(out)
}

fn parse_op<'t>(
  lexer: &mut logos::Lexer<'t, Token<'t>>,
) -> Result<(&'t str, usize, &'t str, &'t str), Error> {
  use Token::*;
  let sym = match expect!(lexer, Sym(_), "Expected an operator") {
    Sym(s) => s,
    _ => unreachable!(),
  };
  let binding = match expect!(lexer, Int(_), "Expected an integer strength") {
    Int(s) => s.parse().unwrap(),
    _ => unreachable!(),
  };
  let module = match expect!(lexer, ProperName(_), "Expected a proper name") {
    ProperName(s) => s,
    _ => unreachable!(),
  };
  expect!(lexer, Dot, "Expected a dot");
  let name = match expect!(lexer, Name(_), "Expected a name") {
    Name(s) => s,
    _ => unreachable!(),
  };
  Ok((sym, binding, module, name))
}

#[cfg(test)]
mod test {
  use super::*;

  macro_rules! test_p {
    ($name:ident, $src:literal) => {
      #[test]
      fn $name() {
        let src = $src;
        let tokens = Token::lexer($src).collect::<Vec<_>>();
        let res = parse($src);
        assert!(
          res.is_ok(),
          "\n{:?} should parse\ngave:\n{:?}\nTokens: {:?}",
          src,
          res,
          tokens
        );
      }
    };
  }

  macro_rules! test_f {
    ($name:ident, $src:literal) => {
      #[test]
      fn $name() {
        let src = $src;
        let tokens = Token::lexer($src).collect::<Vec<_>>();
        let res = parse($src);
        assert!(
          res.is_err(),
          "\n{:?} should fail\ngave:\n{:?}\nTokens: {:?}",
          src,
          res,
          tokens
        );
      }
    };
  }

  test_p!(empty, "");
  test_p!(simple_1, "unary - 2 Preamble._neg");
  test_p!(
    simple_2,
    "binr + 2 Preamble._add     binl # 1 Preamble._call_flip"
  );
  test_p!(
    simple_3,
    "binr ++++ 7 Preamble._add     binl #+!!! 1 Preamble._call_flip"
  );
  test_p!(
    simple_4,
    "binr >>= 6 Preamble._bind     binl <$> 1 Preamble._map"
  );

  test_f!(
    multiple,
    "binr + 2 Preamble._add     binr + 2 Preamble._sub"
  );
}
