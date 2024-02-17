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

  // Sync with lexer.rs
  #[regex("[-+*/'#<>=!&$#%?~^`|]+")]
  Sym(&'t str),
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Oper<'t> {
  BinR(usize, &'t str, &'t str),
  BinL(usize, &'t str, &'t str),
  Un(&'t str, &'t str),
}

pub fn err_msg<'t, A>(msg: String, span: core::ops::Range<usize>) -> Result<A, Error> {
  Err(Error::Special(format!("{}\nOffset: {:?}", msg, span)))
}

macro_rules! expect {
  ($lex:expr, $pat:pat, $msg:literal) => {{
    match ($lex.next(), $lex.span(), $lex.slice()) {
      (Some(Ok(x @ $pat)), _, _) => x,
      (_, s, t) => return err_msg(format!("{} - got {}", $msg.to_string(), t), s),
    }
  }};
}

pub type OpMap<'t> = BTreeMap<&'t str, Oper<'t>>;

pub fn parse<'t>(source: &'t str) -> Result<OpMap<'t>, Error> {
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
    let sym = match expect!(lexer, Sym(_), "Expected an operator") {
      Sym(s) => s,
      _ => unreachable!(),
    };
    let op = match kind {
      KwBinR => {
        let (binding, module, name) = parse_bin(&mut lexer)?;
        BinR(binding, module, name)
      }
      KwBinL => {
        let (binding, module, name) = parse_bin(&mut lexer)?;
        BinL(binding, module, name)
      }
      KwUnary => {
        let (module, name) = parse_un(&mut lexer)?;
        Un(module, name)
      }
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

fn parse_bin<'t>(
  lexer: &mut logos::Lexer<'t, Token<'t>>,
) -> Result<(usize, &'t str, &'t str), Error> {
  use Token::*;
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
  Ok((binding, module, name))
}

fn parse_un<'t>(lexer: &mut logos::Lexer<'t, Token<'t>>) -> Result<(&'t str, &'t str), Error> {
  use Token::*;
  let module = match expect!(lexer, ProperName(_), "Expected a proper name") {
    ProperName(s) => s,
    _ => unreachable!(),
  };
  expect!(lexer, Dot, "Expected a dot");
  let name = match expect!(lexer, Name(_), "Expected a name") {
    Name(s) => s,
    _ => unreachable!(),
  };
  Ok((module, name))
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
  test_p!(simple_1, "unary - Preamble._neg");
  test_p!(
    simple_2,
    "binr + 2 Preamble._add binl # 1 Preamble._call_flip"
  );
  test_p!(
    simple_3,
    "binr ++++ 7 Preamble._add binl #+!!! 1 Preamble._call_flip"
  );
  test_p!(
    simple_4,
    "binr >>= 6 Preamble._bind binl <$> 1 Preamble._map"
  );

  test_f!(multiple, "binr + 2 Preamble._add binr + 2 Preamble._sub");
  test_f!(syntax, "binr 3 + Preamble._add");
}
