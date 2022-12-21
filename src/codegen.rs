use std::io::{Result, Write};

use crate::ast;
use crate::name_resolution::*;
use crate::type_checker::*;

#[derive(Debug, Clone)]
struct GenVar(String);

#[derive(Debug, Copy, Clone)]
struct Ctx<'a> {
  gen_vars: &'a Vec<GenVar>,
}

impl<'a> Ctx<'a> {
  fn var(&self, NameId(slot): NameId) -> &str {
    let GenVar(s) = &self.gen_vars[slot];
    s
  }
}

pub fn gen<'t>(
  out: &mut dyn Write,
  _types: &[Node<'t>],
  names: &[Name<'t>],
  named_ast: &[Def],
) -> Result<()> {
  let gen_vars = names
    .iter()
    .enumerate()
    .map(|(i, name)| GenVar(format!("_{}_{}", i, name.name)))
    .collect();
  let ctx = Ctx { gen_vars: &gen_vars };
  for def in named_ast {
    gen_def(out, ctx, def)?;
  }

  for def in named_ast {
    match def {
      // TODO: Fix this
      Def::Def { name: name @ NameId(slot), .. }
        if names[*slot].name == "main" && names[*slot].is_type == false =>
      {
        write!(out, "print({}) -- TODO, don't\n", ctx.var(*name))?;
      }
      Def::Def { .. } | Def::ForiegnDef { .. } | Def::Type { .. } | Def::ForeignType { .. } => { /* Do nothing */
      }
    }
  }
  Ok(())
}

fn gen_def(out: &mut dyn Write, ctx: Ctx, def: &Def) -> Result<()> {
  Ok(match def {
    Def::Def { name, args, body, .. } => {
      write!(out, "-- BEGIN {}\n", ctx.var(*name))?;
      write!(out, "{} = ", ctx.var(*name))?;
      gen_function(out, ctx, args, body)?;
      write!(out, "-- END {}\n", ctx.var(*name))?;
    }
    Def::ForiegnDef { .. } => todo!(),
    Def::Type { .. } | Def::ForeignType { .. } => (),
  })
}

fn gen_function(out: &mut dyn Write, ctx: Ctx, args: &[NameId], body: &Expr) -> Result<()> {
  if args.len() > 0 {
    write!(out, "function({})\n", ctx.var(args[0]))?;
    write!(out, "return ")?;
    gen_function(out, ctx, &args[1..], body)?;
    write!(out, "end\n")?;
  } else {
    gen_expr(out, ctx, body)?;
    write!(out, "\n")?;
  }
  Ok(())
}

fn gen_expr(out: &mut dyn Write, ctx: Ctx, body: &Expr) -> Result<()> {
  Ok(match body {
    Expr::EInt(i, _) => write!(out, "{}", i)?,
    Expr::Var(name, _) => write!(out, "{}", ctx.var(*name))?,
    Expr::Un(ast::UnOp::Neg(_), expr) => {
      write!(out, "(-")?;
      gen_expr(out, ctx, expr)?;
      write!(out, ")")?;
    }
    Expr::Bin(ast::BinOp::Call(_), a, b) => {
      write!(out, "(")?;
      write!(out, "(")?;
      gen_expr(out, ctx, a)?;
      write!(out, ")")?;
      write!(out, "(")?;
      gen_expr(out, ctx, b)?;
      write!(out, ")")?;
      write!(out, ")")?;
    }
    Expr::Bin(op, a, b) => {
      write!(out, "(")?;
      gen_expr(out, ctx, a)?;
      write!(
        out,
        "{}",
        match op {
          ast::BinOp::Add(_) => "+",
          ast::BinOp::Sub(_) => "-",
          ast::BinOp::Div(_) => "/",
          ast::BinOp::Mul(_) => "*",
          ast::BinOp::Call(_) => unreachable!(),
        }
      )?;
      gen_expr(out, ctx, b)?;
      write!(out, ")")?;
    }
  })
}
