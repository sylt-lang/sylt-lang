use std::collections::BTreeMap;
use std::io::{Result, Write};

use crate::ast;
use crate::error::Span;
use crate::name_resolution::*;
use crate::type_checker::*;

#[derive(Debug, Clone)]
struct GenVar {
  var_name: String,
  foreign_name: String,
}

#[derive(Debug, Copy, Clone)]
struct TmpVar(usize);

impl TmpVar {
  pub fn zero() -> Self {
    TmpVar(0)
  }

  pub fn out(&self) -> String {
    format!("_tmp_{}", self.0)
  }

  pub fn next(&self) -> TmpVar {
    TmpVar(self.0 + 1)
  }
}

#[derive(Debug, Copy, Clone)]
struct Ctx<'a> {
  gen_vars: &'a Vec<GenVar>,

  fields: &'a BTreeMap<FieldId, &'a str>,
}

impl<'a> Ctx<'a> {
  fn var(&self, NameId(slot): NameId) -> &str {
    &self.gen_vars[slot].var_name
  }

  fn foreign_name(&self, NameId(slot): NameId) -> &str {
    &self.gen_vars[slot].foreign_name
  }

  fn field(&self, slot: FieldId) -> &str {
    &self.fields[&slot]
  }
}

const PREAMBLE: &'static str = include_str!("pramble.lua");

pub fn gen<'t>(
  out: &mut dyn Write,
  _types: &[Node<'t>],
  names: &[Name<'t>],
  fields: &BTreeMap<FieldId, &'t str>,
  named_ast: &[Def],
) -> Result<()> {
  writeln!(out, "-- BEGIN PREAMBLE\n{}\n-- END PREAMBLE\n\n", PREAMBLE)?;

  let gen_vars = names
    .iter()
    .enumerate()
    .map(|(i, name)| GenVar {
      var_name: format!("_{}_{}", i, name.name),
      foreign_name: format!("{}", name.name),
    })
    .collect();
  let ctx = Ctx { gen_vars: &gen_vars, fields };
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
      _ => { /* Do nothing */ }
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
    Def::ForiegnDef { name, foreign_block, .. } => match foreign_block {
      Some(foreign_block) => write!(out, "{} = {}\n", ctx.var(*name), foreign_block,)?,
      None => write!(
        out,
        "{} = {} -- FOREIGN\n",
        ctx.var(*name),
        ctx.foreign_name(*name)
      )?,
    },

    Def::Enum { .. } | Def::Type { .. } | Def::ForeignType { .. } => (),
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

fn gen_let_binding(
  out: &mut dyn Write,
  ctx: Ctx,
  tmp: TmpVar,
  bind_value: &Expr,
  binding: &Pattern,
  next_value: &Expr,
) -> Result<()> {
  write!(out, "local {}", tmp.out())?;
  write!(out, " = ")?;
  gen_expr(out, ctx, bind_value)?;
  write!(out, "\n")?;
  gen_pat(out, tmp.out(), ctx, binding)?;
  match next_value {
    Expr::Let { bind_value, binding, next_value } => {
      gen_let_binding(out, ctx, tmp.next(), bind_value, binding, next_value)
    }
    _ => {
      write!(out, "return ")?;
      gen_expr(out, ctx, next_value)
    }
  }
}

fn gen_expr(out: &mut dyn Write, ctx: Ctx, body: &Expr) -> Result<()> {
  Ok(match body {
    Expr::Let { bind_value, binding, next_value } => {
      // TODO: Better code-gen for this, all bindings can be moved to the top of the expressions
      // since there shouldn't be any sideeffects here, right? RIGHT?
      //
      // ASSUMPTION: Let bindings always open a function and are all at the start of that function
      write!(out, "( function()\n")?;
      gen_let_binding(out, ctx, TmpVar::zero(), bind_value, binding, next_value)?;
      write!(out, "\nend )()\n")?;
    }
    Expr::EBool(b, _) => write!(out, "{}", b)?,
    Expr::EInt(i, _) => write!(out, "{}", i)?,
    Expr::EReal(f, _) => write!(out, "{}", f)?, // TODO: Is this stable?
    Expr::EStr(s, _) => write!(out, "{:?}", s)?, // TODO: Is this stable?
    Expr::Var(name, _) => write!(out, "{}", ctx.var(*name))?,
    Expr::EnumConst { ty_name: _, const_name, value, span: _ } => {
      if let Some((value, _)) = value {
        write!(out, "Enum.new( \"{}\", (", ctx.var(*const_name))?;
        gen_expr(out, ctx, value)?;
        write!(out, ") )")?;
      } else {
        write!(out, "Enum.new( \"{}\", nil )", ctx.var(*const_name))?;
      }
    }
    Expr::Un(ast::UnOp::Neg(_), expr, _) => {
      write!(out, "(-")?;
      gen_expr(out, ctx, expr)?;
      write!(out, ")")?;
    }
    Expr::Bin(ast::BinOp::Call(_), a, b, _) => {
      write!(out, "(")?;
      write!(out, "(")?;
      gen_expr(out, ctx, a)?;
      write!(out, ")")?;
      write!(out, "(")?;
      gen_expr(out, ctx, b)?;
      write!(out, ")")?;
      write!(out, ")")?;
    }
    Expr::Bin(op, a, b, _) => {
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
    Expr::Record { to_extend: None, fields, span: _ } => gen_record_constant(out, ctx, fields)?,
    Expr::Record { to_extend: Some(to_extend), fields, span: _ } => {
      write!(out, "sy_record_merge( ")?;
      gen_expr(out, ctx, to_extend)?;
      write!(out, ", ")?;
      gen_record_constant(out, ctx, fields)?;
      write!(out, ")")?
    }
    Expr::Match { value, branches, span } => {
      todo!();
    }
  })
}

fn gen_record_constant(
  out: &mut dyn Write,
  ctx: Ctx,
  fields: &[((Span, FieldId), Expr)],
) -> Result<()> {
  write!(out, "{{")?;
  for ((_, field), value) in fields.iter() {
    write!(out, "[\"{}\"] = ", ctx.field(*field))?;
    gen_expr(out, ctx, value)?;
    write!(out, ",")?;
  }
  write!(out, "}}")
}

fn gen_pat(out: &mut dyn Write, curr: String, ctx: Ctx, binding: &Pattern) -> Result<()> {
  Ok(match binding {
    Pattern::Empty(_) => (),
    Pattern::Var(name, inner, _) => {
      write!(out, "local {} = {}\n", ctx.var(*name), curr)?;
      match inner {
        Some(inner) => gen_pat(out, curr, ctx, inner)?,
        None => (),
      }
    }
    Pattern::EnumConst { inner: Some(inner), .. } => {
      gen_pat(out, format!("{}[2]", curr), ctx, &*inner.0)?
    }
    Pattern::EnumConst { inner: None, .. } => (),
    Pattern::Record(fields, _) => {
      for (field, _, pat) in fields {
        let field = ctx.field(*field);
        gen_pat(out, format!("{}[\"{}\"]", curr, field), ctx, pat)?;
      }
    }
    Pattern::PBool(x, _) => write!(out, "_sy_intern_check_pattern(0, {}, {})\n", x, curr)?,
    Pattern::PInt(x, _) => write!(out, "_sy_intern_check_pattern(1, {}, {})\n", x, curr)?,
    Pattern::PReal(x, _) => write!(out, "_sy_intern_check_pattern(2, {}, {})\n", x, curr)?,
    Pattern::PStr(x, _) => write!(out, "_sy_intern_check_pattern(3, {}, {})\n", x, curr)?,
  })
}
