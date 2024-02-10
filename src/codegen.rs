use std::collections::BTreeMap;
use std::io::{Result, Write};

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

const PREAMBLE: &'static str = include_str!("preamble.lua");

pub fn gen<'t>(
  out: &mut dyn Write,
  _types: &[Node<'t>],
  names: &[Name<'t>],
  fields: &BTreeMap<FieldId, &'t str>,
  named_ast: &[Def],
  gen_module: bool,
) -> Result<()> {
  writeln!(
    out,
    "-- BEGIN LUA PREAMBLE\n{}\n-- END LUA PREAMBLE\n\n",
    PREAMBLE
  )?;

  let gen_vars = names
    .iter()
    .enumerate()
    .map(|(i, name)| GenVar {
      var_name: format!("_{}_{}_{}", i, name.name.0, name.name.1),
      foreign_name: format!("{}", name.name.1),
    })
    .collect();
  let ctx = Ctx { gen_vars: &gen_vars, fields };
  // We special handle `main` and generate it after all other definitions - this lets us ignore
  // circular dependencies for the most part. Constants can still depend on eachother in ways that
  // might break. This change is so much smaller and faster than a more robust solution that
  // telling people to resolve these dependencies some other way is fine.
  //
  // I'm a bit worried because I'm starting to think about moving towards thunks in the code
  // generation - but that might cause other problems?
  let mut main = None;
  for def in named_ast {
    match def {
      Def::Def { name: NameId(slot), .. }
        if names[*slot].name.1 == "main" && names[*slot].is_type == false =>
      {
        main = Some(def);
      }
      _ => {
        gen_def(out, ctx, def)?;
      }
    }
  }
  if let Some(def) = main {
    gen_def(out, ctx, def)?;
  }

  // TODO[et]: Check it's the main module!
  let mut exports = vec![];
  for def in named_ast {
    match def {
      Def::Def { name: name @ NameId(slot), .. }
        if names[*slot].name.1 == "main" && names[*slot].is_type == false =>
      {
        exports.push(("main", ctx.var(*name)));
      }
      Def::Def { name: name @ NameId(slot), .. }
        if gen_module && names[*slot].name.1 == "update" && names[*slot].is_type == false =>
      {
        exports.push(("update", ctx.var(*name)));
      }
      Def::Def { name: name @ NameId(slot), .. }
        if gen_module && names[*slot].name.1 == "draw" && names[*slot].is_type == false =>
      {
        exports.push(("draw", ctx.var(*name)));
      }
      Def::Def { name: name @ NameId(slot), .. }
        if gen_module && names[*slot].name.1 == "init" && names[*slot].is_type == false =>
      {
        exports.push(("init", ctx.var(*name)));
      }
      _ => { /* Do nothing */ }
    }
  }
  if gen_module {
    writeln!(
      out,
      "return {{ {} }}",
      exports
        .into_iter()
        .map(|(lua_name, sy_name)| format!("[\"{}\"] = {}", lua_name, sy_name))
        .collect::<Vec<String>>()
        .join(", ")
    )
  } else {
    writeln!(
      out,
      "print({})",
      exports
        .into_iter()
        .map(|(_lua_name, sy_name)| format!("{}", sy_name))
        .collect::<Vec<String>>()
        .join(", ")
    )
  }
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

    Def::Enum { .. }
    | Def::Type { .. }
    | Def::ForeignType { .. }
    | Def::Class { .. }
    | Def::Instance { .. } => (),
  })
}

fn gen_function(out: &mut dyn Write, ctx: Ctx, args: &[Pattern], body: &Expr) -> Result<()> {
  if args.len() > 0 {
    let arg = "_arg".to_string();
    write!(out, "function({})\n", arg)?;
    gen_pat(out, arg, ctx, &args[0])?;
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
    Expr::EBool(b, _, _) => write!(out, "{}", b)?,
    Expr::EInt(i, _, _) => write!(out, "{}", i)?,
    Expr::EReal(f, _, _) => write!(out, "{}", f)?, // TODO: Is this stable?
    Expr::EStr(s, _, _) => write!(out, "{:?}", s)?, // TODO: Is this stable?
    Expr::Var(name, _) => write!(out, "{}", ctx.var(*name))?,
    Expr::EnumConst { ty_name: _, const_name, value, span: _ } => {
      if let Some((value, _)) = value {
        write!(out, "Sylt.Enum.new( \"{}\", (", ctx.field(*const_name))?;
        gen_expr(out, ctx, value)?;
        write!(out, ") )")?;
      } else {
        write!(out, "Sylt.Enum.new( \"{}\", nil )", ctx.field(*const_name))?;
      }
    }
    Expr::Call(a, b, _) => {
      write!(out, "(")?;
      write!(out, "(")?;
      gen_expr(out, ctx, a)?;
      write!(out, ")")?;
      write!(out, "(")?;
      gen_expr(out, ctx, b)?;
      write!(out, ")")?;
      write!(out, ")")?;
    }
    Expr::Record { to_extend: None, fields, span: _ } => gen_record_constant(out, ctx, fields)?,
    Expr::Record { to_extend: Some(to_extend), fields, span: _ } => {
      write!(out, "Sylt.Record.merge(")?;
      gen_expr(out, ctx, to_extend)?;
      write!(out, ", ")?;
      gen_record_constant(out, ctx, fields)?;
      write!(out, ")")?
    }
    Expr::If { condition, bool: _, t, f, span: _ } => {
      write!(out, "(function() if ")?;
      gen_expr(out, ctx, condition)?;
      write!(out, " then return ")?;
      gen_expr(out, ctx, t)?;
      write!(out, " else return ")?;
      gen_expr(out, ctx, f)?;
      write!(out, " end end)()")?;
    }
    Expr::Match { value, branches, span } => {
      write!(out, "(function(match_value)\n")?;
      write!(out, "local succ = nil\nlocal _msg = nil\n")?;
      for WithBranch { pattern, condition, value, bool: _, span: _ } in branches.iter() {
        write!(out, "succ, _msg = pcall(function()\n    ")?;
        gen_pat(out, "match_value".to_string(), ctx, pattern)?;
        write!(out, "end)\n")?;
        write!(out, "if succ then ")?;
        if let Some(condition) = condition {
          gen_pat(out, "match_value".to_string(), ctx, pattern)?;
          write!(out, "if ")?;
          gen_expr(out, ctx, condition)?;
          write!(out, " then\n")?;

          write!(out, "return ")?;
          gen_expr(out, ctx, value)?;

          write!(out, " end\n")?;
        } else {
          gen_pat(out, "match_value".to_string(), ctx, pattern)?;
          write!(out, "return ")?;
          gen_expr(out, ctx, value)?;
        }
        write!(out, "\nend\n")?;
      }
      write!(out, "print(\"NO BRANCH!\", \"{:?}\")\n", span)?;
      write!(out, "end)(")?;
      gen_expr(out, ctx, value)?;
      write!(out, ")\n")?;
    }
    Expr::Lambda { args, body, span: _ } => {
      gen_function(out, ctx, args, body)?;
    }
  })
}

fn gen_record_constant(
  out: &mut dyn Write,
  ctx: Ctx,
  fields: &[((Span, FieldId), Expr)],
) -> Result<()> {
  write!(out, "Sylt.Record.new({{")?;
  for ((_, field), value) in fields.iter() {
    write!(out, "[\"{}\"] = ", ctx.field(*field))?;
    gen_expr(out, ctx, value)?;
    write!(out, ",")?;
  }
  write!(out, "}})")
}

fn gen_pat(out: &mut dyn Write, curr: String, ctx: Ctx, binding: &Pattern) -> Result<()> {
  Ok(match binding {
    Pattern::Empty(_, _) => write!(out, "Sylt.identity({})\n", curr)?,
    Pattern::Var(name, inner, _) => {
      write!(out, "local {} = {}\n", ctx.var(*name), curr)?;
      match inner {
        Some(inner) => gen_pat(out, curr, ctx, inner)?,
        None => (),
      }
    }
    Pattern::EnumConst { inner: Some(inner), const_name, .. } => gen_pat(
      out,
      format!(
        "Sylt.Pattern.check_const({}, \"{}\")",
        curr,
        ctx.field(*const_name)
      ),
      ctx,
      &*inner.0,
    )?,
    Pattern::EnumConst { inner: None, const_name, .. } => write!(
      out,
      "Sylt.Pattern.check_const({}, \"{}\")\n",
      curr,
      ctx.field(*const_name)
    )?,
    Pattern::Record(fields, _) => {
      for (field, _, pat) in fields {
        let field = ctx.field(*field);
        gen_pat(out, format!("{}[\"{}\"]", curr, field), ctx, pat)?;
      }
    }
    Pattern::PBool(x, _, _) => write!(out, "Sylt.Pattern.check_pattern(0, {}, {})\n", x, curr)?,
    Pattern::PInt(x, _, _) => write!(out, "Sylt.Pattern.check_pattern(1, {}, {})\n", x, curr)?,
    Pattern::PReal(x, _, _) => write!(out, "Sylt.Pattern.check_pattern(2, {}, {})\n", x, curr)?,
    Pattern::PStr(x, _, _) => write!(out, "Sylt.Pattern.check_pattern(3, {}, {})\n", x, curr)?,
  })
}
