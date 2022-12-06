// Do name resolution
// Type check - needs to be memory efficient
// Two scopes? Module and function?

#![allow(dead_code)]
use crate::ast;
use crate::error::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct NameId(usize);

#[derive(Debug)]
pub struct StackFrame(usize);

#[derive(Debug, Clone)]
pub struct Name<'t> {
  global: bool,
  name: &'t str,
  def_at: Span,
  id: NameId,
  usages: Vec<Span>,
}

#[derive(Debug, Clone)]
pub enum Def {
  Def {
    name: NameId,
    args: Vec<NameId>,
    body: Expr,
    span: Span,
  },
  ForiegnDef {
    name: NameId,
    span: Span,
  },
  Type {},
}

#[derive(Debug, Clone)]
pub enum Expr {
  EInt(i64, Span),
  Var(NameId, Span),

  Un(ast::UnOp, Box<Expr>),
  Bin(ast::BinOp, Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone)]
pub struct Ctx<'t> {
  names: Vec<Name<'t>>, // TODO: Lookups can be done in almost constant time compared to linear time
  stack: Vec<NameId>,
}

impl<'t> Ctx<'t> {
  fn new() -> Self {
    Self { names: vec![], stack: vec![] }
  }

  fn push_var(&mut self, global: bool, name: &'t str, def_at: Span) -> NameId {
    let id = NameId(self.names.len());
    self
      .names
      .push(Name { global, name, def_at, id, usages: vec![] });
    self.stack.push(id);
    id
  }

  fn push_local_name(&mut self, name: &'t str, def_at: Span) -> NameId {
    self.push_var(false, name, def_at)
  }

  fn push_global_name(&mut self, name: &'t str, def_at: Span) -> NameId {
    self.push_var(true, name, def_at)
  }

  fn read_name(&mut self, name: &'t str, at: Span) -> Option<NameId> {
    match self.find_name(name) {
      Some(NameId(v)) => {
        self.names[v].usages.push(at);
        return Some(NameId(v));
      }
      None => None,
    }
  }

  fn find_name(&mut self, name: &'t str) -> Option<NameId> {
    for NameId(v) in self.stack.iter().rev() {
      if self.names[*v].name == name {
        return Some(NameId(*v));
      }
    }
    None
  }

  fn push_frame(&self) -> StackFrame {
    StackFrame(self.stack.len())
  }

  fn pop_frame(&mut self, StackFrame(n): StackFrame) {
    self.stack.truncate(n);
  }
}

type RRes<A> = Result<A, Error>;

fn error_no_var<'t, A>(name: &'t str, span: Span) -> RRes<A> {
  Err(Error::ResUnknown { name: name.to_string(), span })
}

fn error_multiple_def<'t>(name: &'t str, original: Span, new: Span) -> Error {
  Error::ResMultiple { name: name.to_string(), original, new }
}


fn resolve_expr<'t>(ctx: &mut Ctx<'t>, def: ast::Expr<'t>) -> RRes<Expr> {
  Ok(match def {
    ast::Expr::EInt(value, span) => Expr::EInt(value, span),
    ast::Expr::Var(ast::Name(name, at), span) => Expr::Var(
      match ctx.read_name(name, at) {
        Some(var) => var,
        None => return error_no_var(name, at),
      },
      span,
    ),
    ast::Expr::Un(op, expr) => Expr::Un(op, Box::new(resolve_expr(ctx, *expr)?)),
    ast::Expr::Bin(op, a, b) => Expr::Bin(
      op,
      Box::new(resolve_expr(ctx, *a)?),
      Box::new(resolve_expr(ctx, *b)?),
    ),
  })
}

fn resolve_def<'t>(ctx: &mut Ctx<'t>, def: ast::Def<'t>) -> RRes<Def> {
  Ok(match def {
    ast::Def::Def { ty: _, name: ast::Name(name, _), args, body, span } => {
      let name = ctx.find_name(name).unwrap();
      let frame = ctx.push_frame();
      let args = args
        .into_iter()
        .map(|ast::Name(name, at)| ctx.push_local_name(name, at))
        .collect();
      let body = resolve_expr(ctx, body)?;
      ctx.pop_frame(frame);
      Def::Def { name, args, body, span }
    }
    ast::Def::ForiegnDef { ty: _, name: ast::Name(name, _), span } => {
      let name = ctx.find_name(name).unwrap();
      Def::ForiegnDef { name, span }
    }
    ast::Def::Type { .. } 
    | ast::Def::ForiegnType { .. } 
    | ast::Def::Enum { .. } => Def::Type {} ,
  })
}

pub fn resolve<'t>(defs: Vec<ast::Def<'t>>) -> Result<(Ctx<'t>, Vec<Def>), Vec<Error>> {
  let mut ctx = Ctx::new();
  let mut out = vec![];
  let mut errs = vec![];
  for (name, at) in defs.iter().map(|d| d.name()) {
    // TODO, handle type definitions here
    match ctx.find_name(name) {
      Some(NameId(old)) => errs.push(error_multiple_def(name, ctx.names[old].def_at, at)),
      None => { ctx.push_global_name(name, at); },
    }
  }
  for def in defs {
    match resolve_def(&mut ctx, def) {
      Err(err) => errs.push(err),
      Ok(o) => out.push(o),
    }
  }
  if errs.is_empty() {
    Ok((ctx, out))
  } else {
    Err(errs)
  }
}

// TODO, translate some programs
