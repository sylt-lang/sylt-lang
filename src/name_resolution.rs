// Do name resolution
// Type check - needs to be memory efficient
// Two scopes? Module and function?

#![allow(dead_code)]
use crate::ast;
use crate::error::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VarId(usize);

#[derive(Debug)]
pub struct StackFrame(usize);

#[derive(Debug, Clone)]
pub struct Var<'t> {
  global: bool,
  name: &'t str,
  def_at: Span,
  id: VarId,
  usages: Vec<Span>,
}

#[derive(Debug, Clone)]
pub enum Def {
  Def {
    name: VarId,
    args: Vec<VarId>,
    body: Expr,
    span: Span,
  },
  Type {
    // thing: TypeId,
    // args: Vec<TypeId>,
    // body: TypeId,
    // span: Span,
  },
  Enum {
    // thing: TypeId,
    // args: Vec<VarId>,
    // // constructors: Vec<EnumConst<'t>>,
    // span: Span,
  },
}

#[derive(Debug, Clone)]
pub enum Expr {
  EInt(i64, Span),
  Var(VarId, Span),

  Un(ast::UnOp, Box<Expr>),
  Bin(ast::BinOp, Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone)]
pub struct Ctx<'t> {
  vars: Vec<Var<'t>>,
  stack: Vec<VarId>,
}

impl<'t> Ctx<'t> {
  fn new() -> Self {
    Self { vars: vec![], stack: vec![] }
  }

  fn push_var(&mut self, global: bool, name: &'t str, def_at: Span) -> VarId {
    let id = VarId(self.vars.len());
    self
      .vars
      .push(Var { global, name, def_at, id, usages: vec![] });
    self.stack.push(id);
    id
  }

  fn push_local_var(&mut self, name: &'t str, def_at: Span) -> VarId {
    self.push_var(false, name, def_at)
  }

  fn push_global_var(&mut self, name: &'t str, def_at: Span) -> VarId {
    self.push_var(true, name, def_at)
  }

  fn read_var(&mut self, name: &'t str, at: Span) -> Option<VarId> {
    match self.find_var(name) {
      Some(VarId(v)) => {
        self.vars[v].usages.push(at);
        return Some(VarId(v));
      }
      None => None,
    }
  }

  fn find_var(&mut self, name: &'t str) -> Option<VarId> {
    for VarId(v) in self.stack.iter().rev() {
      if self.vars[*v].name == name {
        return Some(VarId(*v));
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
      match ctx.read_var(name, at) {
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
    ast::Def::Def { ty: _, name: ast::Name(name, at), args, body, span } => {
      let name = ctx.find_var(name).unwrap();
      let frame = ctx.push_frame();
      let args = args
        .into_iter()
        .map(|ast::Name(name, at)| ctx.push_local_var(name, at))
        .collect();
      let body = resolve_expr(ctx, body)?;
      ctx.pop_frame(frame);
      Def::Def { name, args, body, span }
    }
    ast::Def::Type { name, args, body, span } => todo!(),
    ast::Def::Enum { name, args, constructors, span } => todo!(),
  })
}

pub fn resolve<'t>(defs: Vec<ast::Def<'t>>) -> Result<(Ctx<'t>, Vec<Def>), Vec<Error>> {
  let mut ctx = Ctx::new();
  let mut out = vec![];
  let mut errs = vec![];
  for (name, at) in defs.iter().map(|d| d.name()) {
    match ctx.find_var(name) {
      Some(VarId(old)) => errs.push(error_multiple_def(name, ctx.vars[old].def_at, at)),
      None => { ctx.push_global_var(name, at); },
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
