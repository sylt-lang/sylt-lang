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
    ty: Type,
    name: NameId,
    args: Vec<NameId>,
    body: Expr,
    span: Span,
  },
  ForiegnDef {
    ty: Type,
    name: NameId,
    span: Span,
  },
  Type {
    name: NameId,
    args: Vec<NameId>,
    body: Type,
    span: Span,
  },
  ForeignType {
    name: NameId,
    args: Vec<NameId>,
    span: Span,
  },
}

#[derive(Debug, Clone)]
pub enum Type {
  TCustom {
    name: NameId,
    args: Vec<Type>,
    span: Span,
  },
  TVar(NameId, Span),
  TFunction(Box<Type>, Box<Type>, Span),
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

fn resolve_ty<'t>(ctx: &mut Ctx<'t>, ty: ast::Type<'t>) -> RRes<Type> {
  Ok(match ty {
    ast::Type::TEmpty(at) => Type::TVar(ctx.push_local_name("_FILLED_IN_", at), at),
    ast::Type::TCustom { name: ast::ProperName(name, at), args, span } => {
      let name = match ctx.read_name(name, at) {
        Some(var) => var,
        None => return error_no_var(name, at),
      };
      let args = args
        .into_iter()
        .map(|arg| resolve_ty(ctx, arg))
        .collect::<RRes<Vec<Type>>>()?;
      Type::TCustom { name, args, span }
    }
    ast::Type::TVar(ast::Name(name, at), span) => Type::TVar(
      match ctx.read_name(name, at) {
        Some(var) => var,
        None => return error_no_var(name, at),
      },
      span,
    ),
    ast::Type::TFunction(a, b, span) => Type::TFunction(
      Box::new(resolve_ty(ctx, *a)?),
      Box::new(resolve_ty(ctx, *b)?),
      span,
    ),
  })
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
    ast::Def::Def { ty, name: ast::Name(name, _), args, body, span } => {
      let ty = resolve_ty(ctx, ty)?;
      let name = ctx.find_name(name).unwrap();
      let frame = ctx.push_frame();
      let args = args
        .into_iter()
        .map(|ast::Name(name, at)| ctx.push_local_name(name, at))
        .collect();
      let body = resolve_expr(ctx, body)?;
      ctx.pop_frame(frame);
      Def::Def { ty, name, args, body, span }
    }
    ast::Def::ForiegnDef { ty, name: ast::Name(name, _), span } => {
      let ty = resolve_ty(ctx, ty)?;
      let name = ctx.find_name(name).unwrap();
      Def::ForiegnDef { ty, name, span }
    }
    ast::Def::Type { name: ast::ProperName(name, _), args, body, span } => {
      let name = ctx.find_name(name).unwrap();

      let frame = ctx.push_frame();
      let args = args
        .into_iter()
        .map(|ast::Name(name, at)| ctx.push_local_name(name, at))
        .collect();
      let body = resolve_ty(ctx, body)?;
      ctx.pop_frame(frame);

      Def::Type { name, args, body, span }
    }

    ast::Def::ForiegnType { name: ast::ProperName(name, _), args, span } => {
      let name = ctx.find_name(name).unwrap();

      let frame = ctx.push_frame();
      let args = args
        .into_iter()
        .map(|ast::Name(name, at)| ctx.push_local_name(name, at))
        .collect();
      ctx.pop_frame(frame);

      Def::ForeignType { name, args, span }
    }

    ast::Def::Enum { .. } => todo!(),
  })
}

pub fn resolve<'t>(defs: Vec<ast::Def<'t>>) -> Result<(Ctx<'t>, Vec<Def>), Vec<Error>> {
  let mut ctx = Ctx::new();
  let mut out = vec![];
  let mut errs = vec![];
  for (name, at) in defs.iter().map(|d| d.name()) {
    // TODO, handle type definitions here
    match ctx.find_name(name) {
      Some(NameId(old)) => {
        errs.push(error_multiple_def(name, ctx.names[old].def_at, at));
      }
      None => {
        ctx.push_global_name(name, at);
      }
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
