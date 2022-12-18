// Do name resolution
// Type check - needs to be memory efficient
// Two scopes? Module and function?

use crate::ast;
use crate::error::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct NameId(pub usize);

#[derive(Debug)]
pub struct StackFrame(usize);

#[derive(Debug, Clone)]
pub struct Name<'t> {
  pub name: &'t str,
  pub is_type: bool,
  pub def_at: Span,
  pub usages: Vec<Span>,
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
    span: Span,
  },
}

#[derive(Debug, Clone)]
pub enum Type {
  TApply(Box<Type>, Box<Type>, Span),

  TNode(NameId, Span),
  TFunction(Box<Type>, Box<Type>, Span),

  TInt(Span),
  TForeign(Span),
}

impl Type {
  pub fn span(&self) -> Span {
    match self {
      Type::TApply(_, _, span)
      | Type::TNode(_, span)
      | Type::TFunction(_, _, span)
      | Type::TInt(span)
      | Type::TForeign(span) => *span,
    }
  }
}

#[derive(Debug, Clone)]
pub enum Expr {
  EInt(i64, Span),
  Var(NameId, Span),

  Un(ast::UnOp, Box<Expr>),
  Bin(ast::BinOp, Box<Expr>, Box<Expr>),
}

impl Expr {
  pub fn span(&self) -> Span {
    match self {
      Expr::EInt(_, span) | Expr::Var(_, span) => *span,
      Expr::Un(ast::UnOp::Neg(span), a) => span.merge(a.span()),
      Expr::Bin(_, a, b) => a.span().merge(b.span()),
    }
  }
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

  fn push_var(&mut self, _global: bool, is_type: bool, name: &'t str, def_at: Span) -> NameId {
    let id = NameId(self.names.len());
    self
      .names
      .push(Name { is_type, name, def_at, usages: vec![] });
    self.stack.push(id);
    id
  }

  fn push_local_var(&mut self, name: &'t str, def_at: Span) -> NameId {
    self.push_var(false, false, name, def_at)
  }

  fn push_global_var(&mut self, name: &'t str, def_at: Span) -> NameId {
    self.push_var(true, false, name, def_at)
  }

  fn push_local_type(&mut self, name: &'t str, def_at: Span) -> NameId {
    self.push_var(false, true, name, def_at)
  }

  fn push_global_type(&mut self, name: &'t str, def_at: Span) -> NameId {
    self.push_var(true, true, name, def_at)
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
    ast::Type::TEmpty(at) => {
      let frame = ctx.push_frame();
      let node = ctx.push_local_type("_FILLED_IN_", at);
      ctx.pop_frame(frame);
      Type::TNode(node, at)
    }
    ast::Type::TCustom { name: ast::ProperName(name, at), args, span: _ } if name == "Int" && args.len() == 0 => {
        Type::TInt(at)
    }
    ast::Type::TCustom { name: ast::ProperName(name, at), args, span } => {
      let node = match ctx.read_name(name, at) {
        Some(var) => Type::TNode(var, at),
        None => return error_no_var(name, at),
      };
      if args.is_empty() {
        node
      } else {
        let mut args = args
          .into_iter()
          .map(|arg| resolve_ty(ctx, arg))
          .collect::<RRes<Vec<Type>>>()?;

        let mut acc = args.pop().unwrap();
        while !args.is_empty() {
          acc = Type::TApply(Box::new(args.pop().unwrap()), Box::new(acc), span);
        }
        Type::TApply(Box::new(node), Box::new(acc), span)
      }
    }
    ast::Type::TVar(ast::Name(name, at), span) => Type::TNode(
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
        .map(|ast::Name(name, at)| ctx.push_local_var(name, at))
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
        .map(|ast::Name(name, at)| ctx.push_local_type(name, at))
        .collect();
      let body = resolve_ty(ctx, body)?;
      ctx.pop_frame(frame);

      Def::Type { name, args, body, span }
    }

    ast::Def::ForiegnType { name: ast::ProperName(name, _), span } => {
      let name = ctx.find_name(name).unwrap();

      Def::ForeignType { name, span }
    }

    ast::Def::Enum { .. } => todo!(),
  })
}

pub fn resolve<'t>(defs: Vec<ast::Def<'t>>) -> Result<(Vec<Name<'t>>, Vec<Def>), Vec<Error>> {
  let mut ctx = Ctx::new();
  let mut out = vec![];
  let mut errs = vec![];
  for d in defs.iter() {
    let (name, at) = d.name();
    // TODO, handle type definitions here
    match (ctx.find_name(name), d) {
      (Some(NameId(old)), _) => {
        errs.push(error_multiple_def(name, ctx.names[old].def_at, at));
      }
      (None, ast::Def::Def { .. } | ast::Def::ForiegnDef { .. }) => {
        ctx.push_global_var(name, at);
      }
      (None, ast::Def::Type { .. } | ast::Def::ForiegnType { .. } | ast::Def::Enum { .. }) => {
        ctx.push_global_type(name, at);
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
    Ok((ctx.names, out))
  } else {
    Err(errs)
  }
}

// TODO, translate some programs
