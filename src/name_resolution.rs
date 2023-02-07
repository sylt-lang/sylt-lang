// Do name resolution
// Type check - needs to be memory efficient
// Two scopes? Module and function?

use std::collections::BTreeMap;

use crate::ast;
use crate::error::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct NameId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct FieldId(pub usize);

#[derive(Debug)]
pub struct StackFrame(usize);

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct Name<'t> {
  pub name: &'t str,
  pub is_type: bool,
  pub is_foreign: bool,
  pub is_generic: bool,
  pub def_at: Span,
  pub usages: Vec<Span>,
}

#[derive(Debug, Clone)]
pub enum Def {
  Def {
    ty: Type,
    name: NameId,
    args: Vec<Pattern>,
    body: Expr,
    span: Span,
  },
  ForiegnDef {
    ty: Type,
    name: NameId,
    span: Span,
    foreign_block: Option<String>,
  },
  Type {
    name: NameId,
    args: Vec<NameId>,
    body: Type,
    span: Span,
  },
  Enum {
    name: NameId,
    args: Vec<NameId>,
    constructors: Vec<EnumConst>,
    span: Span,
  },
  ForeignType {
    name: NameId,
    args: Vec<NameId>,
    span: Span,
  },
}

#[derive(Debug, Clone)]
pub struct EnumConst {
  pub tag: NameId,
  pub ty: Option<Type>,
  pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Type {
  TApply(Box<Type>, Box<Type>, Span),

  TNode(NameId, Span),
  TFunction(Box<Type>, Box<Type>, Span),
  TRecord {
    fields: Vec<(Span, FieldId, Type)>,
    span: Span,
  },

  TInt(Span),
  TReal(Span),
  TStr(Span),
  TBool(Span),
}

#[derive(Debug, Clone)]
pub enum Pattern {
  Empty(Span),
  Var(NameId, Option<Box<Pattern>>, Span),

  EnumConst {
    ty_name: NameId,
    const_name: NameId,
    inner: Option<(Box<Pattern>, Type)>,
    span: Span,
  },

  Record(Vec<(FieldId, Span, Pattern)>, Span),

  PBool(bool, Span),
  PInt(i64, Span),
  PReal(f64, Span),
  PStr(String, Span),
}

impl Pattern {
  pub fn span(&self) -> Span {
    match self {
      Pattern::Empty(span)
      | Pattern::Var(_, _, span)
      | Pattern::EnumConst { span, .. }
      | Pattern::PBool(_, span)
      | Pattern::PInt(_, span)
      | Pattern::PReal(_, span)
      | Pattern::PStr(_, span)
      | Pattern::Record(_, span) => *span,
    }
  }
}

#[derive(Debug, Clone)]
pub struct WithBranch {
  pub pattern: Pattern,
  pub condition: Option<Expr>,
  pub value: Expr,
  pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Expr {
  EBool(bool, Span),
  EInt(i64, Span),
  EReal(f64, Span),
  EStr(String, Span),
  Var(NameId, Span),

  Record {
    to_extend: Option<Box<Expr>>,
    fields: Vec<((Span, FieldId), Expr)>,
    span: Span,
  },

  EnumConst {
    ty_name: NameId,
    const_name: NameId,
    value: Option<(Box<Expr>, Type)>,
    span: Span,
  },

  Let {
    bind_value: Box<Expr>,
    binding: Pattern,
    next_value: Box<Expr>,
  },

  Match {
    value: Box<Expr>,

    // Non-empty
    branches: Vec<WithBranch>,
    span: Span,
  },

  Lambda {
    args: Vec<Pattern>,
    body: Box<Expr>,
    span: Span,
  },

  Un(ast::UnOp, Box<Expr>, Span),
  Bin(ast::BinOp, Box<Expr>, Box<Expr>, Span),
}

#[derive(Debug, Clone)]
pub struct Ctx<'t> {
  names: Vec<Name<'t>>, // TODO: Lookups can be done in almost constant time compared to linear time
  stack: Vec<NameId>,

  fields: (BTreeMap<FieldId, &'t str>, BTreeMap<&'t str, FieldId>),

  // NOTE[et]: I think I can do enums better. The type-checker should know as little as possible
  // about them. This can maybe be done by adding more functions to the syntax-tree? Or maybe I
  // should use a different approach. Maybe it's better if this is sent to the type-checker so we
  // don't have to propagate the type of the constructors in the annotated AST. Or maybe I'm
  // overthinking this?
  //
  // Ty -> Const -> Type
  enum_constructors: BTreeMap<NameId, BTreeMap<NameId, Option<Type>>>,
}

impl<'t> Ctx<'t> {
  fn new() -> Self {
    Self {
      names: vec![],
      stack: vec![],
      fields: (BTreeMap::new(), BTreeMap::new()),
      enum_constructors: BTreeMap::new(),
    }
  }

  fn find_field(&mut self, field: &'t str) -> FieldId {
    match self.fields.1.get(field) {
      Some(id) => return *id,
      None => {}
    }

    let id = FieldId(self.fields.0.len());
    self.fields.0.insert(id, field);
    self.fields.1.insert(field, id);
    id
  }

  fn push_var(
    &mut self,
    _global: bool,
    is_type: bool,
    is_foreign: bool,
    is_generic: bool,
    name: &'t str,
    def_at: Span,
  ) -> NameId {
    let id = NameId(self.names.len());
    self.names.push(Name {
      is_type,
      is_foreign,
      is_generic,
      name,
      def_at,
      usages: vec![],
    });
    self.stack.push(id);
    id
  }

  fn push_local_var(&mut self, name: &'t str, def_at: Span) -> NameId {
    self.push_var(false, false, false, false, name, def_at)
  }

  fn push_global_var(&mut self, name: &'t str, def_at: Span) -> NameId {
    self.push_var(true, false, false, false, name, def_at)
  }

  fn push_local_type(&mut self, name: &'t str, def_at: Span) -> NameId {
    self.push_var(false, true, false, false, name, def_at)
  }

  fn push_global_type(&mut self, name: &'t str, def_at: Span) -> NameId {
    self.push_var(true, true, false, false, name, def_at)
  }

  fn push_global_type_foreign(&mut self, name: &'t str, def_at: Span) -> NameId {
    self.push_var(true, true, true, false, name, def_at)
  }

  fn push_global_var_foreign(&mut self, name: &'t str, def_at: Span) -> NameId {
    self.push_var(true, false, true, false, name, def_at)
  }

  fn push_generic(&mut self, name: &'t str, def_at: Span) -> NameId {
    self.push_var(true, false, true, true, name, def_at)
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

// TODO: Show the best matching enum, to be helpful
fn error_no_enum_const<A>(
  ty_name: &str,
  ty_name_at: Span,
  const_name: &str,
  const_name_at: Span,
) -> RRes<A> {
  Err(Error::ResNoEnumConst {
    ty_name: ty_name.to_string(),
    at: const_name_at.merge(ty_name_at),
    const_name: const_name.to_string(),
  })
}

fn error_no_enum<A>(ty_name: &str, ty_name_at: Span) -> RRes<A> {
  Err(Error::ResNoEnum { ty_name: ty_name.to_string(), at: ty_name_at })
}

fn error_msg<A>(msg: &str, span: Span) -> RRes<A> {
  Err(Error::ResMsg { msg: msg.to_string(), span })
}

fn resolve_ty<'t>(ctx: &mut Ctx<'t>, ty: ast::Type<'t>) -> RRes<Type> {
  Ok(match ty {
    ast::Type::TEmpty(at) => {
      let frame = ctx.push_frame();
      let node = ctx.push_local_type("@", at);
      ctx.pop_frame(frame);
      Type::TNode(node, at)
    }
    ast::Type::TCustom { name: ast::ProperName(name, at), args, span: _ }
      if name == "Int" && args.len() == 0 =>
    {
      Type::TInt(at)
    }
    ast::Type::TCustom { name: ast::ProperName(name, at), args, span: _ }
      if name == "Real" && args.len() == 0 =>
    {
      Type::TReal(at)
    }
    ast::Type::TCustom { name: ast::ProperName(name, at), args, span: _ }
      if name == "Str" && args.len() == 0 =>
    {
      Type::TStr(at)
    }
    ast::Type::TCustom { name: ast::ProperName(name, at), args, span: _ }
      if name == "Bool" && args.len() == 0 =>
    {
      Type::TBool(at)
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
    ast::Type::TFunction(a, b, span) => {
      let a = Box::new(resolve_ty(ctx, *a)?);
      let b = Box::new(resolve_ty(ctx, *b)?);
      Type::TFunction(a, b, span)
    }
    ast::Type::TRecord { fields, span } => {
      let fields = fields
        .into_iter()
        .map(|(span, field, ty)| {
          let field = ctx.find_field(field);
          let ty = resolve_ty(ctx, ty)?;
          Ok((span, field, ty))
        })
        .collect::<RRes<Vec<(Span, FieldId, Type)>>>()?;
      Type::TRecord { fields, span }
    }
    ast::Type::TForall(ast::Name(name, at), inner, _span) => {
      let frame = ctx.push_frame();
      ctx.push_generic(name, at);
      let inner = resolve_ty(ctx, *inner)?;
      ctx.pop_frame(frame);
      inner
    }
  })
}

fn resolve_expr<'t>(ctx: &mut Ctx<'t>, def: ast::Expr<'t>) -> RRes<Expr> {
  Ok(match def {
    ast::Expr::Let { bind_value, binding, next_value } => {
      let bind_value = Box::new(resolve_expr(ctx, *bind_value)?);

      let frame = ctx.push_frame();
      let binding = resolve_pattern(ctx, binding)?;
      let next_value = Box::new(resolve_expr(ctx, *next_value)?);
      ctx.pop_frame(frame);

      Expr::Let { bind_value, binding, next_value }
    }

    ast::Expr::EBool(value, span) => Expr::EBool(value, span),
    ast::Expr::EInt(value, span) => Expr::EInt(value, span),
    ast::Expr::EReal(value, span) => Expr::EReal(value, span),
    ast::Expr::EStr(value, span) => Expr::EStr(value.to_string(), span),
    ast::Expr::Var(ast::Name(name, at), span) => Expr::Var(
      match ctx.read_name(name, at) {
        Some(var) => var,
        None => return error_no_var(name, at),
      },
      span,
    ),
    ast::Expr::Record { to_extend, fields, span } => {
      let to_extend = match to_extend {
        Some(to_extend) => Some(Box::new(resolve_expr(ctx, *to_extend)?)),
        None => None,
      };

      let fields = fields
        .into_iter()
        .map(|((at, field), value)| {
          let field = ctx.find_field(field);
          match resolve_expr(ctx, value) {
            Ok(value) => Ok(((at, field), value)),
            Err(err) => Err(err),
          }
        })
        .collect::<RRes<Vec<_>>>()?;

      Expr::Record { span, to_extend, fields }
    }
    ast::Expr::EnumConst {
      ty_name: ty_name @ ast::ProperName(_, ty_name_at),
      const_name: const_name @ ast::ProperName(_, const_name_at),
      value,
    } => {
      let (ty_name, const_name, value_ty) = resolve_enum_const(ctx, ty_name, const_name)?;

      let span = ty_name_at.merge(const_name_at).merge(
        value
          .as_ref()
          .map(|e| e.span().clone())
          .unwrap_or(const_name_at),
      );

      let value = value
        .map(|a| resolve_expr(ctx, *a))
        .transpose()?
        .map(Box::new);

      let value = match (value, value_ty) {
        (Some(v), Some(t)) => Some((v, t)),
        (None, None) => None,
        (Some(_), None) => {
          return error_msg("The type claims no value but a type was given here", span)
        }
        (None, Some(_)) => {
          return error_msg(
            "The type requires a value but no value was given here",
            span,
          )
        }
      };

      Expr::EnumConst { ty_name, const_name, value, span }
    }
    ast::Expr::Un(op, expr) => {
      let at = op.span().merge(expr.span());
      Expr::Un(op, Box::new(resolve_expr(ctx, *expr)?), at)
    }
    ast::Expr::Bin(ast::BinOp::RevCall(op_at), a, b) => {
      let at = a.span().merge(b.span());
      Expr::Bin(
        ast::BinOp::Call(op_at),
        // Note the swapped order
        Box::new(resolve_expr(ctx, *b)?),
        Box::new(resolve_expr(ctx, *a)?),
        at,
      )
    }
    ast::Expr::Bin(op, a, b) => {
      let at = a.span().merge(b.span());
      Expr::Bin(
        op,
        Box::new(resolve_expr(ctx, *a)?),
        Box::new(resolve_expr(ctx, *b)?),
        at,
      )
    }
    ast::Expr::Match { value, branches, span } => {
      let value = Box::new(resolve_expr(ctx, *value)?);

      let branches = branches
        .into_iter()
        .map(|ast::WithBranch { pattern, condition, value, span }| {
          let frame = ctx.push_frame();
          let pattern = resolve_pattern(ctx, pattern)?;
          let condition = condition.map(|c| resolve_expr(ctx, c)).transpose()?;
          let value = resolve_expr(ctx, value)?;
          ctx.pop_frame(frame);

          Ok(WithBranch { pattern, condition, value, span })
        })
        .collect::<RRes<Vec<WithBranch>>>()?;

      Expr::Match { value, branches, span }
    }
    ast::Expr::Lambda { args, body, span } => {
      let frame = ctx.push_frame();
      let args = args
        .into_iter()
        .map(|binding| resolve_pattern(ctx, binding))
        .collect::<RRes<Vec<_>>>()?;
      let body = Box::new(resolve_expr(ctx, *body)?);
      ctx.pop_frame(frame);

      Expr::Lambda { args, body, span }
    }
  })
}

fn resolve_pattern<'t>(ctx: &mut Ctx<'t>, pat: ast::Pattern<'t>) -> RRes<Pattern> {
  Ok(match pat {
    ast::Pattern::Empty(span) => Pattern::Empty(span),
    ast::Pattern::Var(ast::Name(var, at), inner, span) => {
      let var = ctx.push_local_var(var, at);
      let inner = match inner {
        Some(inner) => Some(Box::new(resolve_pattern(ctx, *inner)?)),
        None => None,
      };
      Pattern::Var(var, inner, span)
    }
    ast::Pattern::EnumConst { ty_name, const_name, inner, span } => {
      let (ty_name, const_name, value_ty) = resolve_enum_const(ctx, ty_name, const_name)?;

      let inner = match (inner, value_ty) {
        (Some(v), Some(t)) => Some((Box::new(resolve_pattern(ctx, *v)?), t)),
        (None, None) => None,
        (Some(_), None) => {
          return error_msg("The type claims no value but a type was given here", span)
        }
        (None, Some(_)) => {
          return error_msg(
            "The type requires a value but no value was given here",
            span,
          )
        }
      };

      Pattern::EnumConst { ty_name, const_name, inner, span }
    }
    ast::Pattern::Record(fields, span) => {
      let fields = fields
        .into_iter()
        .map(|((span, field), pat)| {
          let pat = match pat {
            Some(pat) => resolve_pattern(ctx, pat)?,
            None => Pattern::Var(ctx.push_local_var(field, span), None, span),
          };
          Ok((ctx.find_field(field), span, pat))
        })
        .collect::<RRes<Vec<_>>>()?;
      Pattern::Record(fields, span)
    }
    ast::Pattern::PBool(b, span) => Pattern::PBool(b, span),
    ast::Pattern::PInt(i, span) => Pattern::PInt(i, span),
    ast::Pattern::PReal(r, span) => Pattern::PReal(r, span),
    ast::Pattern::PStr(s, span) => Pattern::PStr(s.to_owned(), span),
  })
}

fn resolve_enum_const<'t>(
  ctx: &mut Ctx<'t>,
  ast::ProperName(ty_name_, ty_name_at): ast::ProperName<'t>,
  ast::ProperName(const_name_, const_name_at): ast::ProperName<'t>,
) -> RRes<(NameId, NameId, Option<Type>)> {
  let ty_name = match ctx.read_name(ty_name_, ty_name_at) {
    Some(t) => t,
    None => return error_no_var(ty_name_, ty_name_at),
  };
  let const_name = match ctx.read_name(const_name_, const_name_at) {
    Some(t) => t,
    None => return error_no_var(const_name_, const_name_at),
  };
  let cons = match ctx.enum_constructors.get(&ty_name) {
    Some(t) => t,
    None => return error_no_enum(ty_name_, ty_name_at),
  };
  let value_ty = match cons.get(&const_name) {
    Some(t) => t.clone(),
    None => return error_no_enum_const(ty_name_, ty_name_at, const_name_, const_name_at),
  };
  Ok((ty_name, const_name, value_ty))
}

fn resolve_def<'t>(ctx: &mut Ctx<'t>, def: ast::Def<'t>) -> RRes<Def> {
  Ok(match def {
    ast::Def::Def { ty, name: ast::Name(name, _), args, body, span } => {
      let ty = resolve_ty(ctx, ty)?;
      let name = ctx.find_name(name).unwrap();
      let frame = ctx.push_frame();
      let args = args
        .into_iter()
        .map(|binding| resolve_pattern(ctx, binding))
        .collect::<RRes<Vec<_>>>()?;
      let body = resolve_expr(ctx, body)?;
      ctx.pop_frame(frame);
      Def::Def { ty, name, args, body, span }
    }
    ast::Def::ForiegnDef { ty, name: ast::Name(name, _), span, foreign_block } => {
      let ty = resolve_ty(ctx, ty)?;
      let name = ctx.find_name(name).unwrap();
      let foreign_block = foreign_block.map(|(source, _)| source.to_owned());
      Def::ForiegnDef { ty, name, span, foreign_block }
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

    ast::Def::ForiegnType { name: ast::ProperName(name, _), span, args } => {
      let name = ctx.find_name(name).unwrap();

      let frame = ctx.push_frame();
      let args = args
        .into_iter()
        .map(|ast::Name(name, at)| ctx.push_local_type(name, at))
        .collect();
      ctx.pop_frame(frame);

      Def::ForeignType { name, args, span }
    }

    ast::Def::Enum {
      name: ast::ProperName(name, _),
      args,
      constructors,
      span,
    } => {
      let name = ctx.find_name(name).unwrap();

      let frame = ctx.push_frame();
      let args = args
        .into_iter()
        .map(|ast::Name(name, at)| ctx.push_local_type(name, at))
        .collect();
      let constructors = constructors
        .iter()
        .map(
          |ast::EnumConst { tag: ast::ProperName(tag, _), ty, span }| {
            let tag = ctx.find_name(tag).unwrap();
            let ty = ty
              .as_ref()
              .map(|t| resolve_ty(ctx, t.clone()))
              .transpose()?;
            Ok(EnumConst { tag, ty, span: *span })
          },
        )
        .collect::<RRes<Vec<_>>>()?;
      ctx.pop_frame(frame);

      Def::Enum { name, args, constructors, span }
    }
  })
}

pub fn resolve<'t>(
  defs: Vec<ast::Def<'t>>,
) -> Result<(Vec<Name<'t>>, BTreeMap<FieldId, &'t str>, Vec<Def>), Vec<Error>> {
  let mut ctx = Ctx::new();
  let mut out = vec![];
  let mut errs = vec![];

  // Top-pass
  for d in defs.iter() {
    let (name, at) = match d.name() {
      None => continue,
      Some(x) => x,
    };
    // TODO, handle type definitions here
    match (ctx.find_name(name), d) {
      (Some(NameId(old)), _) => {
        errs.push(error_multiple_def(name, ctx.names[old].def_at, at));
      }
      (None, ast::Def::ForiegnDef { .. }) => {
        ctx.push_global_var_foreign(name, at);
      }
      (None, ast::Def::Def { .. }) => {
        ctx.push_global_var(name, at);
      }
      (None, ast::Def::ForiegnType { .. }) => {
        ctx.push_global_type_foreign(name, at);
      }
      (None, ast::Def::Type { .. }) => {
        ctx.push_global_type(name, at);
      }
      (None, ast::Def::Enum { .. }) => {
        ctx.push_global_type(name, at);
      }
    }
  }

  for d in defs.iter() {
    let (name, _) = match d.name() {
      None => continue,
      Some(x) => x,
    };
    // TODO, handle type definitions here
    match (ctx.find_name(name), d) {
      (None, _) => unreachable!(),

      (_, ast::Def::ForiegnDef { .. })
      | (_, ast::Def::Def { .. })
      | (_, ast::Def::ForiegnType { .. })
      | (_, ast::Def::Type { .. }) => {}

      (Some(ty), ast::Def::Enum { constructors, .. }) => {
        let mut cons = BTreeMap::new();
        for ast::EnumConst { tag: ast::ProperName(tag, at), ty, span: _ } in constructors.iter() {
          if let Some(NameId(old)) = ctx.find_name(tag) {
            errs.push(error_multiple_def(name, ctx.names[old].def_at, *at));
            continue;
          }
          let con = ctx.push_global_type(tag, *at);
          let ty = match ty
            .as_ref()
            .map(|t| resolve_ty(&mut ctx, t.clone()))
            .transpose()
          {
            Ok(ty) => ty,
            Err(err) => {
              errs.push(err);
              continue;
            }
          };
          cons.insert(con, ty);
        }
        ctx.enum_constructors.insert(ty, cons);
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
    Ok((ctx.names, ctx.fields.0, out))
  } else {
    Err(errs)
  }
}
