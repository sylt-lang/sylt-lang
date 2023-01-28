use crate::error::*;

#[derive(Debug, Clone)]
pub struct Name<'t>(pub &'t str, pub Span);

#[derive(Debug, Clone)]
pub struct ProperName<'t>(pub &'t str, pub Span);

#[derive(Debug, Clone)]
pub enum Def<'t> {
  Def {
    ty: Type<'t>,
    name: Name<'t>,
    args: Vec<Name<'t>>,
    body: Expr<'t>,
    span: Span,
  },
  ForiegnDef {
    ty: Type<'t>,
    name: Name<'t>,
    span: Span,
  },
  Type {
    name: ProperName<'t>,
    args: Vec<Name<'t>>,
    body: Type<'t>,
    span: Span,
  },
  Enum {
    name: ProperName<'t>,
    args: Vec<Name<'t>>,
    constructors: Vec<EnumConst<'t>>,
    span: Span,
  },
  ForiegnType {
    name: ProperName<'t>,
    span: Span,
  },

  ForeignBlock {
    source: &'t str,
    span: Span,
  },
}

impl<'t> Def<'t> {
  pub fn name(&self) -> Option<(&'t str, Span)> {
    match self {
      Def::Def { name: Name(str, span), .. }
      | Def::ForiegnDef { name: Name(str, span), .. }
      | Def::Type { name: ProperName(str, span), .. }
      | Def::Enum { name: ProperName(str, span), .. }
      | Def::ForiegnType { name: ProperName(str, span), .. } => Some((str, *span)),

      Def::ForeignBlock { .. } => None,
    }
  }
}

#[derive(Debug, Clone)]
pub enum Pattern<'t> {
  Empty(Span),
  Var(Name<'t>, Option<Box<Pattern<'t>>>, Span),
  EnumConst {
    ty_name: ProperName<'t>,
    const_name: ProperName<'t>,
    inner: Option<Box<Pattern<'t>>>,
    span: Span,
  },
  // Value(Expr<'t>),
}

impl<'t> Pattern<'t> {
  pub fn span(&self) -> Span {
    match self {
      Pattern::Empty(span) | Pattern::Var(_, _, span) | Pattern::EnumConst { span, .. } => *span,
    }
  }
}

#[derive(Debug, Clone)]
pub struct EnumConst<'t> {
  pub tag: ProperName<'t>,
  pub ty: Option<Type<'t>>,
  pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Expr<'t> {
  EBool(bool, Span),
  EInt(i64, Span),
  EReal(f64, Span),
  EStr(&'t str, Span),

  EnumConst {
    ty_name: ProperName<'t>,
    const_name: ProperName<'t>,
    value: Option<Box<Expr<'t>>>,
  },

  Record {
    to_extend: Option<Box<Expr<'t>>>,
    fields: Vec<((Span, &'t str), Expr<'t>)>,
    span: Span,
  },

  Var(Name<'t>, Span),
  Let {
    binding: Pattern<'t>,
    bind_value: Box<Expr<'t>>,

    next_value: Box<Expr<'t>>,
  },
  // Match {
  //   value: Box<Expr<'t>>,
  //
  //   // Non-empty
  //   branches: Vec<(Pattern<'t>, Option<Expr<'t>>, Expr<'t>)>,
  // },
  Un(UnOp, Box<Expr<'t>>),
  Bin(BinOp, Box<Expr<'t>>, Box<Expr<'t>>),
}

impl<'t> Expr<'t> {
  pub fn span(&self) -> Span {
    match self {
      Expr::EInt(_, span)
      | Expr::EReal(_, span)
      | Expr::EStr(_, span)
      | Expr::EBool(_, span)
      | Expr::Var(_, span)
      | Expr::Record { span, .. } => *span,

      Expr::Let { binding, bind_value: _, next_value } => next_value.span().merge(binding.span()),

      Expr::EnumConst {
        ty_name: ProperName(_, ty_span),
        const_name: ProperName(_, const_span),
        value,
      } => {
        let pre_span = ty_span.merge(*const_span);
        match value {
          Some(expr) => pre_span.merge(expr.span()),
          None => pre_span,
        }
      }
      Expr::Un(op, a) => op.span().merge(a.span()),
      Expr::Bin(op, a, b) => op.span().merge(a.span()).merge(b.span()),
    }
  }
}

#[derive(Debug, Clone, Copy)]
pub enum UnOp {
  Neg(Span),
}

impl UnOp {
  pub fn span(&self) -> Span {
    match self {
      UnOp::Neg(span) => *span,
    }
  }
}

#[derive(Debug, Clone, Copy)]
pub enum BinOp {
  Add(Span),
  Sub(Span),
  Div(Span),
  Mul(Span),
  Call(Span),
}

impl BinOp {
  pub fn span(&self) -> Span {
    match self {
      BinOp::Add(span)
      | BinOp::Sub(span)
      | BinOp::Div(span)
      | BinOp::Mul(span)
      | BinOp::Call(span) => *span,
    }
  }
}

#[derive(Debug, Clone)]
pub enum Type<'t> {
  TEmpty(Span),
  TCustom {
    name: ProperName<'t>,
    args: Vec<Type<'t>>,
    span: Span,
  },
  TVar(Name<'t>, Span),
  TFunction(Box<Type<'t>>, Box<Type<'t>>, Span),
}

impl<'t> Type<'t> {
  pub fn span(&self) -> Span {
    match self {
      Type::TEmpty(span)
      | Type::TCustom { span, .. }
      | Type::TVar(_, span)
      | Type::TFunction(_, _, span) => *span,
    }
  }
}
