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
  ForiegnType {
    name: ProperName<'t>,
    args: Vec<Name<'t>>,
    span: Span,
  },

  // Later
  Enum {
    name: ProperName<'t>,
    args: Vec<Name<'t>>,
    constructors: Vec<EnumConst<'t>>,
    span: Span,
  },
}

impl<'t> Def<'t> {
  pub fn name(&self) -> (&'t str, Span) {
    match self {
      Def::Def { name: Name(str, span), .. }
      | Def::ForiegnDef { name: Name(str, span), .. }
      | Def::Type { name: ProperName(str, span), .. }
      | Def::Enum { name: ProperName(str, span), .. }
      | Def::ForiegnType { name: ProperName(str, span), .. } => (str, *span),
    }
  }
}

#[derive(Debug, Clone)]
pub struct EnumConst<'t> {
  pub name: ProperName<'t>,
  pub ty: Option<Type<'t>>,
  pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Expr<'t> {
  EInt(i64, Span),
  Var(Name<'t>, Span),

  Un(UnOp, Box<Expr<'t>>),
  Bin(BinOp, Box<Expr<'t>>, Box<Expr<'t>>),
}

#[derive(Debug, Clone)]
pub enum UnOp {
  Neg(Span),
}

#[derive(Debug, Clone, Copy)]
pub enum BinOp {
  Add(Span),
  Sub(Span),
  Div(Span),
  Mul(Span),
  Call(Span),
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
