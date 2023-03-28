use crate::error::*;

/// A name start with lower case letters (or underscore), `a`, or, `variable_name` for instance.
#[derive(Debug, Clone)]
pub struct Name<'t>(pub &'t str, pub Span);

/// A name starting with an upper case letter, an enum variant for instance.
#[derive(Debug, Clone)]
pub struct ProperName<'t>(pub &'t str, pub Span);

/// An outer definition
#[derive(Debug, Clone)]
pub enum Def<'t> {
  /// Defining a type class
  ///
  /// Example
  /// ```sylt
  /// class Num
  /// ```
  Class { name: ProperName<'t>, span: Span },

  /// Defining an instance of a class
  ///
  /// Example
  /// ```sylt
  /// instance Num Int
  /// ```
  Instance {
    class: ProperName<'t>,
    ty: Type<'t>,
    span: Span,
  },

  /// A definition of a constant or function
  ///
  /// Example
  /// ```sylt
  /// def a : Int := 1
  /// ```
  Def {
    ty: Type<'t>,
    name: Name<'t>,
    args: Vec<Pattern<'t>>,
    body: Expr<'t>,
    span: Span,
  },

  /// A foreign definition
  ///
  /// Example
  /// ```sylt
  /// def a : Int := foreign -[[ 1 ]]-
  /// ```
  ForiegnDef {
    ty: Type<'t>,
    name: Name<'t>,
    span: Span,
    foreign_block: Option<(&'t str, Span)>,
  },

  /// A type alias
  ///
  /// Example
  /// ```sylt
  /// type A x = { variable: x }
  /// ```
  Type {
    name: ProperName<'t>,
    args: Vec<Name<'t>>,
    body: Type<'t>,
    span: Span,
  },

  /// An enum
  ///
  /// Example
  /// ```sylt
  /// enum A = X Int | Y { y: Int }
  /// ```
  Enum {
    name: ProperName<'t>,
    args: Vec<Name<'t>>,
    constructors: Vec<EnumConst<'t>>,
    span: Span,
  },

  /// A foreign type
  ///
  /// Example
  /// ```sylt
  /// type Handle = foreign
  /// ```
  ForiegnType {
    name: ProperName<'t>,
    args: Vec<Name<'t>>,
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
      | Def::ForiegnType { name: ProperName(str, span), .. }
      | Def::Class { name: ProperName(str, span), .. } => Some((str, *span)),

      Def::Instance { .. } => None,
    }
  }
}

#[derive(Debug, Clone)]
pub enum Pattern<'t> {
  /// The empty pattern: `_`
  Empty(Span),

  /// A variable name, matches everything
  Var(Name<'t>, Option<Box<Pattern<'t>>>, Span),

  /// An enum constructor pattern
  ///
  /// Example
  /// ```sylt
  /// Enum:Variant value
  /// ```
  EnumConst {
    ty_name: ProperName<'t>,
    const_name: ProperName<'t>,
    inner: Option<Box<Pattern<'t>>>,
    span: Span,
  },

  /// A record pattern
  ///
  /// Example
  /// ```sylt
  /// { x: 1, y }
  /// ```
  Record(Vec<((Span, &'t str), Option<Pattern<'t>>)>, Span),

  /// A boolean pattern
  PBool(bool, Span),

  /// An integer pattern
  PInt(i64, Span),

  /// A real number pattern
  PReal(f64, Span),

  /// A string pattern
  PStr(&'t str, Span),
}

impl<'t> Pattern<'t> {
  pub fn span(&self) -> Span {
    match self {
      Pattern::Empty(span)
      | Pattern::Var(_, _, span)
      | Pattern::EnumConst { span, .. }
      | Pattern::Record(_, span)
      | Pattern::PBool(_, span)
      | Pattern::PInt(_, span)
      | Pattern::PReal(_, span)
      | Pattern::PStr(_, span) => *span,
    }
  }
}

/// One constructor of an enum
#[derive(Debug, Clone)]
pub struct EnumConst<'t> {
  pub tag: ProperName<'t>,
  pub ty: Option<Type<'t>>,
  pub span: Span,
}

/// A "with" branch in a match expression
///
/// Example
/// ```sylt
/// with 1 -> 2
/// ```
#[derive(Debug, Clone)]
pub struct WithBranch<'t> {
  pub pattern: Pattern<'t>,
  pub condition: Option<Expr<'t>>,
  pub value: Expr<'t>,
  pub span: Span,
}

/// An expression
#[derive(Debug, Clone)]
pub enum Expr<'t> {
  /// A boolean value
  EBool(bool, Span),

  /// An integer value
  EInt(i64, Span),

  /// A real number value
  EReal(f64, Span),

  /// A string value
  EStr(&'t str, Span),

  /// An enum constructor value
  ///
  /// Example
  /// ```sylt
  /// Enum:Variant value
  /// ```
  EnumConst {
    ty_name: ProperName<'t>,
    const_name: ProperName<'t>,
    value: Option<Box<Expr<'t>>>,
  },

  /// A record value
  ///
  /// Example
  /// ```sylt
  /// { x: 1, y: 2 }
  /// ```
  Record {
    to_extend: Option<Box<Expr<'t>>>,
    fields: Vec<((Span, &'t str), Expr<'t>)>,
    span: Span,
  },

  /// A variable
  Var(Name<'t>, Span),

  /// A let binding
  ///
  /// Example
  /// ```sylt
  /// let a = 1 in "another expression"
  /// ```
  Let {
    binding: Pattern<'t>,
    bind_value: Box<Expr<'t>>,

    next_value: Box<Expr<'t>>,
  },

  /// A match expression
  ///
  /// Example
  /// ```sylt
  /// match "expression"
  ///   with "pattern1" -> 0
  ///   with _ -> 1
  /// end
  /// ```
  Match {
    value: Box<Expr<'t>>,

    // Non-empty
    branches: Vec<WithBranch<'t>>,
    span: Span,
  },

  /// A lambda function
  ///
  /// Example
  /// ```sylt
  /// \x -> x
  /// ```
  Lambda {
    args: Vec<Pattern<'t>>,
    body: Box<Expr<'t>>,
    span: Span,
  },

  /// A unary operator expression
  Un(UnOp, Box<Expr<'t>>),

  /// A binary operator expression
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
      | Expr::Match { span, .. }
      | Expr::Lambda { span, .. }
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

/// Unary operators
#[derive(Debug, Clone, Copy)]
pub enum UnOp {
  Neg(Span),
  Not(Span),
}

impl UnOp {
  pub fn span(&self) -> Span {
    match self {
      UnOp::Not(span) | UnOp::Neg(span) => *span,
    }
  }
}

/// Binary operators
#[derive(Debug, Clone, Copy)]
pub enum BinOp {
  /// Addition operator `+`
  Add(Span),
  /// Subtraction operator `-`
  Sub(Span),
  /// Division operator `/`
  Div(Span),
  /// Multiplication operator `*`
  Mul(Span),
  /// Call operator `'`
  Call(Span),
  /// Pipe operator `#`
  RevCall(Span),
  /// And operator `and`
  And(Span),
  /// Or operator `or`
  Or(Span),
  /// Less than operator `<`
  Lt(Span),
  /// Less than or equal operator `<=`
  LtEq(Span),
  /// Equality operator `==`
  Eq(Span),
  /// Inequality operator `!=`
  Neq(Span),
}

impl BinOp {
  pub fn span(&self) -> Span {
    match self {
      BinOp::Add(span)
      | BinOp::Sub(span)
      | BinOp::Div(span)
      | BinOp::Mul(span)
      | BinOp::And(span)
      | BinOp::Or(span)
      | BinOp::Lt(span)
      | BinOp::LtEq(span)
      | BinOp::Eq(span)
      | BinOp::Neq(span)
      | BinOp::Call(span)
      | BinOp::RevCall(span) => *span,
    }
  }
}

/// Types
#[derive(Debug, Clone)]
pub enum Type<'t> {
  /// The empty (unknown) type, matches all types
  TEmpty(Span),

  /// A type alias
  TCustom {
    name: ProperName<'t>,
    args: Vec<Type<'t>>,
    span: Span,
  },

  /// A type variable
  TVar(Name<'t>, Span),

  /// A forall type
  TForall(Name<'t>, Box<Type<'t>>, Span),

  /// A function type
  TFunction(Box<Type<'t>>, Box<Type<'t>>, Span),

  /// A record type
  TRecord {
    fields: Vec<(Span, &'t str, Type<'t>)>,
    span: Span,
  },

  /// A type constraint in the form of a tag
  TLet {
    class: ProperName<'t>,
    var: Name<'t>,
    span: Span,
    inner: Box<Type<'t>>,
  },
}

impl<'t> Type<'t> {
  pub fn span(&self) -> Span {
    match self {
      Type::TEmpty(span)
      | Type::TCustom { span, .. }
      | Type::TVar(_, span)
      | Type::TForall(_, _, span)
      | Type::TFunction(_, _, span)
      | Type::TLet { span, .. }
      | Type::TRecord { span, .. } => *span,
    }
  }
}
