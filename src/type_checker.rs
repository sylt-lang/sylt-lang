#![allow(dead_code)]

use std::collections::BTreeSet;

use crate::ast;
use crate::error::*;
use crate::name_resolution::*;

#[derive(Clone, Debug)]
pub enum CType<'t> {
  NodeType(NameId),
  // Type,
  Unknown,
  Foreign(&'t Name<'t>),
  // Is this a good idea to code here?
  Int,
  Real,
  Str,
  //
  Req(BTreeSet<Requirement>, Box<CType<'t>>),
  // Alias(Box<CType<'t>>),
  // Custom(Box<CType<'t>>),
  Apply(Box<CType<'t>>, Box<CType<'t>>),
  Function(Box<CType<'t>>, Box<CType<'t>>),
}

impl<'t> CType<'t> {
  fn render(&self, checker: &mut Checker<'t>) -> String {
    self.render_inner(checker)
  }

  fn render_inner(&self, checker: &mut Checker<'t>) -> String {
    match self {
      CType::NodeType(name) => {
        let ty = resolve_ty(checker, *name);
        ty.render(checker)
      }
      CType::Unknown => "_".to_string(),
      CType::Foreign(name) => name.name.to_string(),
      CType::Int => "Int".to_string(),
      CType::Real => "Real".to_string(),
      CType::Str => "Str".to_string(),
      CType::Apply(a, b) => {
        let a = a.render(checker);
        let b = b.render(checker);
        format!("{} {}", a, b)
      }
      CType::Function(a, b) => {
        let a = a.render(checker);
        let b = b.render(checker);
        format!("{} -> {}", a, b)
      }

      CType::Req(r, t) => {
        let t = t.render(checker);
        format!("({:?} => {})", r, t)
      }
    }
  }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Requirement {
  Num,
}

impl Requirement {
  fn to_name(&self) -> &'static str {
    match self {
      Requirement::Num => "Num",
    }
  }

  fn to_ctype<'t>(self) -> CType<'t> {
    let mut reqs = BTreeSet::new();
    reqs.insert(self);
    CType::Req(reqs, Box::new(CType::Unknown))
  }
}

#[derive(Clone, Debug)]
pub enum Node<'t> {
  Child(NameId),
  Ty(Box<CType<'t>>),
}

struct Checker<'t> {
  types: Vec<Node<'t>>,
  names: &'t [Name<'t>],
}

type TRes<A> = Result<A, Error>;

pub fn check<'t>(names: &'t Vec<Name<'t>>, defs: &Vec<Def>) -> TRes<Vec<Node<'t>>> {
  // These are the only nodes which should ever be created. Otherwise memory usage will explode.
  let mut checker = Checker {
    types: names
      .iter()
      .map(|_| Node::Ty(Box::new(CType::Unknown)))
      .collect(),
    names,
  };

  for def in defs {
    match def {
      Def::ForiegnDef { name, span, ty, .. } | Def::Def { name, span, ty, .. } => {
        let ty = check_type(&mut checker, ty)?;
        let x = CType::NodeType(*name);
        unify(&mut checker, x, ty, *span)?;
      }

      Def::ForeignType { name, span } => {
        let NameId(slot) = name;
        let x = CType::NodeType(*name);
        unify(&mut checker, x, CType::Foreign(&names[*slot]), *span)?;
      }

      Def::Type { .. } => {}

      Def::Enum { .. } => {}
    }
  }

  for def in defs {
    check_def(&mut checker, def)?;
  }

  // for def in defs}
  //   match def {
  //     Def::Def { name, .. }
  //     | Def::ForiegnDef { name, .. }
  //     | Def::Type { name, .. }
  //     | Def::ForeignType { name, .. } => {
  //       let NameId(slot) = *name;
  //       let x = resolve_ty(&mut checker, *name);
  //       let ty = x.render(&mut checker);
  //       let name = names[slot].name;
  //       println!("{:?} - {:#?}", name, ty);
  //     }
  //   }
  // }

  Ok(checker.types)
}

fn check_def(checker: &mut Checker, def: &Def) -> TRes<()> {
  Ok(match def {
    Def::Def { ty, name, args, body, span } => {
      let (def_ty, ret) = unify_params(checker, ty, args.as_slice())?;
      unify(checker, CType::NodeType(*name), def_ty, *span)?;
      let body = check_expr(checker, body)?;
      unify(checker, body, ret, *span)?;
    }
    Def::ForiegnDef { ty, name, span } => {
      let def_ty = check_type(checker, ty)?;
      unify(checker, CType::NodeType(*name), def_ty, *span)?;
    }
    Def::Type { .. } => {
      // TODO! More needs to be done here, mainly with higher order types and stuff
    }
    Def::Enum { .. } => {
      // TODO! More needs to be done here, mainly with higher order types and stuff
    }
    Def::ForeignType { .. } => { /* Do nothing */ }
  })
}

fn unify<'t>(checker: &mut Checker<'t>, a: CType<'t>, b: CType<'t>, span: Span) -> TRes<CType<'t>> {
  Ok(match (a, b) {
    (CType::Unknown, b) => b,
    (a, CType::Unknown) => a,
    (CType::Req(ar, inner_a), CType::Req(br, inner_b)) => {
      let c = unify(checker, *inner_a, *inner_b, span)?;
      let cr = ar.union(&br).cloned().collect();
      check_requirements(checker, span, cr, c)?
    }
    (CType::Req(req, inner_a), inner_b) => {
      let c = unify(checker, *inner_a, inner_b, span)?;
      check_requirements(checker, span, req, c)?
    }
    (inner_a, CType::Req(req, inner_b)) => {
      let c = unify(checker, inner_a, *inner_b, span)?;
      check_requirements(checker, span, req, c)?
    }
    (CType::NodeType(a_id), b) => {
      let inner_a = resolve_ty(checker, a_id);
      let c = unify(checker, inner_a, b, span)?;
      inject(checker, a_id, c)
    }
    (a, CType::NodeType(b_id)) => {
      let inner_b = resolve_ty(checker, b_id);
      let c = unify(checker, a, inner_b, span)?;
      inject(checker, b_id, c)
    }
    (CType::Foreign(a), CType::Foreign(b)) if a.def_at == b.def_at => CType::Foreign(a),
    (CType::Foreign(a), CType::Foreign(b)) if a.def_at != b.def_at => {
      return error_unify(
        checker,
        "Failed to merge these two foriegn types types",
        CType::Foreign(a),
        CType::Foreign(b),
        span,
      )
    }
    (CType::Int, CType::Int) => CType::Int,
    (CType::Real, CType::Real) => CType::Real,
    (CType::Str, CType::Str) => CType::Str,
    (CType::Apply(a0, a1), CType::Apply(b0, b1)) => {
      let c0 = unify(checker, *a0, *b0, span)?;
      let c1 = unify(checker, *a1, *b1, span)?;
      CType::Apply(Box::new(c0), Box::new(c1))
    }
    (CType::Function(a0, a1), CType::Function(b0, b1)) => {
      let c0 = unify(checker, *a0, *b0, span)?;
      let c1 = unify(checker, *a1, *b1, span)?;
      CType::Function(Box::new(c0), Box::new(c1))
    }
    (a, b) => return error_unify(checker, "Failed to merge types", a, b, span),
  })
}

fn check_requirements<'t>(
  checker: &mut Checker<'t>,
  span: Span,
  req: BTreeSet<Requirement>,
  c: CType<'t>,
) -> TRes<CType<'t>> {
  match c {
    CType::NodeType(name) => {
      let c = resolve_ty(checker, name);
      return check_requirements(checker, span, req, c);
    }
    CType::Req(other, inner) => {
      let req = req.union(&other).cloned().collect();
      return check_requirements(checker, span, req, *inner);
    }
    //
    CType::Foreign(_) => {
      return error_req(
        checker,
        "A Foreign type cannot have requirements",
        c,
        &req,
        span,
      );
    }
    //
    CType::Unknown => {}
    CType::Int
      if req.iter().all(|r| match r {
        Requirement::Num => true,
      }) => {}
    CType::Real
      if req.iter().all(|r| match r {
        Requirement::Num => true,
      }) => {}
    CType::Str
      if req.iter().all(|r| match r {
        Requirement::Num => false,
      }) => {}
    //
    CType::Apply(_, _) => todo!(),
    CType::Function(_, _) => todo!(),
    _ => {
      return error_req(
        checker,
        "The requirements are not valid here",
        c,
        &req,
        span,
      );
    }
  }
  Ok(CType::Req(req, Box::new(c)))
}

fn check_expr<'t>(checker: &mut Checker<'t>, body: &Expr) -> TRes<CType<'t>> {
  Ok(match body {
    Expr::EInt(_, _) => CType::Int,
    Expr::EReal(_, _) => CType::Real,
    Expr::EStr(_, _) => CType::Str,
    Expr::Var(name, _) => CType::NodeType(*name),
    Expr::Const { ty_name, value, const_name: _, span } => {
      let ty = resolve_ty(checker, *ty_name);
      match value {
        Some(expr) => {
          let expr_ty = check_expr(checker, expr)?;
          unify(checker, ty, expr_ty, *span)?
        }
        None => ty,
      }
    }
    Expr::Un(ast::UnOp::Neg(at), expr, _) => {
      let expr_ty = check_expr(checker, expr)?;
      unify(checker, expr_ty, CType::Int, *at)?
    }
    Expr::Bin(ast::BinOp::Call(at), f, a, _) => {
      let f_ty = check_expr(checker, f)?;
      let a_ty = check_expr(checker, a)?;
      let f_ty = unify(
        checker,
        f_ty,
        CType::Function(Box::new(a_ty), Box::new(CType::Unknown)),
        *at,
      )?;
      let (_arg_ty, ret_ty) = unpack_function(checker, f_ty, *at)?;
      ret_ty
    }
    Expr::Bin(ast::BinOp::Add(at) | ast::BinOp::Sub(at) | ast::BinOp::Mul(at), a, b, _) => {
      let a_ty = check_expr(checker, a)?;
      let b_ty = check_expr(checker, b)?;
      let c_ty = unify(checker, a_ty, b_ty, *at)?;
      unify(checker, c_ty, Requirement::Num.to_ctype(), *at)?
    }

    Expr::Bin(ast::BinOp::Div(at), a, b, _) => {
      let a_ty = check_expr(checker, a)?;
      let b_ty = check_expr(checker, b)?;
      let c_ty = unify(checker, a_ty, b_ty, *at)?;
      unify(checker, c_ty, CType::Real, *at)?
    }
  })
}

fn unpack_function<'t>(
  checker: &mut Checker<'t>,
  f_ty: CType<'t>,
  at: Span,
) -> TRes<(CType<'t>, CType<'t>)> {
  Ok(match f_ty {
    CType::NodeType(name) => {
      let ty = resolve_ty(checker, name);
      unpack_function(checker, ty, at)?
    }
    CType::Function(a, r) => (*a, *r),
    CType::Unknown
    | CType::Foreign(_)
    | CType::Int
    | CType::Real
    | CType::Str
    | CType::Req(_, _)
    | CType::Apply(_, _) => {
      return error_expected(
        checker,
        "Expected a function, but got something else",
        f_ty,
        at,
      )
    }
  })
}

fn resolve<'t>(checker: &mut Checker<'t>, NameId(slot): &NameId) -> NameId {
  // TODO union find
  match checker.types[*slot] {
    Node::Child(parent) => {
      let at = resolve(checker, &parent);
      checker.types[*slot] = Node::Child(at);
      at
    }
    Node::Ty(_) => NameId(*slot),
  }
}

fn resolve_ty<'t>(checker: &mut Checker<'t>, a: NameId) -> CType<'t> {
  let NameId(slot) = resolve(checker, &a);
  if let Node::Ty(ty) = checker.types[slot].clone() {
    *ty
  } else {
    panic!("Invariant doesn't hold! Not an inner most type!")
  }
}

fn inject<'t>(checker: &mut Checker<'t>, a_id: NameId, c: CType<'t>) -> CType<'t> {
  let NameId(slot) = resolve(checker, &a_id);
  checker.types[slot] = Node::Ty(Box::new(c.clone()));
  c
}

fn unify_params<'t>(
  checker: &mut Checker<'t>,
  ty: &Type,
  args: &[NameId],
) -> TRes<(CType<'t>, CType<'t>)> {
  if args.is_empty() {
    let out = check_type(checker, ty)?;
    Ok((out.clone(), out.clone()))
  } else {
    match ty {
      Type::TFunction(a, rest, at) => {
        let head = args[0];
        let tail = &args[1..];
        let param_node = resolve(checker, &head);
        let a_ty = check_type(checker, a)?;
        let param = unify(checker, a_ty, CType::NodeType(param_node), *at)?;
        let (def_ty, ret) = unify_params(checker, rest, tail)?;
        Ok((CType::Function(Box::new(param), Box::new(def_ty)), ret))
      }
      Type::TInt(_)
      | Type::TReal(_)
      | Type::TStr(_)
      | Type::TApply(_, _, _)
      | Type::TNode(_, _) => {
        let out = check_type(checker, ty)?;
        Ok((out.clone(), out.clone()))
      }
    }
  }
}

fn check_type<'t>(checker: &mut Checker<'t>, ty: &Type) -> TRes<CType<'t>> {
  // TODO
  Ok(match ty {
    Type::TInt(_) => CType::Int,
    Type::TReal(_) => CType::Real,
    Type::TStr(_) => CType::Str,
    Type::TApply(a, b, _) => {
      let a_ty = check_type(checker, a)?;
      let b_ty = check_type(checker, b)?;
      CType::Apply(Box::new(a_ty), Box::new(b_ty))
    }
    Type::TNode(slot, _) => resolve_ty(checker, *slot),
    Type::TFunction(a, b, _) => {
      let a_ty = check_type(checker, a)?;
      let b_ty = check_type(checker, b)?;
      CType::Function(Box::new(a_ty), Box::new(b_ty))
    }
  })
}

fn error_req<'t, A>(
  checker: &mut Checker<'t>,
  msg: &'static str,
  a: CType<'t>,
  req: &BTreeSet<Requirement>,
  span: Span,
) -> Result<A, Error> {
  Err(Error::CheckReq {
    msg,
    span,
    a: a.render(checker),
    req: format!("{:?}", req),
  })
}

fn error_msg<A>(msg: &'static str, a_span: Span, b_span: Span) -> TRes<A> {
  Err(Error::CheckMsg { msg, a_span, b_span })
}

fn error_expected<'t, A>(
  checker: &mut Checker<'t>,
  msg: &'static str,
  a: CType<'t>,
  span: Span,
) -> TRes<A> {
  Err(Error::CheckExpected { msg, span, a: a.render(checker) })
}

fn error_unify<'t, A>(
  checker: &mut Checker<'t>,
  msg: &'static str,
  a: CType<'t>,
  b: CType<'t>,
  span: Span,
) -> Result<A, Error> {
  Err(Error::CheckUnify {
    msg,
    span,
    a: a.render(checker),
    b: b.render(checker),
  })
}
