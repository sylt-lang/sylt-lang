#![allow(dead_code)]

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::ast;
use crate::error::*;
use crate::name_resolution::*;

#[derive(Clone, Debug)]
pub enum CType<'t> {
  NodeType(NameId),
  // TODO - add Error type so we can report multiple errors and stuff
  Unknown,
  Foreign(&'t Name<'t>),
  // Is this a good idea to code here?
  Bool,
  Int,
  Real,
  Str,
  Record,
  //
  Req(BTreeSet<Requirement>, Box<CType<'t>>),
  Apply(Box<CType<'t>>, Box<CType<'t>>),
  Function(Box<CType<'t>>, Box<CType<'t>>),
}

impl<'t> CType<'t> {
  fn is_same(&self, other: &Self) -> bool {
    match (self, other) {
      (CType::Bool, CType::Bool)
      | (CType::Int, CType::Int)
      | (CType::Real, CType::Real)
      | (CType::Str, CType::Str)
      | (CType::Record, CType::Record)
      | (CType::Unknown, CType::Unknown) => true,
      (CType::NodeType(a), CType::NodeType(b)) => a == b,
      _ => false,
    }
  }
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
      CType::Bool => "Bool".to_string(),
      CType::Int => "Int".to_string(),
      CType::Real => "Real".to_string(),
      CType::Str => "Str".to_string(),
      // This isn't good enough
      CType::Record => "Record".to_string(),
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

      CType::Req(rs, t) => {
        let t = t.render(checker);
        let rs = rs.iter().map(|r| r.to_name(checker)).collect::<Vec<String>>().join(", ");
        format!("([{:?}] => {})", rs, t)
      }
    }
  }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord)]
pub enum Requirement {
  Num,
  Field(FieldId, NameId),
}

impl PartialOrd for Requirement {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    fn to_tuple(s: &Requirement) -> (usize, usize) {
      match s {
        Requirement::Num => (0, 0),
        Requirement::Field(FieldId(n), _) => (1, *n),
      }
    }

    Some(to_tuple(self).cmp(&to_tuple(other)))
  }
}

impl Requirement {
  fn to_name<'t>(&self, checker: &mut Checker<'t>) -> String {
    match self {
      Requirement::Num => "Num".to_owned(),
      Requirement::Field(field, ty) => {
        format!(
          "({}: {})",
          checker.field(*field),
          CType::NodeType(*ty).render(checker)
        )
      }
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
  fields: &'t BTreeMap<FieldId, &'t str>,
}

impl<'t> Checker<'t> {
  fn field(&self, field: FieldId) -> &'t str {
    &self.fields[&field]
  }

  fn raise_to_node(&mut self, ty: CType<'t>) -> NameId {
    let name = NameId(self.types.len());
    self.types.push(Node::Ty(Box::new(ty)));
    name
  }
}

type TRes<A> = Result<A, Error>;

pub fn check<'t>(
  names: &'t Vec<Name<'t>>,
  defs: &Vec<Def>,
  fields: &'t BTreeMap<FieldId, &'t str>,
) -> TRes<Vec<Node<'t>>> {
  // These are the only nodes which should ever be created. Otherwise memory usage will explode.
  let mut checker = Checker {
    types: names
      .iter()
      .map(|_| Node::Ty(Box::new(CType::Unknown)))
      .collect(),
    names,
    fields,
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

      Def::Enum { name, span, args: _, constructors: _ } => {
        let NameId(slot) = name;
        let x = CType::NodeType(*name);
        unify(&mut checker, x, CType::Foreign(&names[*slot]), *span)?;
      }

      Def::ForeignBlock { .. } => { /* Do nothing */ }
    }
  }

  for def in defs {
    check_def(&mut checker, def)?;
  }

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

    Def::ForeignType { .. } | Def::ForeignBlock { .. } => { /* Do nothing */ }
  })
}

fn record_merge<'t>(
  checker: &mut Checker<'t>,
  reqs: BTreeSet<Requirement>,
  extend_ty: CType<'t>,
  span: Span,
) -> TRes<CType<'t>> {
  Ok(match extend_ty {
    t @ CType::Unknown | t @ CType::Record | t @ CType::NodeType(_) => {
      CType::Req(reqs, Box::new(t))
    }
    CType::Req(inner_reqs, inner) => {
      let mut new_inner_reqs = inner_reqs.clone();
      for req in reqs.iter() {
        // Overwrite all collisions
        new_inner_reqs.insert(*req);
      }
      CType::Req(new_inner_reqs, inner)
    }
    _ => {
      return error_expected(
        checker,
        "Expected a record, but this isn't a record",
        extend_ty,
        span,
      );
    }
  })
}

fn unify<'t>(checker: &mut Checker<'t>, a: CType<'t>, b: CType<'t>, span: Span) -> TRes<CType<'t>> {
  Ok(match (a, b) {
    (CType::Unknown, b) => b,
    (a, CType::Unknown) => a,
    (CType::Req(ar, inner_a), CType::Req(br, inner_b)) => {
      let c = unify(checker, *inner_a, *inner_b, span)?;
      let mut cr = ar.clone();
      for bb in br.iter() {
        match (cr.get(bb), bb) {
          (Some(Requirement::Field(_, a_id)), Requirement::Field(_, b_id)) => {
            // TODO: Annotate error with field name
            unify(
              checker,
              CType::NodeType(*a_id),
              CType::NodeType(*b_id),
              span,
            )?;
            cr.insert(*bb);
          }
          (None | Some(Requirement::Num | Requirement::Field(_, _)), _) => {
            cr.insert(*bb);
          }
        }
      }
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
    // (CType::Record(ax), CType::Record(bx)) => {
    //   let mut out = vec![];
    //   for (aa, bb) in ax.iter().zip(bx.iter()) {
    //     if aa.0 != bb.0 {
    //       return error_label(
    //         checker,
    //         aa.0.max(bb.0),
    //         &CType::Record(ax),
    //         &CType::Record(bx),
    //         span,
    //       );
    //     }
    //     out.push((aa.0, unify(checker, aa.1.clone(), bb.1.clone(), span)?));
    //   }
    //   CType::Record(out)
    // }
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
    c @ CType::Req(_, _) => {
      return unify(checker, c, CType::Req(req, Box::new(CType::Unknown)), span);
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
        Requirement::Field(_, _) => false,
      }) => {}
    CType::Real
      if req.iter().all(|r| match r {
        Requirement::Num => true,
        Requirement::Field(_, _) => false,
      }) => {}
    CType::Str
      if req.iter().all(|r| match r {
        Requirement::Num => false,
        Requirement::Field(_, _) => false,
      }) => {}
    CType::Record
      if req.iter().all(|r| match r {
        Requirement::Num => false,
        Requirement::Field(_, _) => true,
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
    Expr::EBool(_, _) => CType::Bool,
    Expr::EInt(_, _) => CType::Int,
    Expr::EReal(_, _) => CType::Real,
    Expr::EStr(_, _) => CType::Str,
    Expr::Var(name, _) => CType::NodeType(*name),
    Expr::EnumConst { ty_name, value, const_name: _, span } => {
      let ty = resolve_ty(checker, *ty_name);
      match value {
        Some((expr, exp_ty)) => {
          let expeced_ty = check_type(checker, exp_ty)?;
          let expr_ty = check_expr(checker, expr)?;
          // TODO: This won't handle generics.
          unify(checker, expeced_ty, expr_ty, *span)?;
          ty
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
    Expr::Let { bind_value, binding, next_value } => {
      let bind_value_ty = check_expr(checker, bind_value)?;
      let binding_ty = check_pattern(checker, binding)?;
      unify(checker, bind_value_ty, binding_ty, binding.span())?;
      check_expr(checker, next_value)?
    }
    Expr::Record { to_extend, fields, span } => {
      let mut reqs = BTreeSet::new();
      for ((span, field), value) in fields.iter() {
        let value_ty = check_expr(checker, value)?;
        let value_node = checker.raise_to_node(value_ty);
        let field_req = Requirement::Field(*field, value_node);
        if reqs.contains(&field_req) {
          panic!(
            "Multiple of the same field {:?}, {:?}",
            checker.field(*field),
            span
          );
        }
        reqs.insert(field_req);
      }
      match to_extend {
        None => CType::Req(reqs, Box::new(CType::Record)),
        Some(to_extend) => {
          let extend_ty = check_expr(checker, to_extend)?;
          record_merge(checker, reqs, extend_ty, *span)?
        }
      }
    }
  })
}

fn check_pattern<'t>(checker: &mut Checker<'t>, binding: &Pattern) -> TRes<CType<'t>> {
  Ok(match binding {
    Pattern::Empty(_) => CType::Unknown,
    Pattern::Var(var, inner, span) => {
      let var_ty = CType::NodeType(*var);
      match inner {
        Some(inner) => {
          let inner_ty = check_pattern(checker, inner)?;
          unify(checker, var_ty, inner_ty, *span)?
        }
        None => var_ty,
      }
    }
    Pattern::EnumConst { ty_name, const_name: _, inner, span } => {
      let ty = resolve_ty(checker, *ty_name);
      match inner {
        Some((pattern, exp_ty)) => {
          let expeced_ty = check_type(checker, exp_ty)?;
          let pat_ty = check_pattern(checker, pattern)?;
          // TODO: This won't handle generics.
          unify(checker, expeced_ty, pat_ty, *span)?;
          ty
        }
        None => ty,
      }
    }
    Pattern::Record(_, _) => CType::Unknown, // todo!(),
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
    | CType::Bool
    | CType::Int
    | CType::Real
    | CType::Str
    | CType::Record
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
      | Type::TBool(_)
      | Type::TApply(_, _, _)
      | Type::TNode(_, _) => {
        let out = check_type(checker, ty)?;
        Ok((out.clone(), out.clone()))
      }
    }
  }
}

fn check_type<'t>(checker: &mut Checker<'t>, ty: &Type) -> TRes<CType<'t>> {
  Ok(match ty {
    Type::TBool(_) => CType::Bool,
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

fn error_label<'t, A>(
  checker: &mut Checker<'t>,
  field: FieldId,
  a: &CType<'t>,
  b: &CType<'t>,
  span: Span,
) -> Result<A, Error> {
  Err(Error::CheckExtraLabel {
    field: checker.field(field).to_owned(),
    span,
    a: a.render(checker),
    b: b.render(checker),
  })
}
