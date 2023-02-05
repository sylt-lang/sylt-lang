#![allow(dead_code)]

use std::cmp::Ordering;
use std::collections::btree_map::Entry;
use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::ast;
use crate::error::*;
use crate::name_resolution::*;

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub enum CType<'t> {
  NodeType(NameId),
  // TODO - add Error type so we can report multiple errors and stuff
  Unknown,
  Foreign(&'t Name<'t>),
  // Is this a good idea to code here?
  Generic(usize),
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
  // The public function
  pub fn render_to_string(
    &self,
    types: Vec<Node<'t>>,
    names: &'t Vec<Name<'t>>,
    fields: &'t BTreeMap<FieldId, &'t str>,
  ) -> String {
    // TODO: We need to clone types for now, but we should be able to not clone it later by
    // having a mutable borrow - preferably CType shouldn't care about Checker.
    let mut checker = Checker { types, names, fields };
    self.render(&mut checker)
  }

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
        let rs = rs
          .iter()
          .map(|r| r.to_name(checker))
          .collect::<Vec<String>>()
          .join(", ");
        format!("([{}] => {})", rs, t)
      }
      CType::Generic(i) => {
        format!("#{}", *i)
      }
    }
  }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Requirement {
  Num,
  Field(FieldId, NameId),
}

impl PartialOrd for Requirement {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for Requirement {
  fn cmp(&self, other: &Self) -> Ordering {
    fn to_tuple(s: &Requirement) -> (usize, usize) {
      match s {
        Requirement::Num => (0, 0),
        Requirement::Field(FieldId(n), _) => (1, *n),
      }
    }

    to_tuple(self).cmp(&to_tuple(other))
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

  // This function is really expensive memory wise. Removing a call to this function is big profit!
  fn raise_to_node(&mut self, ty: CType<'t>) -> NameId {
    match ty {
      CType::NodeType(id) => id,
      ty => {
        let name = NameId(self.types.len());
        self.types.push(Node::Ty(Box::new(ty)));
        name
      }
    }
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
      .enumerate()
      .map(|(i, Name { is_generic, .. })| {
        if *is_generic {
          Node::Ty(Box::new(CType::Generic(i)))
        } else {
          Node::Ty(Box::new(CType::Unknown))
        }
      })
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
      let ty = check_type(checker, ty)?;
      let body = check_expr(checker, body)?;
      let mut def_ty = body;
      for arg in args.iter().rev() {
        let arg = check_pattern(checker, arg)?;
        def_ty = CType::Function(Box::new(arg), Box::new(def_ty));
      }
      let name_ty = unify(checker, CType::NodeType(*name), def_ty, *span)?;
      unify(checker, name_ty, ty, *span)?;
    }
    Def::ForiegnDef { ty, name, span, foreign_block: _ } => {
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
    (a, b) if a == b => a,
    (CType::Unknown, b) => b,
    (a, CType::Unknown) => a,
    (CType::Req(ar, box CType::Record), CType::Req(br, box CType::Record)) => {
      for aa in ar.iter() {
        match (br.get(aa), aa) {
          (Some(Requirement::Field(_, a_id)), Requirement::Field(_, b_id)) => {
            unify(
              checker,
              CType::NodeType(*a_id),
              CType::NodeType(*b_id),
              span,
            )?;
          }
          (_, Requirement::Field(field, _)) => {
            let err = error_unify(
              checker,
              "There are extra labels in one record",
              CType::Req(ar.clone(), Box::new(CType::Record)),
              CType::Req(br.clone(), Box::new(CType::Record)),
              span,
            );
            return with_label(checker, *field, err);
          }
          (_, _) => {
            return error_unify(
              checker,
              "There are extra labels in one record",
              CType::Req(ar.clone(), Box::new(CType::Record)),
              CType::Req(br.clone(), Box::new(CType::Record)),
              span,
            );
          }
        }
      }
      for bb in br.iter() {
        match (ar.get(bb), bb) {
          (Some(Requirement::Field(_, b_id)), Requirement::Field(_, a_id)) => {
            unify(
              checker,
              CType::NodeType(*a_id),
              CType::NodeType(*b_id),
              span,
            )?;
          }
          (_, Requirement::Field(field, _)) => {
            let err = error_unify(
              checker,
              "There are extra labels in one record",
              CType::Req(ar.clone(), Box::new(CType::Record)),
              CType::Req(br.clone(), Box::new(CType::Record)),
              span,
            );
            return with_label(checker, *field, err);
          }
          (_, _) => {
            return error_unify(
              checker,
              "There are extra labels in one record",
              CType::Req(ar.clone(), Box::new(CType::Record)),
              CType::Req(br.clone(), Box::new(CType::Record)),
              span,
            );
          }
        }
      }

      CType::Req(ar, Box::new(CType::Record))
    }
    (CType::Req(ar, inner_a), CType::Req(br, inner_b)) => {
      let c = unify(checker, *inner_a, *inner_b, span)?;
      let mut cr = ar.clone();
      for bb in br.iter() {
        match (cr.get(bb), bb) {
          (Some(Requirement::Field(field, a_id)), Requirement::Field(_, b_id)) => {
            let u = unify(
              checker,
              CType::NodeType(*a_id),
              CType::NodeType(*b_id),
              span,
            );
            with_label(checker, *field, u)?;
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
    // Prevents infinite recursion if we've linked a lot of things, which really isn't a problem.
    (CType::NodeType(a_id), CType::NodeType(b_id))
      if resolve(checker, &a_id) == resolve(checker, &b_id) =>
    {
      CType::NodeType(a_id)
    }
    (CType::NodeType(a_id), b) => {
      let inner_a = resolve_ty(checker, a_id);
      let c = unify(checker, inner_a, b, span)?;
      inject(checker, a_id, c);
      CType::NodeType(a_id)
    }
    (a, CType::NodeType(b_id)) => {
      let inner_b = resolve_ty(checker, b_id);
      let c = unify(checker, a, inner_b, span)?;
      inject(checker, b_id, c);
      CType::NodeType(b_id)
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
    // CType::Apply(_, _) => todo!(),
    // CType::Function(_, _) => todo!(),
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
    Expr::Var(name, _) => specialize_if_needed(checker, CType::NodeType(*name)),
    Expr::EnumConst { ty_name, value, const_name: _, span } => {
      let ty = CType::NodeType(*ty_name);
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
    Expr::Un(ast::UnOp::Not(at), expr, _) => {
      let expr_ty = check_expr(checker, expr)?;
      unify(checker, expr_ty, CType::Bool, *at)?
    }
    Expr::Bin(ast::BinOp::RevCall(_), _, _, _) => unreachable!("Compiled to `Call`"),
    Expr::Bin(ast::BinOp::Call(at), f, a, _) => {
      let f_ty = check_expr(checker, f)?;
      let a_ty = check_expr(checker, a)?;
      // Can this be removed?
      match unify(
        checker,
        f_ty,
        CType::Function(Box::new(a_ty), Box::new(CType::Unknown)),
        *at,
      )? {
        CType::NodeType(name) => {
          if let CType::Function(_, ret) = resolve_ty(checker, name) {
            *ret
          } else {
            unreachable!()
          }
        }
        CType::Function(_, ret) => *ret,
        _ => unreachable!(),
      }
    }
    Expr::Bin(ast::BinOp::Add(at) | ast::BinOp::Sub(at) | ast::BinOp::Mul(at), a, b, _) => {
      let a_ty = check_expr(checker, a)?;
      let b_ty = check_expr(checker, b)?;
      let c_ty = unify(checker, a_ty, b_ty, *at)?;
      unify(checker, c_ty, Requirement::Num.to_ctype(), *at)?
    }
    Expr::Bin(
      ast::BinOp::Neq(at) | ast::BinOp::Eq(at) | ast::BinOp::Lt(at) | ast::BinOp::LtEq(at),
      a,
      b,
      _,
    ) => {
      let a_ty = check_expr(checker, a)?;
      let b_ty = check_expr(checker, b)?;
      let c_ty = unify(checker, a_ty, b_ty, *at)?;
      unify(checker, c_ty, Requirement::Num.to_ctype(), *at)?;
      CType::Bool
    }
    Expr::Bin(ast::BinOp::And(at) | ast::BinOp::Or(at), a, b, _) => {
      let a_ty = check_expr(checker, a)?;
      let b_ty = check_expr(checker, b)?;
      let c_ty = unify(checker, a_ty, b_ty, *at)?;
      unify(checker, c_ty, CType::Bool, *at)?
    }
    Expr::Bin(ast::BinOp::Div(at), a, b, _) => {
      let a_ty = check_expr(checker, a)?;
      let b_ty = check_expr(checker, b)?;
      let c_ty = unify(checker, a_ty, b_ty, *at)?;
      unify(checker, c_ty, CType::Real, *at)?
    }
    Expr::Let { bind_value, binding, next_value } => {
      let out = check_expr(checker, next_value)?;

      let bind_value_ty = check_expr(checker, bind_value)?;
      let binding_ty = check_pattern(checker, binding)?;
      unify(checker, bind_value_ty, binding_ty, binding.span())?;
      out
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
    Expr::Match { value, branches, span: _ } => {
      let mut outer_match_ty = check_expr(checker, value)?;

      // NOTE[et]: There's different ways of doing this, it might be more nice to depth-first
      // instead of breath first.
      for WithBranch { pattern, condition: _, value: _, span } in branches.iter() {
        let pattern_ty = check_pattern(checker, pattern)?;
        outer_match_ty = unify(checker, pattern_ty, outer_match_ty, *span)?;
      }

      for WithBranch { pattern: _, condition, value: _, span } in branches.iter() {
        if let Some(condition) = condition {
          let condition_ty = check_expr(checker, condition)?;
          unify(checker, condition_ty, CType::Bool, *span)?;
        }
      }

      let mut ret_ty = CType::Unknown;
      for WithBranch { pattern: _, condition: _, value, span } in branches.iter() {
        let value_ty = check_expr(checker, value)?;
        ret_ty = unify(checker, value_ty, ret_ty, *span)?;
      }

      ret_ty
    }

    Expr::Lambda { args, body, span: _ } => {
      let body = check_expr(checker, body)?;
      let mut def_ty = body;
      for arg in args.iter().rev() {
        let arg = check_pattern(checker, arg)?;
        def_ty = CType::Function(Box::new(arg), Box::new(def_ty));
      }
      def_ty
    }
  })
}

fn specialize_if_needed<'t>(checker: &mut Checker<'t>, ty: CType<'t>) -> CType<'t> {
  fn specialize_inner<'t>(
    checker: &mut Checker<'t>,
    ty: CType<'t>,
    given_names: &mut BTreeMap<usize, NameId>,
  ) -> CType<'t> {
    match ty {
      CType::Unknown
      | CType::Foreign(_)
      | CType::Bool
      | CType::Int
      | CType::Real
      | CType::Str
      | CType::Record => ty,

      CType::Generic(i) => match given_names.entry(i) {
        Entry::Vacant(v) => {
          let new_node = checker.raise_to_node(CType::Unknown);
          v.insert(new_node);
          CType::NodeType(new_node)
        }
        Entry::Occupied(o) => CType::NodeType(*o.get()),
      },

      CType::Req(reqs, inner) => CType::Req(
        reqs.clone(),
        Box::new(specialize_inner(checker, *inner, given_names)),
      ),
      CType::Apply(a, b) => {
        let a = Box::new(specialize_inner(checker, *a, given_names));
        let b = Box::new(specialize_inner(checker, *b, given_names));
        CType::Apply(a, b)
      }
      CType::Function(a, b) => {
        let a = Box::new(specialize_inner(checker, *a, given_names));
        let b = Box::new(specialize_inner(checker, *b, given_names));
        CType::Function(a, b)
      }
      CType::NodeType(node) => {
        // NOTE[et]: I dislike this - maybe we should have two function, one that looks for generics and
        // one that copies, and we only copy the types when we absolutely need to?
        match resolve_ty(checker, node) {
          CType::Unknown
          | CType::Foreign(_)
          | CType::Bool
          | CType::Int
          | CType::Real
          | CType::Str
          | CType::Record => CType::NodeType(node),

          CType::NodeType(_)
          | CType::Generic(_)
          | CType::Req(_, _)
          | CType::Apply(_, _)
          | CType::Function(_, _) => {
            let inner = resolve_ty(checker, node);
            specialize_inner(checker, inner, given_names)
          }
        }
      }
    }
  }

  specialize_inner(checker, ty, &mut BTreeMap::new())
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
      let ty = CType::NodeType(*ty_name);
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
    Pattern::Record(fields, _) => {
      let mut reqs = BTreeSet::new();
      for (field, field_span, pat) in fields.iter() {
        let value_ty = check_pattern(checker, pat)?;
        let value_node = checker.raise_to_node(value_ty);
        let field_req = Requirement::Field(*field, value_node);
        if reqs.contains(&field_req) {
          panic!(
            "Multiple of the same field {:?}, {:?}",
            checker.field(*field),
            field_span
          );
        }
        reqs.insert(field_req);
      }
      CType::Req(reqs, Box::new(CType::Unknown))
    }
    Pattern::PBool(_, _) => CType::Bool,
    Pattern::PInt(_, _) => CType::Int,
    Pattern::PReal(_, _) => CType::Real,
    Pattern::PStr(_, _) => CType::Str,
  })
}

fn resolve<'t>(checker: &mut Checker<'t>, NameId(slot): &NameId) -> NameId {
  match checker.types[*slot] {
    Node::Child(parent) => {
      let at = resolve(checker, &parent);
      checker.types[*slot] = Node::Child(at);
      at
    }
    Node::Ty(_) => NameId(*slot),
  }
}

// Think twice before using this function, it's usually better to keep thinks linked.
fn resolve_ty<'t>(checker: &mut Checker<'t>, a: NameId) -> CType<'t> {
  let NameId(slot) = resolve(checker, &a);
  if let Node::Ty(ty) = checker.types[slot].clone() {
    *ty
  } else {
    panic!("Invariant doesn't hold! Not an inner most type!")
  }
}

fn inject<'t>(checker: &mut Checker<'t>, a_id: NameId, c: CType<'t>) {
  let NameId(slot) = resolve(checker, &a_id);
  match &c {
    CType::NodeType(c) if c == &a_id => panic!("Typechecker bug!"),
    CType::NodeType(c) if c != &a_id => checker.types[slot] = Node::Child(*c),
    c => checker.types[slot] = Node::Ty(Box::new(c.clone())),
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
    Type::TNode(slot, _) => CType::NodeType(*slot),
    Type::TFunction(a, b, _) => {
      let a_ty = check_type(checker, a)?;
      let b_ty = check_type(checker, b)?;
      CType::Function(Box::new(a_ty), Box::new(b_ty))
    }
    Type::TRecord { fields, span: _ } => {
      let mut reqs = BTreeSet::new();
      for (span, field, inner_ty) in fields.iter() {
        let value_ty = check_type(checker, inner_ty)?;
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
      CType::Req(reqs, Box::new(CType::Record))
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

fn with_label<'t, A>(
  checker: &Checker<'t>,
  field: FieldId,
  curr: Result<A, Error>,
) -> Result<A, Error> {
  match curr {
    Ok(curr) => Ok(curr),
    Err(inner) => Err(Error::CheckField {
      field: checker.field(field).to_string(),
      inner: Box::new(inner),
    }),
  }
}
