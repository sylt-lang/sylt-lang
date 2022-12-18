#![allow(dead_code)]

use crate::ast;
use crate::error::*;
use crate::name_resolution::*;

#[derive(Clone, Debug)]
enum CType {
  NodeType(NameId),
  // Type,
  Unknown,
  Foreign,
  Int,
  // Alias(Box<CType<'t>>),
  // Custom(Box<CType<'t>>),
  Apply(Box<CType>, Box<CType>),
  Function(Box<CType>, Box<CType>),
}

#[derive(Clone, Debug)]
enum Node {
  Child(NameId),
  Ty(Box<CType>),
}

struct Checker {
  types: Vec<Node>,
}

type TRes<A> = Result<A, Error>;

pub fn check<'t>(names: &Vec<Name<'t>>, defs: &Vec<Def>) -> TRes<()> {
  // These are the only nodes which should ever be created. Otherwise memory usage will explode.
  let mut checker = Checker {
    types: names
      .iter()
      .map(|name| match name.is_type {
        true => Node::Ty(Box::new(CType::Unknown)),
        false => Node::Ty(Box::new(CType::Unknown)),
      })
      .collect(),
  };

  for def in defs {
    check_def(&mut checker, def)?;
  }

  for def in defs {
    match def {
      Def::Def { name, .. }
      | Def::ForiegnDef { name, .. }
      | Def::Type { name, .. }
      | Def::ForeignType { name, .. } => {
        let NameId(slot) = *name;
        let x = resolve_ty(&mut checker, *name);
        let ty = bake_type(&mut checker, x);
        let name = names[slot].name;
        println!("{:?} - {:#?}", name, ty);
      }
    }
  }

  Ok(())
}

fn bake_type(checker: &mut Checker, ty: CType) -> CType {
  match ty {
    CType::NodeType(id) => resolve_ty(checker, id),
    CType::Unknown => CType::Unknown,
    CType::Foreign => CType::Foreign,
    CType::Int => CType::Int,
    CType::Apply(a, b) => CType::Apply(
      Box::new(bake_type(checker, *a)),
      Box::new(bake_type(checker, *b)),
    ),
    CType::Function(a, b) => CType::Function(
      Box::new(bake_type(checker, *a)),
      Box::new(bake_type(checker, *b)),
    ),
  }
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
    Def::Type { name, args, body, span } => {
      // TODO! More needs to be done here, no?
    }
    Def::ForeignType { name, span } => {
      // TODO! More needs to be done here, no?
    }
  })
}

fn unify(checker: &mut Checker, a: CType, b: CType, span: Span) -> TRes<CType> {
  Ok(match (a, b) {
    (CType::Unknown, b) => b,
    (a, CType::Unknown) => a,
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
    (CType::Foreign, CType::Foreign) => CType::Foreign,
    (CType::Int, CType::Int) => CType::Int,
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
    (a, b) => return error_unify("Failed to merge types", a, b, span),
  })
}

fn check_expr(checker: &mut Checker, body: &Expr) -> TRes<CType> {
  // TODO
  Ok(match body {
    Expr::EInt(_, _) => CType::Int,
    Expr::Var(name, _) => resolve_ty(checker, *name),
    Expr::Un(_, _) => todo!(),
    Expr::Bin(ast::BinOp::Add(at), a, b) => {
      let a_ty = check_expr(checker, a)?;
      let b_ty = check_expr(checker, b)?;
      unify(checker, a_ty, b_ty, *at)?
    }
    Expr::Bin(_, a, b) => {
      return error_msg(
        "Do not support other operators than addition!",
        a.span(),
        b.span(),
      )
    }
  })
}

fn resolve(checker: &mut Checker, NameId(slot): &NameId) -> NameId {
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

fn resolve_ty(checker: &mut Checker, a: NameId) -> CType {
  let NameId(slot) = resolve(checker, &a);
  if let Node::Ty(ty) = checker.types[slot].clone() {
    *ty
  } else {
    panic!("Invariant doesn't hold! Not an inner most type!")
  }
}

fn inject(checker: &mut Checker, a_id: NameId, c: CType) -> CType {
  let NameId(slot) = resolve(checker, &a_id);
  checker.types[slot] = Node::Ty(Box::new(c.clone()));
  c
}

fn unify_params(checker: &mut Checker, ty: &Type, args: &[NameId]) -> TRes<(CType, CType)> {
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
      Type::TInt(_) | Type::TForeign(_) | Type::TApply(_, _, _) | Type::TNode(_, _) => {
        Ok((CType::Unknown, CType::Unknown))
      }
    }
  }
}

fn check_type(checker: &mut Checker, ty: &Type) -> TRes<CType> {
  // TODO
  Ok(match ty {
    Type::TInt(_) => CType::Int,
    Type::TForeign(_) => CType::Foreign,
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

fn error_msg<A>(msg: &'static str, a_span: Span, b_span: Span) -> TRes<A> {
  Err(Error::CheckMsg { msg, a_span, b_span })
}

fn error_unify(msg: &'static str, a: CType, b: CType, span: Span) -> Result<CType, Error> {
  Err(Error::CheckUnify {
    msg,
    span,
    a: format!("{:?}", a),
    b: format!("{:?}", b),
  })
}
