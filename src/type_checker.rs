#![allow(dead_code)]

use crate::error::*;
use crate::name_resolution::*;

struct NodeId(usize);

enum CType<'t> {
  NodeType(&'t Node<'t>),
  Type,
  Unknown,
  Custom(Box<CType<'t>>), 
}

struct Node<'t> {
  parent: Option<&'t Node<'t>>,
  ty: CType<'t>,
  // TODO: more fields
}

struct Checker<'t> {
  types: Vec<Node<'t>>,
}

type TRes<A> = Result<A, Error>;

pub fn check<'t>(names: &Vec<Name<'t>>, ast: &Vec<Def>) -> TRes<()> {
  // These are the only nodes which should ever be created. Otherwise we will get exponential
  // memory usage.
  let checker = Checker {
    types: names
      .iter()
      .map(|name| match name.is_type {
        true => Node { parent: None, ty: CType::Type },
        false => Node { parent: None, ty: CType::Unknown },
      })
      .collect(),
  };

  panic!();
}
