// Do name resolution
// Type check - needs to be memory efficient
// Two scopes? Module and function?

#![allow(dead_code)]
use crate::ast;
use crate::ast::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VarId(usize);

#[derive(Debug)]
pub struct StackFrame(usize);

#[derive(Debug, Clone)]
pub struct Var<'t> {
  global: bool,
  name: &'t str,
  def_at: Span,
  id: VarId,
  usages: Vec<Span>,
}

#[derive(Debug, Clone)]
pub enum Def {
  Def {
    thing: VarId,
    args: Vec<VarId>,
    body: Expr,
    span: Span,
  },
  Type {
    // thing: TypeId,
    // args: Vec<TypeId>,
    // body: TypeId,
    // span: Span,
  },
  Enum {
    // thing: TypeId,
    // args: Vec<VarId>,
    // // constructors: Vec<EnumConst<'t>>,
    // span: Span,
  },
}

#[derive(Debug, Clone)]
pub enum Expr {
  EInt(i64, Span),
  Var(VarId, Span),

  Un(UnOp, Box<Expr>),
  Bin(BinOp, Box<Expr>, Box<Expr>),
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

struct Ctx<'t> {
  vars: Vec<Var<'t>>,
  stack: Vec<VarId>,
}

impl<'t> Ctx<'t> {
  fn push_var(&mut self, global: bool, name: &'t str, def_at: Span) -> VarId {
    let id = VarId(self.vars.len());
    self
      .vars
      .push(Var { global, name, def_at, id, usages: vec![] });
    id
  }

  pub fn push_local_var(&mut self, name: &'t str, def_at: Span) -> VarId {
    self.push_var(false, name, def_at)
  }

  pub fn push_global_var(&mut self, name: &'t str, def_at: Span) -> VarId {
    self.push_var(true, name, def_at)
  }


  pub fn read_var(&mut self, at: Span, name: &'t str) -> Option<VarId> {
    for VarId(v) in self.stack.iter().rev() {
        if self.vars[*v].name == name {
            self.vars[*v].usages.push(at);
            return Some(VarId(*v));
        }
    }
    None
  }

  pub fn push_frame(&self) -> StackFrame {
      StackFrame(self.stack.len())
  }

  pub fn pop_frame(&mut self, StackFrame(n): StackFrame) {
      self.stack.truncate(n);
  }
}

// TODO, translate some programs
