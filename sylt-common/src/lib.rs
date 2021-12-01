pub mod block;
pub mod error;
pub mod op;
pub mod prog;
pub mod ty;
pub mod upvalue;
pub mod value;

use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;

pub use block::{Block, BlockLinkState};
pub use error::Error;
pub use op::{Op, OpResult};
pub use prog::BytecodeProg;
pub use ty::Type;
pub use upvalue::UpValue;
pub use value::Value;

/// A linkable external function. Created either manually or using
/// [sylt_macro::extern_function].
pub type RustFunction = fn(RuntimeContext) -> Result<Value, error::RuntimeError>;

#[derive(Debug)]
pub struct Frame {
    pub stack_offset: usize,
    pub block: Rc<RefCell<Block>>,
    pub ip: usize,
    pub contains_upvalues: bool,
}

pub trait Machine {
    fn stack_from_base(&self, base: usize) -> Cow<[Value]>;
    fn constants(&self) -> &[Value];
    fn eval_op(&mut self, op: Op) -> Result<OpResult, Error>;
    fn eval_call(&mut self, callable: Value, args: &[&Value]) -> Result<Value, Error>;
    fn args(&self) -> &[String];
}

pub struct RuntimeContext<'m> {
    pub stack_base: usize,
    pub machine: &'m mut dyn Machine,
}
