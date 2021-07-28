pub mod blob;
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

pub use blob::Blob;
pub use block::{Block, BlockLinkState};
pub use error::Error;
pub use op::{Op, OpResult};
pub use prog::Prog;
pub use ty::Type;
pub use upvalue::UpValue;
pub use value::{MatchableValue, Value};

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
    fn blobs(&self) -> &[Blob];
    fn eval_op(&mut self, op: Op) -> Result<OpResult, Error>;
    fn eval_call(&mut self, callable: Value, args: &[&Value]) -> Result<Value, Error>;
}

pub struct RuntimeContext<'m> {
    pub typecheck: bool,
    pub stack_base: usize,
    pub machine: &'m mut dyn Machine,
}
