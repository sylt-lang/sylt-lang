pub mod blob;
pub mod block;
pub mod error;
pub mod op;
pub mod prog;
pub mod rc;
pub mod ty;
pub mod upvalue;
pub mod value;

use std::borrow::Cow;

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
pub type RustFunction = fn(&[Value], RuntimeContext) -> Result<Value, error::RuntimeError>;

pub trait Machine {
    fn stack(&self) -> Cow<[Value]>;
    fn blobs(&self) -> &[Blob];
    fn eval_op(&mut self, op: Op) -> Result<OpResult, Error>;
}

pub struct RuntimeContext<'t> {
    pub typecheck: bool,
    pub blobs: &'t [Blob],
}
