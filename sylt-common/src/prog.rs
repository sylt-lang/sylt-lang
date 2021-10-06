use std::cell::RefCell;
use std::rc::Rc;

use crate::{Block, RustFunction, Value};

#[derive(Clone)]
pub struct BytecodeProg {
    pub blocks: Vec<Rc<RefCell<Block>>>,
    pub functions: Vec<RustFunction>,
    pub constants: Vec<Value>,
    pub strings: Vec<String>,
}

#[derive(Clone)]
pub enum Prog {
    Bytecode(BytecodeProg),
    Lua,
}
