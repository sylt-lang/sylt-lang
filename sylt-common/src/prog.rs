use std::cell::RefCell;
use std::rc::Rc;

use crate::{Block, RustFunction, Value};

#[derive(Clone)]
pub struct Prog {
    pub blocks: Vec<Rc<RefCell<Block>>>,
    pub functions: Vec<RustFunction>,
    pub constants: Vec<Value>,
    pub strings: Vec<String>,
}
