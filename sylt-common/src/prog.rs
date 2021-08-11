use std::cell::RefCell;
use std::rc::Rc;

use crate::{Blob, Block, RustFunction, Value};

#[derive(Clone)]
pub struct Prog {
    pub blocks: Vec<Rc<RefCell<Block>>>,
    pub blobs: Vec<Blob>,
    pub functions: Vec<RustFunction>,
    pub constants: Vec<Value>,
    pub strings: Vec<String>,
}
