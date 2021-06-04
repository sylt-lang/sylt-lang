use crate::error::Error;
use crate::syntree;
use crate::{Prog, Op, Block, Value, Type};
use std::collections::{hash_map::Entry, HashMap};
use crate::rc::Rc;
use std::cell::RefCell;

struct Variable {
    name: String,
    typ: Type,
    slot: usize,
    line: usize,
}

struct Compiler {
    globals: Vec<Variable>,
    blocks: Vec<Block>,

    panic: bool,
    errors: Vec<Error>,

    strings: Vec<String>,
    constants: Vec<Value>,

    values: HashMap<Value, usize>,
}

impl Compiler {
    fn new() -> Self {
        Self {
            globals: Vec::new(),
            blocks: Vec::new(),

            panic: false,
            errors: Vec::new(),

            strings: Vec::new(),
            constants: Vec::new(),

            values: HashMap::new(),
        }
    }

    fn value(&mut self, value: Value) -> usize {
        match self.values.entry(value.clone()) {
            Entry::Vacant(e) => {
                let slot = self.constants.len();
                e.insert(slot);
                self.constants.push(value);
                slot
            }
            Entry::Occupied(e) => {
                *e.get()
            }
        }
    }

    fn compile(mut self, tree: syntree::Prog) -> Result<Prog, Vec<Error>> {
        self.blocks.push(Block::new("/preamble/", &tree.modules[0].0));
        if self.errors.is_empty() {
            Ok(Prog {
                blocks: self.blocks.into_iter().map(|x| Rc::new(RefCell::new(x))).collect(),
                functions: Vec::new(),
                constants: self.constants,
                strings: self.strings,
            })
        } else {
            Err(self.errors)
        }
    }
}


pub fn compile(prog: syntree::Prog) -> Result<Prog, Vec<Error>> {
    Compiler::new().compile(prog)
}
