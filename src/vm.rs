use std::path::{Path, PathBuf};
use std::collections::HashMap;

use crate::error::{Error, ErrorKind};

macro_rules! error {
    ( $thing:expr, $kind:expr) => {
        return Err($thing.error($kind, None));
    };
    ( $thing:expr, $kind:expr, $msg:expr) => {
        return Err($thing.error($kind, Some($msg)));
    };
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum Value {
    Float(f64),
    Int(i64),
    Bool(bool),
    String(String),
}

#[derive(Debug, Clone)]
pub enum Op {
    Illegal,

    Pop,
    Constant(Value),

    Add,
    Sub,
    Mul,
    Div,
    Neg,

    And,
    Or,
    Not,

    Jmp(usize),
    JmpFalse(usize),

    Equal,   // ==
    Less,    // <
    Greater, // >

    AssertEqual,
    Unreachable,

    ReadLocal(usize),
    Assign(usize),


    Print,
    Return,
}

#[derive(Debug)]
pub struct Block {
    name: String,
    file: PathBuf,
    ops: Vec<Op>,
    last_line_offset: usize,
    line_offsets: HashMap<usize, usize>,
}

impl Block {
    pub fn new(name: &str, file: &Path) -> Self {
        Self {
            name: String::from(name),
            file: file.to_owned(),
            ops: Vec::new(),
            last_line_offset: 0,
            line_offsets: HashMap::new(),
        }
    }

    pub fn line(&mut self, token_position: usize) {
        if token_position != self.last_line_offset {
            self.line_offsets.insert(self.curr(), token_position);
            self.last_line_offset = token_position;
        }
    }

    pub fn add(&mut self, op: Op, token_position: usize) -> usize {
        let len = self.curr();
        self.line(token_position);
        self.ops.push(op);
        len
    }

    pub fn add_from(&mut self, ops: &[Op], token_position: usize) -> usize {
        let len = self.curr();
        self.line(token_position);
        self.ops.extend_from_slice(ops);
        len
    }

    pub fn curr(&self) -> usize {
        self.ops.len()
    }

    pub fn patch(&mut self, op: Op, pos: usize) {
        self.ops[pos] = op;
    }
}

#[derive(Debug)]
pub struct VM {
    stack: Vec<Value>,

    block: Block,
    ip: usize,
}

pub fn run_block(block: Block) -> Result<(), Error> {
    let mut vm = VM {
        stack: Vec::new(),

        block,
        ip: 0,
    };

    vm.run()
}

impl VM {
    fn pop_twice(&mut self) -> (Value, Value) {
        let (a, b) = (self.stack.pop().unwrap(), self.stack.pop().unwrap());
        (b, a)
    }

    fn _peek_up(&self, amount: usize) -> Option<&Value> {
        self.stack.get(self.stack.len() - amount)
    }

    fn error(&self, kind: ErrorKind, message: Option<String>) -> Error {
        let find_line = || {
            for i in (0..=self.ip).rev() {
                if let Some(line) = self.block.line_offsets.get(&i) {
                    return *line;
                }
            }
            return 0;
        };

        Error {
            kind,
            file: self.block.file.clone(),
            line: find_line(),
            message,
        }
    }

    pub fn run(&mut self) -> Result<(), Error>{
        const PRINT_WHILE_RUNNING: bool = true;
        const PRINT_BLOCK: bool = true;

        if PRINT_BLOCK {
            println!(" === {} ===", self.block.name);
            for s in self.block.ops.iter() {
                println!("| {:?}", s);
            }
            println!("");
        }

        loop {
            if PRINT_WHILE_RUNNING {
                print!("    [");
                for s in self.stack.iter() {
                    print!("{:?} ", s);
                }
                println!("]");

                println!("{:?}", self.block.ops[self.ip]);
            }

            let op = self.block.ops[self.ip].clone();
            match op {
                Op::Illegal => {
                    error!(self, ErrorKind::InvalidProgram);
                }

                Op::Unreachable => {
                    error!(self, ErrorKind::Unreachable);
                }

                Op::Pop => {
                    self.stack.pop();
                }

                Op::Constant(value) => {
                    self.stack.push(value.clone());
                }

                Op::Neg => {
                    match self.stack.pop().unwrap() {
                        Value::Float(a) => self.stack.push(Value::Float(-a)),
                        Value::Int(a) => self.stack.push(Value::Int(-a)),
                        a => error!(self, ErrorKind::TypeError(op.clone(), vec![a])),
                    }
                }

                Op::Add => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(b + a)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(b + a)),
                        (Value::String(a), Value::String(b)) => self.stack.push(Value::String(format!("{}{}", a, b))),
                        (a, b) => error!(self, ErrorKind::TypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Sub => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(b - a)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(b - a)),
                        (a, b) => error!(self, ErrorKind::TypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Mul => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(b * a)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(b * a)),
                        (a, b) => error!(self, ErrorKind::TypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Div => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(b / a)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(b / a)),
                        (a, b) => error!(self, ErrorKind::TypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Equal => {
                    let (a, b) = self.pop_twice();
                    self.stack.push(Value::Bool(a == b));
                }

                Op::Less => {
                    let (a, b) = self.pop_twice();
                    self.stack.push(Value::Bool(a < b));
                }

                Op::Greater => {
                    let (a, b) = self.pop_twice();
                    self.stack.push(Value::Bool(a > b));
                }

                Op::And => {
                    match self.pop_twice() {
                        (Value::Bool(a), Value::Bool(b)) => self.stack.push(Value::Bool(a && b)),
                        (a, b) => error!(self, ErrorKind::TypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Or => {
                    match self.pop_twice() {
                        (Value::Bool(a), Value::Bool(b)) => self.stack.push(Value::Bool(a || b)),
                        (a, b) => error!(self, ErrorKind::TypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Not => {
                    match self.stack.pop().unwrap() {
                        Value::Bool(a) => self.stack.push(Value::Bool(!a)),
                        a => error!(self, ErrorKind::TypeError(op.clone(), vec![a])),
                    }
                }

                Op::Jmp(line) => {
                    self.ip = line;
                    continue;
                }

                Op::JmpFalse(line) => {
                    if Some(Value::Bool(false)) == self.stack.pop() {
                        self.ip = line;
                        continue;
                    }
                }

                Op::AssertEqual => {
                    let (a, b) = self.pop_twice();
                    if a != b {
                        error!(self, ErrorKind::AssertFailed(a, b));
                    }
                    self.stack.push(Value::Bool(a == b));
                }

                Op::ReadLocal(slot) => {
                    self.stack.push(self.stack[slot].clone());
                }

                Op::Assign(slot) => {
                    self.stack[slot] = self.stack.pop().unwrap();
                }

                Op::Print => {
                    println!("PRINT: {:?}", self.stack.pop());
                }

                Op::Return => {
                    return Ok(());
                }
            }
            self.ip += 1;
        }
    }
}
