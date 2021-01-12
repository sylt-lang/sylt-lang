use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::collections::HashMap;
use owo_colors::OwoColorize;

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
    String(Rc<String>),
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

    pub fn add_line(&mut self, token_position: usize) {
        if token_position != self.last_line_offset {
            self.line_offsets.insert(self.curr(), token_position);
            self.last_line_offset = token_position;
        }
    }

    fn line(&self, ip: usize) -> usize {
        for i in (0..=ip).rev() {
            if let Some(line) = self.line_offsets.get(&i) {
                return *line;
            }
        }
        return 0;
    }

    pub fn debug_print(&self) {
        println!("     === {} ===", self.name.blue());
        for (i, s) in self.ops.iter().enumerate() {
            if self.line_offsets.contains_key(&i) {
                print!("{:5} ", self.line_offsets[&i].red());
            } else {
                print!("    {} ", "|".red());
            }
            println!("{:05} {:?}", i.blue(), s);
        }
        println!("");
    }

    pub fn add(&mut self, op: Op, token_position: usize) -> usize {
        let len = self.curr();
        self.add_line(token_position);
        self.ops.push(op);
        len
    }

    pub fn add_from(&mut self, ops: &[Op], token_position: usize) -> usize {
        let len = self.curr();
        self.add_line(token_position);
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
        let len = self.stack.len();
        let res = (self.stack[len-2].clone(), self.stack[len-1].clone());
        self.stack.truncate(len - 2);
        res
    }

    fn _peek_up(&self, amount: usize) -> Option<&Value> {
        self.stack.get(self.stack.len() - amount)
    }

    fn error(&self, kind: ErrorKind, message: Option<String>) -> Error {
        Error {
            kind,
            file: self.block.file.clone(),
            line: self.block.line(self.ip),
            message,
        }
    }

    pub fn run(&mut self) -> Result<(), Error>{
        const PRINT_WHILE_RUNNING: bool = true;
        const PRINT_BLOCK: bool = true;

        if PRINT_BLOCK {
            self.block.debug_print();
        }

        loop {
            if PRINT_WHILE_RUNNING {
                print!("    [");
                for (i, s) in self.stack.iter().enumerate() {
                    if i != 0 {
                        print!(" ");
                    }
                    match s {
                        Value::String(rc) => print!("{:?}<{}>", rc.green(), Rc::strong_count(rc)),
                        _ => print!("{:?}", s.green()),
                    }
                }
                println!("]");

                println!("{:5} {:05} {:?}", self.block.line(self.ip).red(), self.ip.blue(), self.block.ops[self.ip]);
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
                        (Value::String(a), Value::String(b)) => {
                            self.stack.push(Value::String(Rc::from(format!("{}{}", a, b))))
                        }
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
