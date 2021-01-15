use owo_colors::OwoColorize;
use std::collections::HashMap;
use std::fmt::Debug;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use crate::compiler::Type;
use crate::error::{Error, ErrorKind};

macro_rules! error {
    ( $thing:expr, $kind:expr) => {
        return Err($thing.error($kind, None));
    };
    ( $thing:expr, $kind:expr, $msg:expr) => {
        return Err($thing.error($kind, Some($msg)));
    };
}

#[derive(Clone)]
pub enum Value {
    Float(f64),
    Int(i64),
    Bool(bool),
    String(Rc<String>),
    Function(Vec<Type>, Type, Rc<Block>),
    Nil,
}

impl Debug for Value {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Float(f) => write!(fmt, "(float {})", f),
            Value::Int(i) => write!(fmt, "(int {})", i),
            Value::Bool(b) => write!(fmt, "(bool {})", b),
            Value::String(s) => write!(fmt, "(string \"{}\")", s),
            Value::Function(args, ret, block) => write!(fmt, "(fn {}: {:?} -> {:?})", block.name, args, ret),
            Value::Nil => write!(fmt, "(nil)"),
        }
    }
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

    Assert,
    Unreachable,

    ReadLocal(usize),
    Assign(usize),

    Call(usize),

    Print,
    Return,
}

#[derive(Debug)]
pub struct Block {
    pub name: String,
    pub file: PathBuf,
    pub ops: Vec<Op>,
    pub last_line_offset: usize,
    pub line_offsets: HashMap<usize, usize>,
    pub line: usize,
}

impl Block {
    pub fn new(name: &str, file: &Path, line: usize) -> Self {
        Self {
            name: String::from(name),
            file: file.to_owned(),
            ops: Vec::new(),
            last_line_offset: 0,
            line_offsets: HashMap::new(),
            line,
        }
    }

    pub fn id(&self) -> (PathBuf, usize) {
        (self.file.clone(), self.line)
    }

    pub fn last_op(&self) -> Option<&Op> {
        self.ops.last()
    }

    pub fn add_line(&mut self, token_position: usize) {
        if token_position != self.last_line_offset {
            self.line_offsets.insert(self.curr(), token_position);
            self.last_line_offset = token_position;
        }
    }

    pub fn line(&self, ip: usize) -> usize {
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

    pub fn last_instruction(&mut self) -> &Op {
        self.ops.last().unwrap()
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
struct Frame {
    stack_offset: usize,
    block: Rc<Block>,
    ip: usize,
}

#[derive(Debug)]
pub struct VM {
    stack: Vec<Value>,
    frames: Vec<Frame>,
    print_blocks: bool,
    print_ops: bool,
}

impl VM {
    pub fn new() -> Self {
        Self {
            stack: Vec::new(),
            frames: Vec::new(),
            print_blocks: false,
            print_ops: false,
        }
    }

    pub fn print_blocks(mut self, b: bool) -> Self {
        self.print_blocks = b;
        self
    }

    pub fn print_ops(mut self, b: bool) -> Self {
        self.print_ops = b;
        self
    }

    fn pop_twice(&mut self) -> (Value, Value) {
        let len = self.stack.len();
        let res = (self.stack[len-2].clone(), self.stack[len-1].clone());
        self.stack.truncate(len - 2);
        res
    }

    fn _peek_up(&self, amount: usize) -> Option<&Value> {
        self.stack.get(self.stack.len() - amount)
    }

    fn frame(&self) -> &Frame {
        let last = self.frames.len() - 1;
        &self.frames[last]
    }

    fn frame_mut(&mut self) -> &mut Frame {
        let last = self.frames.len() - 1;
        &mut self.frames[last]
    }

    fn error(&self, kind: ErrorKind, message: Option<String>) -> Error {
        let frame = self.frames.last().unwrap();
        Error {
            kind,
            file: frame.block.file.clone(),
            line: frame.block.line(frame.ip),
            message,
        }
    }

    pub fn run(&mut self, block: Rc<Block>) -> Result<(), Error>{
        if let Err(err) = crate::typer::VM::new().print_ops(true).typecheck(Type::NoType, Rc::clone(&block)) {
            println!("TYPE ERROR: {}", err);
        }

        self.frames.push(Frame {
            stack_offset: 0,
            block,
            ip: 0
        });

        if self.print_blocks {
            self.frame().block.debug_print();
        }

        loop {
            if self.print_ops {
                let start = self.frame().stack_offset;
                print!("    {:3} [", start);
                for (i, s) in self.stack.iter().skip(start).enumerate() {
                    if i != 0 {
                        print!(" ");
                    }
                    print!("{:?}", s.green());
                }
                println!("]");

                println!("{:5} {:05} {:?}",
                         self.frame().block.line(self.frame().ip).red(),
                         self.frame().ip.blue(),
                         self.frame().block.ops[self.frame().ip]);
            }

            let op = self.frame().block.ops[self.frame().ip].clone();
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
                        a => error!(self, ErrorKind::RuntimeTypeError(op.clone(), vec![a])),
                    }
                }

                Op::Add => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(a + b)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(a + b)),
                        (Value::String(a), Value::String(b)) => {
                            self.stack.push(Value::String(Rc::from(format!("{}{}", a, b))))
                        }
                        (a, b) => error!(self, ErrorKind::RuntimeTypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Sub => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(a - b)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(a - b)),
                        (a, b) => error!(self, ErrorKind::RuntimeTypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Mul => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(a * b)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(a * b)),
                        (a, b) => error!(self, ErrorKind::RuntimeTypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Div => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(a / b)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(a / b)),
                        (a, b) => error!(self, ErrorKind::RuntimeTypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Equal => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Bool(a == b)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Bool(a == b)),
                        (Value::String(a), Value::String(b)) => self.stack.push(Value::Bool(a == b)),
                        (Value::Bool(a), Value::Bool(b)) => self.stack.push(Value::Bool(a == b)),
                        (a, b) => error!(self, ErrorKind::RuntimeTypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Less => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Bool(a < b)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Bool(a < b)),
                        (Value::String(a), Value::String(b)) => self.stack.push(Value::Bool(a < b)),
                        (Value::Bool(a), Value::Bool(b)) => self.stack.push(Value::Bool(a < b)),
                        (a, b) => error!(self, ErrorKind::RuntimeTypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Greater => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Bool(a > b)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Bool(a > b)),
                        (Value::String(a), Value::String(b)) => self.stack.push(Value::Bool(a > b)),
                        (Value::Bool(a), Value::Bool(b)) => self.stack.push(Value::Bool(a > b)),
                        (a, b) => error!(self, ErrorKind::RuntimeTypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::And => {
                    match self.pop_twice() {
                        (Value::Bool(a), Value::Bool(b)) => self.stack.push(Value::Bool(a && b)),
                        (a, b) => error!(self, ErrorKind::RuntimeTypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Or => {
                    match self.pop_twice() {
                        (Value::Bool(a), Value::Bool(b)) => self.stack.push(Value::Bool(a || b)),
                        (a, b) => error!(self, ErrorKind::RuntimeTypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Not => {
                    match self.stack.pop().unwrap() {
                        Value::Bool(a) => self.stack.push(Value::Bool(!a)),
                        a => error!(self, ErrorKind::RuntimeTypeError(op.clone(), vec![a])),
                    }
                }

                Op::Jmp(line) => {
                    self.frame_mut().ip = line;
                    continue;
                }

                Op::JmpFalse(line) => {
                    if matches!(self.stack.pop(), Some(Value::Bool(false))) {
                        self.frame_mut().ip = line;
                        continue;
                    }
                }

                Op::Assert => {
                    if matches!(self.stack.pop(), Some(Value::Bool(false))) {
                        error!(self, ErrorKind::Assert);
                    }
                    self.stack.push(Value::Bool(true));
                }

                Op::ReadLocal(slot) => {
                    let slot = self.frame().stack_offset + slot;
                    self.stack.push(self.stack[slot].clone());
                }

                Op::Assign(slot) => {
                    let slot = self.frame().stack_offset + slot;
                    self.stack[slot] = self.stack.pop().unwrap();
                }

                Op::Call(num_args) => {
                    let new_base = self.stack.len() - 1 - num_args;
                    match &self.stack[new_base] {
                        Value::Function(args, _ret, block) => {
                            if args.len() != num_args {
                                error!(self,
                                       ErrorKind::InvalidProgram,
                                       format!("Invalid number of arguments, got {} expected {}.",
                                               num_args, args.len()));
                            }
                            if self.print_blocks {
                                block.debug_print();
                            }
                            self.frames.push(Frame {
                                stack_offset: new_base,
                                block: Rc::clone(&block),
                                ip: 0,
                            });
                            continue;
                        },
                        _ => {
                            unreachable!()
                        }
                    }
                }

                Op::Print => {
                    println!("PRINT: {:?}", self.stack.pop().unwrap());
                }

                Op::Return => {
                    let last = self.frames.pop().unwrap();
                    if self.frames.is_empty() {
                        return Ok(());
                    } else {
                        self.stack[last.stack_offset] = self.stack.pop().unwrap();
                    }
                }
            }
            self.frame_mut().ip += 1;
        }
    }
}
