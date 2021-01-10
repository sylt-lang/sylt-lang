use std::collections::HashMap;
use std::fmt;
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum Value {
    Float(f64),
    Int(i64),
    Bool(bool),
}

#[derive(Debug, Clone, Copy)]
pub enum Op {
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

    Equal,   // ==
    Less,    // <
    Greater, // >

    AssertEqual,

    Print,
    Return,
}

#[derive(Debug)]
pub struct Block {
    name: String,
    file: PathBuf,
    ops: Vec<Op>,
    last_line_offset: Option<usize>,
    line_offsets: HashMap<usize, usize>,
}

impl Block {
    pub fn new(name: &str, file: &Path) -> Self {
        Self {
            name: String::from(name),
            file: file.to_owned(),
            ops: Vec::new(),
            last_line_offset: None,
            line_offsets: HashMap::new(),
        }
    }

    pub fn add(&mut self, op: Op, token_position: Option<usize>) -> usize {
        let len = self.ops.len();
        if token_position != self.last_line_offset {
            if let Some(token_position) = token_position {
                self.line_offsets.insert(len, token_position);
            }
        }
        self.ops.push(op);
        len
    }

    pub fn add_from(&mut self, ops: &[Op], token_position: Option<usize>) -> usize {
        let len = self.ops.len();
        for op in ops {
            self.add(*op, token_position);
        }
        len
    }
}

#[derive(Debug)]
pub struct VM {
    stack: Vec<Value>,

    block: Block,
    ip: usize,
}

#[derive(Debug)]
pub enum VMErrorKind {
    TypeError(Op, Vec<Value>),
    AssertFailed(Value, Value),
}

#[derive(Debug)]
pub struct Error {
    kind: VMErrorKind,
    file: PathBuf,
    line: usize,
    message: Option<String>,
}

impl fmt::Display for VMErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VMErrorKind::TypeError(op, values) => {
                let values = values
                    .iter()
                    .fold(String::new(), |a, v| { format!("{}, {:?}", a, v) });
                write!(f, "Cannot apply {:?} to values {}", op, values)
            }
            VMErrorKind::AssertFailed(a, b) => {
                write!(f, "Assertion failed, {:?} != {:?}.", a, b)
            }
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match &self.message {
            Some(s) => format!("\n{}", s),
            None => String::from(""),
        };
        write!(f, "{:?}:{} [Runtime Error] {}{}", self.file, self.line, self.kind, message)
    }
}


pub fn run_block(block: Block) -> Result<(), Error> {
    let mut vm = VM {
        stack: Vec::new(),

        block,
        ip: 0,
    };

    vm.run()
}

macro_rules! error {
    ( $vm:expr, $kind:expr) => {
        return Err($vm.error($kind, None));
    };
    ( $vm:expr, $kind:expr, $msg:expr) => {
        return Err($vm.error($kind, Some($msg)));
    };
}

impl VM {
    fn pop_twice(&mut self) -> (Value, Value) {
        let (a, b) = (self.stack.pop().unwrap(), self.stack.pop().unwrap());
        (b, a)
    }

    fn _peek_up(&self, amount: usize) -> Option<&Value> {
        self.stack.get(self.stack.len() - amount)
    }

    fn error(&self, kind: VMErrorKind, message: Option<String>) -> Error {
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

            let op = self.block.ops[self.ip];
            match op {
                Op::Pop => {
                    self.stack.pop();
                }

                Op::Constant(value) => {
                    self.stack.push(value);
                }

                Op::Neg => {
                    match self.stack.pop().unwrap() {
                        Value::Float(a) => self.stack.push(Value::Float(-a)),
                        Value::Int(a) => self.stack.push(Value::Int(-a)),
                        a => error!(self, VMErrorKind::TypeError(op, vec![a])),
                    }
                }

                Op::Add => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(b + a)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(b + a)),
                        (a, b) => error!(self, VMErrorKind::TypeError(op, vec![a, b])),
                    }
                }

                Op::Sub => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(b - a)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(b - a)),
                        (a, b) => error!(self, VMErrorKind::TypeError(op, vec![a, b])),
                    }
                }

                Op::Mul => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(b * a)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(b * a)),
                        (a, b) => error!(self, VMErrorKind::TypeError(op, vec![a, b])),
                    }
                }

                Op::Div => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(b / a)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(b / a)),
                        (a, b) => error!(self, VMErrorKind::TypeError(op, vec![a, b])),
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
                        (a, b) => error!(self, VMErrorKind::TypeError(op, vec![a, b])),
                    }
                }

                Op::Or => {
                    match self.pop_twice() {
                        (Value::Bool(a), Value::Bool(b)) => self.stack.push(Value::Bool(a || b)),
                        (a, b) => error!(self, VMErrorKind::TypeError(op, vec![a, b])),
                    }
                }

                Op::Not => {
                    match self.stack.pop().unwrap() {
                        Value::Bool(a) => self.stack.push(Value::Bool(!a)),
                        a => error!(self, VMErrorKind::TypeError(op, vec![a])),
                    }
                }

                Op::AssertEqual => {
                    let (a, b) = self.pop_twice();
                    if a != b {
                        error!(self, VMErrorKind::AssertFailed(a, b));
                    }
                    self.stack.push(Value::Bool(a == b));
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
