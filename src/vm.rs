use owo_colors::OwoColorize;
use std::collections::HashMap;
use std::fmt::Debug;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::cell::RefCell;

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
    Function(Vec<Rc<RefCell<UpValue>>>, Rc<Block>),
    Unkown,
    Nil,
}

#[derive(Clone, Debug)]
pub struct UpValue {
    slot: usize,
    value: Value,
}

impl UpValue {

    fn new(value: usize) -> Self {
        Self {
            slot: value,
            value: Value::Nil,
        }
    }

    fn get(&self, stack: &[Value]) -> Value {
        if self.is_closed() {
            self.value.clone()
        } else {
            stack[self.slot].clone()
        }
    }

    fn set(&mut self, stack: &mut [Value], value: Value) {
        if self.is_closed() {
            self.value = value;
        } else {
            stack[self.slot] = value;
        }
    }


    fn is_closed(&self) -> bool {
        self.slot == 0
    }

    fn close(&mut self, value: Value) {
        self.slot = 0;
        self.value = value;
    }
}

impl Debug for Value {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Float(f) => write!(fmt, "(float {})", f),
            Value::Int(i) => write!(fmt, "(int {})", i),
            Value::Bool(b) => write!(fmt, "(bool {})", b),
            Value::String(s) => write!(fmt, "(string \"{}\")", s),
            Value::Function(_, block) => write!(fmt, "(fn {}: {:?})", block.name, block.ty),
            Value::Unkown => write!(fmt, "(unkown)"),
            Value::Nil => write!(fmt, "(nil)"),
        }
    }
}

impl Value {
    fn identity(self) -> Self {
        match self {
            Value::Float(_) => Value::Float(1.0),
            Value::Int(_) => Value::Int(1),
            Value::Bool(_) => Value::Bool(true),
            a => a,
        }
    }

    fn as_type(&self) -> Type {
        match self {
            Value::Float(_) => Type::Float,
            Value::Int(_) => Type::Int,
            Value::Bool(_) => Type::Bool,
            Value::String(_) => Type::String,
            Value::Function(_, block) => block.ty.clone(),
            Value::Unkown => Type::UnknownType,
            Value::Nil => Type::Void,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Op {
    Illegal,

    Pop,
    PopUpvalue,
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
    AssignLocal(usize),

    ReadUpvalue(usize),
    AssignUpvalue(usize),

    Define(Type),

    Call(usize),

    Print,
    Return,
}

#[derive(Debug)]
pub struct Block {
    pub ty: Type,
    pub ups: Vec<(usize, bool, Type)>,

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
            ty: Type::Void,
            ups: Vec::new(),
            name: String::from(name),
            file: file.to_owned(),
            ops: Vec::new(),
            last_line_offset: 0,
            line_offsets: HashMap::new(),
            line,
        }
    }

    pub fn from_type(ty: &Type) -> Self {
        let mut block = Block::new("/empty/", Path::new(""), 0);
        block.ty = ty.clone();
        block
    }

    pub fn args(&self) -> &Vec<Type> {
        if let Type::Function(ref args, _) = self.ty {
            args
        } else {
            unreachable!()
        }
    }

    pub fn ret(&self) -> &Type {
        if let Type::Function(_, ref ret) = self.ty {
            ret
        } else {
            unreachable!()
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
    upvalues: HashMap<usize, Rc<RefCell<UpValue>>>,

    stack: Vec<Value>,
    frames: Vec<Frame>,
    print_blocks: bool,
    print_ops: bool,
}

enum OpResult {
    Continue,
    Done,
}

impl VM {
    pub fn new() -> Self {
        Self {
            upvalues: HashMap::new(),
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

    fn find_upvalue(&mut self, slot: usize) -> &mut Rc<RefCell<UpValue>> {
        self.upvalues.entry(slot).or_insert(
            Rc::new(RefCell::new(UpValue::new(slot))))
    }

    fn pop(&mut self) -> Value {
        self.stack.pop().unwrap()
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

    fn op(&self) -> &Op {
        let ip = self.frame().ip;
        &self.frame().block.ops[ip]
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

    fn eval_op(&mut self, op: Op) -> Result<OpResult, Error> {
        match op {
            Op::Illegal => {
                error!(self, ErrorKind::InvalidProgram);
            }

            Op::Unreachable => {
                error!(self, ErrorKind::Unreachable);
            }

            Op::Pop => {
                self.stack.pop().unwrap();
            }

            Op::PopUpvalue => {
                self.stack.pop().unwrap();
            }

            Op::Constant(value) => {
                let offset = self.frame().stack_offset;
                let value = match value {
                    Value::Function(_, block) => {
                        let mut ups = Vec::new();
                        println!("UPS: {:?}", block.ups);
                        for (slot, is_up, _) in block.ups.iter() {
                            let up = if *is_up {
                                if let Value::Function(local_ups, _) = &self.stack[offset] {
                                    Rc::clone(&local_ups[*slot])
                                } else {
                                    unreachable!()
                                }
                            } else {
                                let slot = self.frame().stack_offset + slot;
                                Rc::clone(self.find_upvalue(slot))
                            };
                            ups.push(up);
                        }
                        Value::Function(ups, block)
                    },
                    _ => value.clone(),
                };
                self.stack.push(value);
            }

            Op::Neg => {
                match self.stack.pop().unwrap() {
                    Value::Float(a) => self.stack.push(Value::Float(-a)),
                    Value::Int(a) => self.stack.push(Value::Int(-a)),
                    a => error!(self, ErrorKind::RuntimeTypeError(op, vec![a])),
                }
            }

            Op::Add => {
                match self.pop_twice() {
                    (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(a + b)),
                    (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(a + b)),
                    (Value::String(a), Value::String(b)) => {
                        self.stack.push(Value::String(Rc::from(format!("{}{}", a, b))))
                    }
                    (a, b) => error!(self, ErrorKind::RuntimeTypeError(op, vec![a, b])),
                }
            }

            Op::Sub => {
                match self.pop_twice() {
                    (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(a - b)),
                    (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(a - b)),
                    (a, b) => error!(self, ErrorKind::RuntimeTypeError(op, vec![a, b])),
                }
            }

            Op::Mul => {
                match self.pop_twice() {
                    (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(a * b)),
                    (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(a * b)),
                    (a, b) => error!(self, ErrorKind::RuntimeTypeError(op, vec![a, b])),
                }
            }

            Op::Div => {
                match self.pop_twice() {
                    (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(a / b)),
                    (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(a / b)),
                    (a, b) => error!(self, ErrorKind::RuntimeTypeError(op, vec![a, b])),
                }
            }

            Op::Equal => {
                match self.pop_twice() {
                    (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Bool(a == b)),
                    (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Bool(a == b)),
                    (Value::String(a), Value::String(b)) => self.stack.push(Value::Bool(a == b)),
                    (Value::Bool(a), Value::Bool(b)) => self.stack.push(Value::Bool(a == b)),
                    (a, b) => error!(self, ErrorKind::RuntimeTypeError(op, vec![a, b])),
                }
            }

            Op::Less => {
                match self.pop_twice() {
                    (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Bool(a < b)),
                    (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Bool(a < b)),
                    (Value::String(a), Value::String(b)) => self.stack.push(Value::Bool(a < b)),
                    (Value::Bool(a), Value::Bool(b)) => self.stack.push(Value::Bool(a < b)),
                    (a, b) => error!(self, ErrorKind::RuntimeTypeError(op, vec![a, b])),
                }
            }

            Op::Greater => {
                match self.pop_twice() {
                    (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Bool(a > b)),
                    (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Bool(a > b)),
                    (Value::String(a), Value::String(b)) => self.stack.push(Value::Bool(a > b)),
                    (Value::Bool(a), Value::Bool(b)) => self.stack.push(Value::Bool(a > b)),
                    (a, b) => error!(self, ErrorKind::RuntimeTypeError(op, vec![a, b])),
                }
            }

            Op::And => {
                match self.pop_twice() {
                    (Value::Bool(a), Value::Bool(b)) => self.stack.push(Value::Bool(a && b)),
                    (a, b) => error!(self, ErrorKind::RuntimeTypeError(op, vec![a, b])),
                }
            }

            Op::Or => {
                match self.pop_twice() {
                    (Value::Bool(a), Value::Bool(b)) => self.stack.push(Value::Bool(a || b)),
                    (a, b) => error!(self, ErrorKind::RuntimeTypeError(op, vec![a, b])),
                }
            }

            Op::Not => {
                match self.stack.pop().unwrap() {
                    Value::Bool(a) => self.stack.push(Value::Bool(!a)),
                    a => error!(self, ErrorKind::RuntimeTypeError(op, vec![a])),
                }
            }

            Op::Jmp(line) => {
                self.frame_mut().ip = line;
                return Ok(OpResult::Continue);
            }

            Op::JmpFalse(line) => {
                if matches!(self.stack.pop(), Some(Value::Bool(false))) {
                    self.frame_mut().ip = line;
                    return Ok(OpResult::Continue);
                }
            }

            Op::Assert => {
                if matches!(self.stack.pop(), Some(Value::Bool(false))) {
                    error!(self, ErrorKind::Assert);
                }
                self.stack.push(Value::Bool(true));
            }

            Op::ReadUpvalue(slot) => {
                let offset = self.frame().stack_offset;
                let value = match &self.stack[offset] {
                    Value::Function(ups, _) => {
                        ups[slot].borrow().get(&self.stack)
                    }
                    _ => unreachable!(),
                };
                self.stack.push(value);
            }

            Op::AssignUpvalue(slot) => {
                let offset = self.frame().stack_offset;
                let value = self.stack.pop().unwrap();
                let slot = match &self.stack[offset] {
                    Value::Function(ups, _) => Rc::clone(&ups[slot]),
                    _ => unreachable!(),
                };
                slot.borrow_mut().set(&mut self.stack, value);
            }

            Op::ReadLocal(slot) => {
                let slot = self.frame().stack_offset + slot;
                self.stack.push(self.stack[slot].clone());
            }

            Op::AssignLocal(slot) => {
                let slot = self.frame().stack_offset + slot;
                self.stack[slot] = self.stack.pop().unwrap();
            }

            Op::Define(_) => {}

            Op::Call(num_args) => {
                let new_base = self.stack.len() - 1 - num_args;
                match &self.stack[new_base] {
                    Value::Function(_, block) => {
                        let args = block.args();
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
                        return Ok(OpResult::Continue);
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
                    return Ok(OpResult::Done);
                } else {
                    self.stack[last.stack_offset] = self.stack.pop().unwrap();
                    self.stack.truncate(last.stack_offset + 1);
                }
            }
        }
        self.frame_mut().ip += 1;
        Ok(OpResult::Continue)
    }

    pub fn print_stack(&self) {
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

    pub fn run(&mut self, block: Rc<Block>) -> Result<(), Error>{
        self.stack.clear();
        self.frames.clear();

        self.stack.push(Value::Function(Vec::new(), Rc::clone(&block)));

        self.frames.push(Frame {
            stack_offset: 0,
            block,
            ip: 0
        });

        if self.print_blocks {
            println!("\n    [[{}]]\n", "RUNNING".red());
            self.frame().block.debug_print();
        }

        loop {
            if self.print_ops {
                self.print_stack()
            }

            if matches!(self.eval_op(self.op().clone())?, OpResult::Done) {
                return Ok(());
            }
        }
    }

    fn check_op(&mut self, op: Op) -> Result<(), Error> {
        match op {
            Op::Unreachable => {}

            Op::Jmp(_line) => {}

            Op::Constant(value) => {
                self.stack.push(value.clone());
            }

            Op::ReadUpvalue(slot) => {
                self.stack.push(self.frame().block.ups[slot].2.as_value());
            }

            Op::AssignUpvalue(slot) => {
                let var = self.frame().block.ups[slot].2.clone();
                let up = self.stack.pop().unwrap().as_type();
                if var != up {
                    error!(self, ErrorKind::TypeError(op, vec![var, up]),
                                  "Incorrect type for upvalue.".to_string());
                }
            }

            Op::Return => {
                let a = self.stack.pop().unwrap();
                let ret = self.frame().block.ret();
                if a.as_type() != *ret {
                    error!(self, ErrorKind::TypeError(op, vec![a.as_type(),
                                                               ret.clone()]),
                                                      "Not matching return type.".to_string());
                }
            }

            Op::Print => {
                self.pop();
            }

            Op::Define(ref ty) => {
                let top_type = self.stack.last().unwrap().as_type();
                match (ty, top_type) {
                    (Type::UnknownType, top_type)
                        if top_type != Type::UnknownType => {}
                    (a, b) if a != &b => {
                        error!(self,
                            ErrorKind::TypeError(
                                op.clone(),
                                vec![a.clone(), b.clone()]),
                                format!("Tried to assign a type {:?} to type {:?}.", a, b)
                        );
                    }
                    _ => {}
                }
            }

            Op::Call(num_args) => {
                let new_base = self.stack.len() - 1 - num_args;
                match &self.stack[new_base] {
                    Value::Function(_, block) => {
                        let args = block.args();
                        if args.len() != num_args {
                            error!(self,
                                ErrorKind::InvalidProgram,
                                format!("Invalid number of arguments, got {} expected {}.",
                                    num_args, args.len()));
                        }

                        let stack_args = &self.stack[self.stack.len() - args.len()..];
                        let stack_args: Vec<_> = stack_args.iter().map(|x| x.as_type()).collect();
                        if args != &stack_args {
                            error!(self,
                                ErrorKind::TypeError(op.clone(), vec![]),
                                format!("Expected args of type {:?} but got {:?}.",
                                    args, stack_args));
                        }

                        self.stack[new_base] = block.ret().as_value();

                        self.stack.truncate(new_base + 1);
                    },
                    _ => {
                        error!(self,
                            ErrorKind::TypeError(op.clone(), vec![self.stack[new_base].as_type()]),
                            format!("Tried to call non-function {:?}", self.stack[new_base]));
                    }
                }
            }

            Op::JmpFalse(_) => {
                match self.pop() {
                    Value::Bool(_) => {},
                    a => { error!(self, ErrorKind::TypeError(op.clone(), vec![a.as_type()])) },
                }
            }
            _ => {
                self.eval_op(op)?;
                return Ok(())
            }
        }
        self.frame_mut().ip += 1;
        Ok(())
    }

    fn typecheck_block(&mut self, block: Rc<Block>) -> Vec<Error> {
        self.stack.clear();
        self.frames.clear();

        self.stack.push(Value::Function(Vec::new(), Rc::clone(&block)));
        for arg in block.args() {
            self.stack.push(arg.as_value());
        }

        self.frames.push(Frame {
            stack_offset: 0,
            block: block,
            ip: 0
        });

        if self.print_blocks {
            println!("\n    [[{}]]\n", "TYPECHECK".purple());
            self.frame().block.debug_print();
        }

        let mut errors = Vec::new();
        loop {
            let ip = self.frame().ip;
            if ip >= self.frame().block.ops.len() {
                break;
            }

            if self.print_ops {
                self.print_stack()
            }

            if let Err(e) = self.check_op(self.op().clone()) {
                errors.push(e);
                self.frame_mut().ip += 1;
            }

            if !self.stack.is_empty() {
                let ident = self.stack.pop().unwrap().identity();
                self.stack.push(ident);
            }
        }
        errors
    }

    pub fn typecheck(&mut self, blocks: &Vec<Rc<Block>>) -> Result<(), Vec<Error>> {
        let mut errors = Vec::new();

        for block in blocks.iter() {
            let ups: Vec<_> = block.ups.iter().map(|x| x.2.as_value()).collect();
            errors.append(&mut self.typecheck_block(Rc::clone(block)));
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

#[cfg(test)]
mod tests {
    mod typing {
        use crate::test_string;
        use crate::error::ErrorKind;

        test_string!(uncallable_type, "
                 f := fn i: int {
                     i()
                 }",
                 [ErrorKind::TypeError(_, _)]);

        test_string!(wrong_params, "
                 f : fn -> int = fn a: int -> int {}",
                 [ErrorKind::TypeError(_, _), ErrorKind::TypeError(_, _)]);

        test_string!(wrong_ret, "
                 f : fn -> int = fn {}",
                 [ErrorKind::TypeError(_, _)]);
    }
}
