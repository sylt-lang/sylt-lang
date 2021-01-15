use owo_colors::OwoColorize;
use std::collections::HashSet;
use std::fmt::Debug;
use std::path::PathBuf;
use std::rc::Rc;

use crate::compiler::Type;
use crate::error::{Error, ErrorKind};
use crate::vm::{Block, Op, Value};

macro_rules! error {
    ( $thing:expr, $kind:expr) => {
        return Err($thing.error($kind, None));
    };
    ( $thing:expr, $kind:expr, $msg:expr) => {
        return Err($thing.error($kind, Some(String::from($msg))));
    };
}

#[derive(Debug)]
struct Frame {
    stack_offset: usize,
    block: Rc<Block>,
    ip: usize,
}

#[derive(Debug)]
pub struct VM {
    checked: HashSet<(PathBuf, usize)>,

    stack: Vec<Type>,
    frames: Vec<Frame>,

    print_blocks: bool,
    print_ops: bool,
}

impl VM {
    pub fn new() -> Self {
        Self {
            checked: HashSet::new(),

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

    fn pop(&mut self) -> Type {
        let len = self.stack.len();
        let res = self.stack[len-1].clone();
        self.stack.truncate(len - 1);
        res
    }


    fn pop_twice(&mut self) -> (Type, Type) {
        let len = self.stack.len();
        let res = (self.stack[len - 2].clone(), self.stack[len - 1].clone());
        self.stack.truncate(len - 2);
        res
    }

    fn peek_up(&self, amount: usize) -> Type {
        self.stack[self.stack.len() - 1 - amount].clone()
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

    pub fn typecheck(&mut self, return_type: Type, block: Rc<Block>) -> Result<(), Error>{
        let id = block.id();
        if self.checked.contains(&id) {
            return Ok(());
        }
        self.checked.insert(id);

        self.frames.push(Frame {
            stack_offset: 0,
            block,
            ip: 0
        });

        let outer = self.stack.is_empty();

        if self.print_blocks {
            self.frame().block.debug_print();
        }

        loop {
            let ip = self.frame().ip;
            let op = self.frame().block.ops.get(ip);
            if op.is_none() {
                return Ok(());
            }
            let op = op.unwrap().clone();

            if self.print_ops {
                let start = self.frame().stack_offset;
                print!("    {:3} [", start);
                for (i, s) in self.stack.iter().skip(start).enumerate() {
                    if i != 0 {
                        print!(" ");
                    }
                    match s {
                        Type::Function(args, ret) => print!("Function({:?} -> {:?})", args.green(), ret.green()),
                        s => print!("{:?}", s.green()),
                    }
                }
                println!("]");

                println!("{:5} {:05} {:?}",
                         self.frame().block.line(self.frame().ip).red(),
                         self.frame().ip.blue(),
                         self.frame().block.ops[self.frame().ip]);
            }

            match op {
                Op::Illegal => {}

                Op::Unreachable => {}

                Op::Pop => {
                    self.stack.pop();
                }

                Op::Constant(value) => {
                    let ty = Type::from(&value);
                    if let Value::Function(args, ret, block) = value {
                        let mut stack = vec![ret.clone()];
                        stack.extend_from_slice(&args);

                        let mut sub = VM {
                            checked: self.checked.clone(),
                            stack,
                            frames: vec![],
                            print_blocks: self.print_blocks,
                            print_ops: self.print_ops,
                        };

                        sub.typecheck(ret.clone(), Rc::clone(&block))?;

                        self.checked = sub.checked;
                    }
                    self.stack.push(ty);
                }

                Op::Neg => {
                    match self.peek_up(0) {
                        Type::Float | Type::Int => {},
                        a => error!(self, ErrorKind::TypeError(op.clone(), vec![a.clone()])),
                    }
                }

                Op::Add => {
                    let (a, b) = self.pop_twice();
                    match (&a, &b) {
                        (Type::Float, Type::Float)
                            | (Type::Int, Type::Int)
                            | (Type::String, Type::String) => {
                            self.stack.push(a)
                        }
                        _ => error!(self, ErrorKind::TypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Sub | Op::Mul | Op::Div => {
                    let (a, b) = self.pop_twice();
                    match (&a, &b) {
                        (Type::Float, Type::Float)
                            | (Type::Int, Type::Int) => self.stack.push(a),
                        _ => error!(self, ErrorKind::TypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Equal | Op::Less | Op::Greater => {
                    match self.pop_twice() {
                        (a, b) if (&[&a, &b]).contains(&&Type::UnknownType) =>
                            error!(self, ErrorKind::TypeError(op.clone(), vec![a, b])),
                        (a, b) if a == b => self.stack.push(Type::Bool),
                        (a, b) => error!(self, ErrorKind::TypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::And | Op::Or => {
                    match self.pop_twice() {
                        (Type::Bool, Type::Bool) => self.stack.push(Type::Bool),
                        (a, b) => error!(self, ErrorKind::TypeError(op.clone(), vec![a, b])),
                    }
                }

                Op::Not => {
                    match self.pop() {
                        Type::Bool => { self.stack.push(Type::Bool); },
                        a => { error!(self, ErrorKind::TypeError(op.clone(), vec![a])) },
                    }
                }

                Op::Jmp(_line) => {
                }

                Op::JmpFalse(_line) => {
                    match self.pop() {
                        Type::Bool => {},
                        a => { error!(self, ErrorKind::TypeError(op.clone(), vec![a])) },
                    }
                }

                Op::Assert => {
                    match self.pop() {
                        Type::Bool => { self.stack.push(Type::Bool); },
                        a => { error!(self, ErrorKind::TypeError(op.clone(), vec![a])) },
                    }
                }

                Op::ReadLocal(slot) => {
                    let slot = self.frame().stack_offset + slot;
                    self.stack.push(self.stack[slot].clone());
                }

                Op::Assign(slot) => {
                    let slot = self.frame().stack_offset + slot;
                    let lhs = self.stack[slot].clone();
                    let rhs = self.pop();
                    match (&lhs, &rhs) {
                        (Type::UnknownType, rhs) => {
                            if rhs == &Type::UnknownType {
                                error!(self, ErrorKind::TypeError(op.clone(), vec![lhs, rhs.clone()]), "");
                            } else {
                                self.stack[slot] = rhs.clone();
                            }
                        }
                        (lhs, rhs) if lhs == rhs => {},
                        (lhs, rhs) => error!(self,
                                             ErrorKind::TypeError(
                                                 op.clone(),
                                                 vec![lhs.clone(), rhs.clone()]
                                             )),
                    }
                }

                Op::Define(ref ty) => {
                    let top_type = self.stack.last().unwrap();
                    match (ty, top_type) {
                        (Type::UnknownType, top_type)
                            if top_type != &Type::UnknownType => {}
                        (a, b) if a != b => {
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
                        Type::Function(args, ret) => {
                            if args.len() != num_args {
                                error!(self,
                                       ErrorKind::InvalidProgram,
                                       format!("Invalid number of arguments, got {} expected {}.",
                                               num_args, args.len()));
                            }

                            let stack_args = &self.stack[self.stack.len() - args.len()..];
                            if args != stack_args {
                                error!(self,
                                       ErrorKind::TypeError(op.clone(), vec![]),
                                       format!("Expected args of type {:?} but got {:?}.",
                                               args, stack_args));
                            }

                            self.stack[new_base] = *ret.clone();
                        },
                        _ => {
                            error!(self,
                                   ErrorKind::TypeError(op.clone(), vec![self.stack[new_base].clone()]),
                                   format!("Tried to call non-function {:?}", self.stack[new_base]));
                        }
                    }
                }

                Op::Print => {
                    self.pop();
                }

                Op::Return => {
                    if outer {
                        return Ok(());
                    }

                    let a = self.stack.pop().unwrap_or(Type::Void);
                    if a != return_type {
                        error!(self, ErrorKind::TypeError(op, vec![a, return_type.clone()]), "Not matching return type.");
                    }
                }
            }
            self.frame_mut().ip += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::test_string;
    use crate::error::ErrorKind;

    test_string!(uncallable_type, "
                 f := fn i: int {
                     i()
                 }
                 ",
                 [ErrorKind::TypeError(_, _)]);

    test_string!(wrong_params, "
                 f : fn -> int = fn a: int -> int {}
                 ",
                 [ErrorKind::TypeError(_, _)]);

    test_string!(wrong_ret, "
                 f : fn -> int = fn {}
                 ",
                 [ErrorKind::TypeError(_, _)]);
}
