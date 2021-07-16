use owo_colors::OwoColorize;
use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use sylt_common::error::{Error, RuntimeError, RuntimePhase};
use sylt_common::{Blob, Block, BlockLinkState, Machine, Op, OpResult, Prog, RuntimeContext, RustFunction, Type, Value};

macro_rules! error {
    ( $thing:expr, $kind:expr) => {
        return Err($thing.error($kind, None));
    };
    ( $thing:expr, $kind:expr, $( $msg:expr ),*) => {
        {
            let msg = Some(format!($( $msg ),*).into());
            return Err($thing.error($kind, msg));
        }
    };
}

macro_rules! one_op {
    ( $self:expr, $op:expr, $fun:expr ) => {
        let a = $self.pop();
        let b = $fun(&a);
        if b.is_nil() {
            $self.push(b);
            error!($self, RuntimeError::TypeError($op, vec![a.into()]));
        }
        $self.push(b);
    };
}

macro_rules! two_op {
    ( $self:expr, $op:expr, $fun:expr ) => {
        let (a, b) = $self.poppop();
        let c = $fun(&a, &b);
        if c.is_nil() {
            $self.push(c);
            error!(
                $self,
                RuntimeError::TypeError($op, vec![a.into(), b.into()])
            );
        }
        $self.push(c);
    };
}

pub struct VM {
    ignore_error: bool,

    ip: usize,
    stack: Vec<Type>,
    upvalues: Vec<Type>,

    blobs: Vec<Blob>,
    constants: Vec<Value>,
    strings: Vec<String>,
    extern_functions: Vec<RustFunction>,

    global_types: Vec<Type>,
    cur_block: usize,
    blocks: Vec<Rc<RefCell<Block>>>,
}

// Checks the program for type errors.
pub fn typecheck(prog: &Prog, verbosity: u32) -> Result<(), Vec<Error>> {
    let (globals, mut errors) = typecheck_block(0, prog, Vec::new(), verbosity);
    for block_slot in 1..prog.blocks.len() {
        errors.append(&mut typecheck_block(block_slot, prog, globals.clone(), verbosity).1);
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn typecheck_block(
    block_slot: usize,
    prog: &Prog,
    global_types: Vec<Type>,
    verbosity: u32,
) -> (Vec<Type>, Vec<Error>) {
    let block = &prog.blocks[block_slot];
    let print_bytecode = verbosity > 0;
    let print_exec = verbosity > 0;
    if print_bytecode {
        println!(
            "\n    [[{} - {}]]\n",
            "TYPECHECKING".purple(),
            block.borrow().name
        );
        block.borrow().debug_print(Some(&prog.constants));
    }

    let mut vm = VM::new(block_slot, prog, global_types);
    let mut errors = Vec::new();
    let ops = (*block).borrow().ops.clone();
    for (ip, op) in ops.iter().enumerate() {
        vm.ip = ip;
        vm.ignore_error = false;

        #[cfg(debug_assertions)]
        if print_exec {
            vm.print_stack()
        }

        // Global operations in the outer scope are the same
        // as local operations. Since we assign to the stack.
        //
        // This makes the implementation a lot easier.
        let op = match (block_slot == 0, op) {
            (true, Op::ReadGlobal(slot)) => Op::ReadLocal(*slot),
            (true, Op::AssignGlobal(slot)) => Op::AssignLocal(*slot),
            _ => *op,
        };

        if let Err(e) = vm.eval_op(op) {
            if !vm.ignore_error {
                errors.push(e);
            }
        }
    }

    if print_bytecode {
        println!("\n    [[{} - {}]]\n", "DONE".purple(), block.borrow().name);
    }

    (vm.stack, errors)
}

impl VM {
    pub(crate) fn new(cur_block: usize, prog: &Prog, global_types: Vec<Type>) -> Self {
        let block = Rc::clone(&prog.blocks[cur_block]);
        let upvalues = block
            .borrow()
            .upvalues
            .iter()
            .map(|(_, _, ty)| ty)
            .cloned()
            .collect();
        let mut vm = Self {
            ignore_error: false,
            ip: 0,
            stack: Vec::new(),
            upvalues,
            blobs: prog.blobs.clone(),
            constants: prog.constants.clone(),
            strings: prog.strings.clone(),
            extern_functions: prog.functions.clone(),
            global_types,
            cur_block,
            blocks: prog.blocks.clone(),
        };

        vm.push(block.borrow().ty.clone());
        for arg in block.borrow().args() {
            vm.push(arg.clone());
        }

        vm
    }

    fn print_stack(&self) {
        print!("        [",);
        for (i, s) in self.stack.iter().enumerate() {
            if i != 0 {
                print!(" ");
            }
            print!("{:?}", s.green());
        }
        println!("]");

        println!(
            "{:5} {:05} {:?}",
            self.block().borrow().line(self.ip).blue(),
            self.ip.red(),
            self.block().borrow().ops[self.ip]
        );
    }

    fn push(&mut self, ty: Type) -> &Type {
        self.stack.push(ty);
        self.stack.last().unwrap()
    }

    fn pop(&mut self) -> Type {
        match self.stack.pop() {
            Some(Type::Invalid) => {
                self.ignore_error = true;
                Type::Invalid
            }
            Some(x) => x,
            None => self.crash_and_burn(),
        }
    }

    fn poppop(&mut self) -> (Type, Type) {
        let a = self.pop();
        let b = self.pop();
        (b, a) // this matches the order they were on the stack
    }

    fn block(&self) -> Rc<RefCell<Block>> {
        Rc::clone(&self.blocks[self.cur_block])
    }

    fn error(&self, kind: RuntimeError, message: Option<String>) -> Error {
        Error::RuntimeError {
            kind,
            phase: RuntimePhase::Typecheck,
            file: self.block().borrow().file.clone(),
            line: self.block().borrow().line(self.ip),
            message,
        }
    }

    /// Stop the program, violently
    fn crash_and_burn(&self) -> ! {
        println!("Typecheck failed for {}", self.block().borrow().name);
        self.print_stack();
        unreachable!();
    }

    fn call_callable(&mut self, callable: Type, new_base: usize) -> Result<Type, RuntimeError> {
        let args = self.stack[new_base + 1..].to_vec();
        match callable {
            Type::Blob(blob_slot) => {
                let blob = &self.blobs[blob_slot];
                let values = self.stack[new_base + 1..]
                    .chunks_exact(2)
                    .map(|b| {
                        if let Type::Field(f) = &b[0] {
                            (f.clone(), b[1].clone())
                        } else {
                            unreachable!("Got {:?}, expected field", b[0]);
                        }
                    })
                    .collect::<HashMap<String, Type>>();

                for (field, ty) in values.iter() {
                    match blob.fields.get(field) {
                        Some(given_ty) => {
                            if let Err(msg) = given_ty.fits(ty, &self.blobs) {
                                return Err(RuntimeError::FieldTypeMismatch(
                                    blob.name.clone(),
                                    field.clone(),
                                    given_ty.clone(),
                                    ty.clone(),
                                    msg,
                                ));
                            }
                        }
                        None => {
                            return Err(RuntimeError::UnknownField(
                                blob.name.clone(),
                                field.clone(),
                            ));
                        }
                    }
                }

                for (field, ty) in blob.fields.iter() {
                    match (values.get(field), ty) {
                        (Some(t), ty) => {
                            if let Err(msg) = ty.fits(t, &self.blobs) {
                                return Err(RuntimeError::FieldTypeMismatch(
                                    blob.name.clone(),
                                    field.clone(),
                                    ty.clone(),
                                    t.clone(),
                                    msg,
                                ));
                            }
                        }
                        (None, ty) => {
                            if let Err(msg) = ty.fits(&Type::Void, &self.blobs) {
                                return Err(RuntimeError::FieldTypeMismatch(
                                    blob.name.clone(),
                                    field.clone(),
                                    ty.clone(),
                                    Type::Void,
                                    msg,
                                ));
                            }
                        }
                    }
                }

                Ok(Type::Instance(blob_slot))
            }

            Type::Function(fargs, fret) => {
                for (a, b) in fargs.iter().zip(args.iter()) {
                    if let Err(msg) = a.fits(b, &self.blobs) {
                        return Err(RuntimeError::ArgumentType(
                            fargs.clone(),
                            args,
                            msg,
                        ));
                    }
                }
                Ok((*fret).clone())
            }

            Type::ExternFunction(slot) => {
                let extern_func = self.extern_functions[slot];
                let ctx = RuntimeContext {
                    typecheck: true,
                    stack_base: new_base + 1,
                    machine: self,
                };
                extern_func(ctx).map(|r| r.into())
            }

            Type::Unknown => Ok(Type::Unknown),

            _ => Err(RuntimeError::InvalidProgram),
        }
    }
}

impl Machine for VM {
    fn stack_from_base(&self, base: usize) -> Cow<[Value]> {
        Cow::Owned(self.stack[base..].iter().map(Value::from).collect::<Vec<_>>())
    }

    fn blobs(&self) -> &[Blob] {
        &self.blobs
    }

    fn eval_call(&mut self, callable: Value, args: &[&Value]) -> Result<Value, Error> {
        self.push(Type::from(callable));
        let num_args = args.len();
        args.iter().for_each(|value| {
            self.push(Type::from(*value));
        });
        self.eval_op(Op::Call(num_args))?;
        // Take the return value from the stack.
        Ok(Value::from(self.pop()))
    }

    /// Checks the current operation for type errors.
    fn eval_op(&mut self, op: Op) -> Result<OpResult, Error> {
        match op {
            Op::Illegal => {}
            Op::Unreachable => {}
            Op::Jmp(_line) => {}
            Op::Yield => {}

            Op::Pop => {
                self.pop();
            }
            Op::Copy(n) => {
                let end = Vec::from(&self.stack[self.stack.len() - n..]);
                self.stack.extend(end);
            }

            Op::Swap => {
                let (a, b) = self.poppop();
                self.push(b);
                self.push(a);
            }

            Op::ReadLocal(n) => {
                let ty = self.stack[n].clone();
                if matches!(ty, Type::Unknown) {
                    self.push(Type::Invalid);
                    error!(
                        self,
                        RuntimeError::InvalidProgram,
                        "Read from an uninitalized value"
                    );
                } else {
                    self.push(ty);
                }
            }

            Op::AssignLocal(slot) => {
                let current = self.stack[slot].clone();
                let given = self.pop();
                if let Err(msg) = current.fits(&given, &self.blobs) {
                    error!(
                        self,
                        RuntimeError::TypeMismatch(current, given),
                        "Failed to assign. {}",
                        msg
                    );
                }

                if matches!(current, Type::Unknown) {
                    self.stack[slot] = given;
                }
            }

            Op::ReadGlobal(slot) => match self.global_types.get(slot).cloned() {
                Some(Type::Unknown) | Some(Type::Invalid) => {
                    self.push(Type::Invalid);
                    error!(
                        self,
                        RuntimeError::InvalidProgram,
                        "Read from an uninitalized global"
                    );
                }
                Some(ty) => { self.push(ty); },
                _ => { self.push(Type::Unknown); },
            },

            Op::AssignGlobal(slot) => {
                let current = self.global_types[slot].clone();
                let given = self.pop();
                if let Err(msg) = current.fits(&given, &self.blobs) {
                    error!(
                        self,
                        RuntimeError::TypeMismatch(current, given),
                        "Failed to assign. {}",
                        msg
                    );
                }
            }

            Op::Constant(slot) => {
                let ty = Type::from(&self.constants[slot]);
                self.push(ty);
                let value = &self.constants[slot];

                while let Value::Function(_, _, block) = value {
                    let block = Rc::clone(&self.blocks[*block]);
                    match block.borrow().linking {
                        BlockLinkState::Linked => break,
                        BlockLinkState::Nothing => {}
                    }

                    let mut types = Vec::new();
                    for (slot, is_up, ty) in block.borrow().upvalues.iter() {
                        if *is_up {
                            types.push(ty.clone());
                        } else {
                            types.push((&self.stack[*slot]).clone());
                        }
                    }

                    let mut block_mut = block.borrow_mut();
                    for (i, (_, is_up, ty)) in block_mut.upvalues.iter_mut().enumerate() {
                        if *is_up {
                            continue;
                        }

                        let suggestion = &types[i];
                        if matches!(ty, Type::Unknown) {
                            *ty = suggestion.clone();
                        } else if ty != suggestion {
                            error!(
                                self,
                                RuntimeError::CannotInfer(ty.clone(), suggestion.clone())
                            );
                        }
                    }
                    break;
                }
            }

            Op::AssignField(field) => {
                let (inst, expect) = self.poppop();
                match inst {
                    Type::Instance(ty) => {
                        let field = &self.strings[field];
                        let ty = &self.blobs[ty];
                        match ty.fields.get(field) {
                            Some(ty) => {
                                if ty != &expect {
                                    error!(
                                        self,
                                        RuntimeError::TypeMismatch(expect, ty.clone()),
                                        "Types of field and variable do not match"
                                    );
                                }
                            }
                            _ => {
                                error!(
                                    self,
                                    RuntimeError::UnknownField(ty.name.clone(), field.clone())
                                );
                            }
                        };
                    }
                    inst => {
                        error!(
                            self,
                            RuntimeError::TypeError(Op::AssignField(field), vec![Type::from(inst)])
                        );
                    }
                }
            }

            Op::GetField(field) => match self.pop() {
                Type::Instance(ty) => match &*self.strings[field] {
                    "_id" => {
                        self.push(Type::Int);
                    }
                    "_name" => {
                        self.push(Type::String);
                    }
                    field => {
                        let ty = &self.blobs[ty];
                        match ty.fields.get(field).cloned() {
                            Some(ty) => {
                                self.push(ty);
                            }
                            _ => {
                                let name = ty.name.clone();
                                let field = field.to_string();
                                self.push(Type::Invalid);
                                error!(
                                    self,
                                    RuntimeError::UnknownField(name, field)
                                );
                            }
                        }
                    }
                },
                inst => {
                    error!(
                        self,
                        RuntimeError::TypeError(Op::GetField(field), vec![Type::from(inst)])
                    );
                }
            },

            Op::PopUpvalue => {
                self.pop();
            }

            Op::ReadUpvalue(slot) => {
                let ty = self.upvalues.get(slot).unwrap().clone();
                self.push(ty);
            }

            Op::AssignUpvalue(slot) => {
                let current = self.upvalues.get(slot).unwrap().clone();
                let up = self.pop();
                if let Err(msg) = current.fits(&up, &self.blobs) {
                    error!(
                        self,
                        RuntimeError::TypeMismatch(up, current),
                        "Captured varibles type doesn't match upvalue type. {}",
                        msg
                    );
                }
                if matches!(current, Type::Unknown) {
                    self.upvalues[slot] = up;
                }
            }

            Op::Return => {
                let to_ret = self.pop();
                let ret = self.block().borrow().ret().clone();
                if to_ret != ret {
                    error!(
                        self,
                        RuntimeError::TypeMismatch(ret, to_ret),
                        "Value does not match return type"
                    );
                }
            }

            Op::Print => {
                self.pop();
            }

            Op::Define(ty) => {
                let ty = if let Value::Ty(ty) = &self.constants[ty] {
                    ty.clone()
                } else {
                    unreachable!("Cannot define variable to non-type");
                };
                let top_type = self.pop();
                self.push(top_type.clone());
                match (ty, top_type) {
                    (Type::Unknown, top_type) if top_type != Type::Unknown => {}
                    (a, b) => {
                        if let Err(msg) = a.fits(&b, &self.blobs) {
                            error!(
                                self,
                                RuntimeError::TypeMismatch(a.clone(), b),
                                "Cannot define mismatching types. {}",
                                msg
                            );
                        } else {
                            let last = self.stack.len() - 1;
                            self.stack[last] = a;
                        }
                    }
                }
            }

            Op::Force(ty) => {
                let old = self.pop();
                match &self.constants[ty] {
                    Value::Ty(Type::Unknown) => {
                        self.push(old);
                    }
                    Value::Ty(ty) => {
                        let ty = ty.clone();
                        self.push(ty);
                    }
                    _ => {
                        error!(self, RuntimeError::InvalidProgram, "Can only force types");
                    }
                }
            }

            Op::Union => {
                let (a, b) = self.poppop();
                self.push(Type::maybe_union([a, b].iter(), self.blobs.as_slice()));
            }

            Op::Link(slot) => {
                match &self.constants[slot] {
                    Value::Function(_, _, block) => {
                        self.block().borrow_mut().linking = BlockLinkState::Linked;

                        let mut types = Vec::new();
                        for (slot, is_up, ty) in self.blocks[*block].borrow().upvalues.iter() {
                            if *is_up {
                                types.push(ty.clone());
                            } else {
                                types.push(self.stack[*slot].clone());
                            }
                        }

                        let mut block_mut = self.blocks[*block].borrow_mut();
                        for (i, (_, is_up, ty)) in block_mut.upvalues.iter_mut().enumerate() {
                            if *is_up {
                                continue;
                            }

                            let suggestion = &types[i];
                            if matches!(ty, Type::Unknown) {
                                *ty = suggestion.clone();
                            } else if ty != suggestion {
                                error!(
                                    self,
                                    RuntimeError::CannotInfer(ty.clone(), suggestion.clone())
                                );
                            }
                        }
                    }

                    value => {
                        error!(
                            self,
                            RuntimeError::TypeError(op, vec![]),
                            "Cannot link non-function {:?}",
                            value
                        );
                    }
                };
            }

            Op::GetIndex => match self.poppop() {
                (Type::List(a), b) if b.fits(&Type::Int, &self.blobs).is_ok() => {
                    self.push((*a).clone());
                }
                (Type::Tuple(a), b) if b.fits(&Type::Int, &self.blobs).is_ok() => {
                    self.push(Type::Union(a.iter().cloned().collect()));
                }
                (Type::Dict(k, v), i) if k.fits(&i, &self.blobs).is_ok() => {
                    self.push((*v).clone());
                }
                (a, b) => {
                    self.push(Type::Invalid);
                    error!(
                        self,
                        RuntimeError::TypeError(op, vec![]),
                        "Failed to index '{:?}' with '{:?}'",
                        a,
                        b
                    );
                }
            },

            Op::GetConstIndex(slot) => match self.pop() {
                Type::List(a) => {
                    self.push((*a).clone());
                }
                Type::Tuple(a) => {
                    self.push(a.get(slot as usize).cloned().unwrap_or(Type::Void));
                }
                Type::Dict(k, v) if k.fits(&Type::Int, &self.blobs).is_ok() => {
                    self.push((*v).clone());
                }
                a => {
                    self.push(Type::Invalid);
                    error!(
                        self,
                        RuntimeError::TypeError(op, vec![]),
                        "Failed to index '{:?}' with '{:?}'",
                        a,
                        Type::Int
                    );
                }
            },

            Op::AssignIndex => {
                let value = self.pop();
                let slot = self.pop();
                let indexable = self.pop();
                match (indexable, slot, value) {
                    (Type::List(v), Type::Int, n) => match (v.as_ref(), &n) {
                        (Type::Unknown, top_type) if top_type != &Type::Unknown => {}
                        (a, b) => {
                            if let Err(msg) = a.fits(b, &self.blobs) {
                                error!(
                                    self,
                                    RuntimeError::TypeMismatch(a.clone(), b.clone()),
                                    "Cannot assign mismatching types. {}",
                                    msg
                                );
                            }
                        }
                    },
                    (Type::Dict(k, v), i, n) => {
                        if let Err(msg) = k.fits(&i, &self.blobs) {
                            error!(
                                self,
                                RuntimeError::TypeMismatch(*k.clone(), i.clone()),
                                "Cannot index with missmatching types. {}",
                                msg
                            );
                        }

                        if let Err(msg) = v.fits(&n, &self.blobs) {
                            error!(
                                self,
                                RuntimeError::TypeMismatch(*v.clone(), n.clone()),
                                "Cannot assign with missmatching types. {}",
                                msg
                            );
                        }
                    }
                    (indexable, slot, _) => {
                        self.stack.push(Type::Void);
                        error!(
                            self,
                            RuntimeError::TypeError(Op::AssignIndex, vec![indexable, slot])
                        );
                    }
                }
            }

            Op::Contains => {
                let (element, container) = self.poppop();
                match (Type::from(container), Type::from(element)) {
                    (Type::List(v), e) | (Type::Set(v), e) | (Type::Dict(v, _), e) => {
                        self.push(Type::Bool);
                        if let Err(msg) = v.fits(&e, &self.blobs) {
                            error!(
                                self,
                                RuntimeError::TypeMismatch(v.as_ref().clone(), e),
                                "Container does not contain the type. {}",
                                msg
                            );
                        }
                    }
                    (indexable, e) => {
                        self.push(Type::Invalid);
                        error!(self, RuntimeError::IndexError(indexable.into(), e.into()));
                    }
                }
            }

            Op::Call(num_args) => {
                let new_base = self.stack.len() - 1 - num_args;
                let callable = &self.stack[new_base];

                let mut err = None;
                self.stack[new_base] = match callable {
                    Type::Union(alts) => {
                        let mut returns = HashSet::new();
                        for alt in alts.clone().into_iter() {
                            if let Ok(res) = self.call_callable(alt, new_base) {
                                returns.insert(Type::from(res));
                            }
                        }
                        if returns.is_empty() {
                            err = Some(RuntimeError::InvalidProgram);
                            Type::Void
                        } else {
                            Type::Union(returns)
                        }
                    }
                    _ => {
                        let callable = callable.clone();
                        match self.call_callable(callable, new_base) {
                            Err(e) => {
                                err = Some(e);
                                Type::Void
                            }
                            Ok(v) => Type::from(v),
                        }
                    },
                };

                self.ignore_error |= self.stack[new_base + 1..]
                    .iter()
                    .any(|x| matches!(x, Type::Invalid));
                self.stack.truncate(new_base + 1);
                if let Some(err) = err {
                    error!(self, err, "Failed to call");
                }
            }

            Op::JmpFalse(_) => match self.pop() {
                Type::Bool => {}
                a => {
                    error!(self, RuntimeError::TypeError(op, vec![a.into()]))
                }
            },

            Op::JmpNPop(_, _) => {}

            Op::Tuple(n) => {
                let n = self.stack.len() - n;
                let end = self.stack.split_off(n);
                self.push(Type::Tuple(end));
            }

            Op::List(n) => {
                let n = self.stack.len() - n;
                let ty = Type::maybe_union(self.stack.split_off(n).iter(), self.blobs.as_slice());
                self.push(Type::List(Box::new(ty)));
            }

            Op::Set(n) => {
                let n = self.stack.len() - n;
                let ty = Type::maybe_union(self.stack.split_off(n).iter(), self.blobs.as_slice());
                self.push(Type::Set(Box::new(ty)));
            }

            Op::Dict(n) => {
                let n = self.stack.len() - n;
                let elems = self.stack.split_off(n);
                let key = Type::maybe_union(elems.iter().step_by(2), self.blobs.as_slice());
                let value = Type::maybe_union(elems.iter().skip(1).step_by(2), self.blobs.as_slice());
                self.push(Type::Dict(Box::new(key), Box::new(value)));
            }

            // TODO(ed): These look the same as in vm.rs, since the macros and functions hide the
            // rest, maybe merge them?
            Op::Neg => {
                one_op!(self, Op::Neg, op::neg);
            }

            Op::Add => {
                two_op!(self, Op::Add, op::add);
            }

            Op::Sub => {
                two_op!(self, Op::Sub, op::sub);
            }

            Op::Mul => {
                two_op!(self, Op::Mul, op::mul);
            }

            Op::Div => {
                two_op!(self, Op::Div, op::div);
            }

            Op::Equal => {
                two_op!(self, Op::Equal, op::eq);
            }

            Op::Less => {
                two_op!(self, Op::Less, op::less);
            }

            Op::Greater => {
                two_op!(self, Op::Greater, op::greater);
            }

            Op::Is => {
                self.poppop();
                self.push(Type::Bool);
            }

            Op::And => {
                two_op!(self, Op::And, op::and);
            }

            Op::Or => {
                two_op!(self, Op::Or, op::or);
            }

            Op::Not => {
                one_op!(self, Op::Not, op::not);
            }

            Op::Assert => {
                let ty = self.pop();
                self.push(ty.clone());
                if !matches!(ty, Type::Bool) {
                    error!(
                        self,
                        RuntimeError::TypeMismatch(Type::Bool, ty),
                        "Can only assert on bools"
                    );
                }
            }
        }
        Ok(OpResult::Done)
    }
}

///
/// Module with all the operators that can be applied
/// to values.
///
/// Broken out because they need to be recursive.
mod op {
    use super::Type;
    use std::collections::HashSet;

    fn tuple_dist_op(a: &Vec<Type>, n: &Type, f: fn(&Type, &Type) -> Type) -> Type {
        Type::Tuple(a.iter().map(|a| f(a, n)).collect())
    }

    fn tuple_bin_op(a: &Vec<Type>, b: &Vec<Type>, f: fn(&Type, &Type) -> Type) -> Type {
        Type::Tuple(a.iter().zip(b.iter()).map(|(a, b)| f(a, b)).collect())
    }

    fn tuple_un_op(a: &Vec<Type>, f: fn(&Type) -> Type) -> Type {
        Type::Tuple(a.iter().map(f).collect())
    }

    fn union_un_op(a: &HashSet<Type>, f: fn(&Type) -> Type) -> Type {
        a.iter()
            .find_map(|x| {
                let x = f(x);
                if x.is_nil() {
                    None
                } else {
                    Some(x)
                }
            })
            .unwrap_or(Type::Invalid)
    }

    fn union_bin_op(a: &HashSet<Type>, b: &Type, f: fn(&Type, &Type) -> Type) -> Type {
        a.iter()
            .find_map(|x| {
                let x = f(x, b);
                if x.is_nil() {
                    None
                } else {
                    Some(x)
                }
            })
            .unwrap_or(Type::Invalid)
    }

    pub fn neg(value: &Type) -> Type {
        match value {
            Type::Float => Type::Float,
            Type::Int => Type::Int,
            Type::Tuple(a) => tuple_un_op(a, neg),
            Type::Union(v) => union_un_op(&v, neg),
            Type::Unknown => Type::Unknown,
            _ => Type::Invalid,
        }
    }

    pub fn not(value: &Type) -> Type {
        match value {
            Type::Bool => Type::Bool,
            Type::Tuple(a) => tuple_un_op(a, not),
            Type::Union(v) => union_un_op(&v, not),
            Type::Unknown => Type::Bool,
            _ => Type::Invalid,
        }
    }

    pub fn add(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Float, Type::Float) => Type::Float,
            (Type::Int, Type::Int) => Type::Int,
            (Type::String, Type::String) => Type::String,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, add),
            (Type::Tuple(t), n) | (n, Type::Tuple(t)) => tuple_dist_op(t, n, add),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => add(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, add),
            _ => Type::Invalid,
        }
    }

    pub fn sub(a: &Type, b: &Type) -> Type {
        add(a, &neg(b))
    }

    pub fn mul(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Float, Type::Float) => Type::Float,
            (Type::Int, Type::Int) => Type::Int,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, mul),
            (Type::Tuple(t), n) | (n, Type::Tuple(t)) => tuple_dist_op(t, n, mul),

            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => mul(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, mul),
            _ => Type::Invalid,
        }
    }

    pub fn div(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Float, Type::Float) => Type::Float,
            (Type::Int, Type::Int) => Type::Int,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, div),
            (Type::Tuple(t), n) => tuple_dist_op(t, n, div),

            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => div(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, div),
            _ => Type::Invalid,
        }
    }

    pub fn eq(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Float, Type::Float) => Type::Bool,
            (Type::Int, Type::Int) => Type::Bool,
            (Type::String, Type::String) => Type::Bool,
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => a
                .iter()
                .zip(b.iter())
                .find_map(|(a, b)| match less(a, b) {
                    Type::Bool => None,
                    a => Some(a),
                })
                .unwrap_or(Type::Bool),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => eq(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, eq),
            (Type::Void, Type::Void) => Type::Bool,
            (Type::List(a), Type::List(b)) => eq(a, b),
            _ => Type::Invalid,
        }
    }

    pub fn less(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Float, Type::Float)
            | (Type::Int, Type::Int)
            | (Type::Float, Type::Int)
            | (Type::Int, Type::Float) => Type::Bool,
            (Type::String, Type::String) => Type::Bool,
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => a
                .iter()
                .zip(b.iter())
                .find_map(|(a, b)| match less(a, b) {
                    Type::Bool => None,
                    a => Some(a),
                })
                .unwrap_or(Type::Bool),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => less(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, less),
            _ => Type::Invalid,
        }
    }

    pub fn greater(a: &Type, b: &Type) -> Type {
        less(b, a)
    }

    pub fn and(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, and),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => and(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, and),
            _ => Type::Invalid,
        }
    }

    pub fn or(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, or),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => or(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, or),
            _ => Type::Invalid,
        }
    }
}
