use owo_colors::OwoColorize;
use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{hash_map::Entry, HashMap, HashSet};
use std::rc::Rc;
use sylt_common::error::{Error, RuntimeError, RuntimePhase};
use sylt_common::{
    Blob, Block, BlockLinkState, Frame, Machine, Op, OpResult, Prog, RuntimeContext, RustFunction,
    Type, UpValue, Value,
};

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
    upvalues: HashMap<usize, Rc<RefCell<UpValue>>>,

    stack: Vec<Value>,
    frames: Vec<Frame>,
    blocks: Vec<Rc<RefCell<Block>>>,
    blobs: Vec<Blob>,

    constants: Vec<Value>,
    strings: Vec<String>,

    pub print_bytecode: bool,
    pub print_exec: bool,

    extern_functions: Vec<RustFunction>,
}

impl VM {
    pub fn new() -> Self {
        Self {
            upvalues: HashMap::new(),

            stack: Vec::new(),
            frames: Vec::new(),
            blocks: Vec::new(),
            blobs: Vec::new(),

            constants: Vec::new(),
            strings: Vec::new(),

            print_bytecode: false,
            print_exec: false,

            extern_functions: Vec::new(),
        }
    }

    fn drop_upvalue(&mut self, slot: usize, value: Value) {
        if let Entry::Occupied(entry) = self.upvalues.entry(slot) {
            entry.get().borrow_mut().close(value);
            entry.remove();
        }
    }

    fn find_upvalue(&mut self, slot: usize) -> &mut Rc<RefCell<UpValue>> {
        self.upvalues
            .entry(slot)
            .or_insert_with(|| Rc::new(RefCell::new(UpValue::new(slot))))
    }

    fn push(&mut self, value: Value) {
        self.stack.push(value);
    }

    fn pop(&mut self) -> Value {
        match self.stack.pop() {
            Some(x) => x,
            None => self.crash_and_burn(),
        }
    }

    fn poppop(&mut self) -> (Value, Value) {
        let (a, b) = (
            self.stack.remove(self.stack.len() - 1),
            self.stack.remove(self.stack.len() - 1),
        );
        (b, a) // this matches the order they were on the stack
    }

    fn frame(&self) -> &Frame {
        self.frames.last().unwrap()
    }

    fn frame_mut(&mut self) -> &mut Frame {
        self.frames.last_mut().unwrap()
    }

    fn constant(&self, slot: usize) -> &Value {
        &self.constants[slot]
    }

    fn string(&self, slot: usize) -> &String {
        &self.strings[slot]
    }

    fn op(&self) -> Op {
        let ip = self.frame().ip;
        self.frame().block.borrow().ops[ip]
    }

    fn print_stacktrace(&self) {
        println!("\n<{}>", "STACK".red());
        for (i, frame) in self.frames.iter().enumerate() {
            println!(
                "  {:>3}. {}:{:<4} in {:10}",
                i,
                frame.block.borrow().file.display(),
                frame.block.borrow().line(self.frame().ip),
                frame.block.borrow().name.blue()
            );
        }
        println!()
    }

    /// Stop the program, violently
    fn crash_and_burn(&self) -> ! {
        self.print_stack();
        println!("\n");
        self.print_stacktrace();
        self.frame()
            .block
            .borrow()
            .debug_print(Some(&self.constants));
        println!(
            "    ip: {}, line: {}\n",
            self.frame().ip.blue(),
            self.frame().block.borrow().line(self.frame().ip).blue()
        );
        unreachable!();
    }

    fn error(&self, kind: RuntimeError, message: Option<String>) -> Error {
        let frame = self.frames.last().unwrap();
        self.print_stacktrace();
        Error::RuntimeError {
            kind,
            phase: RuntimePhase::Runtime,
            file: frame.block.borrow().file.clone(),
            line: frame.block.borrow().line(frame.ip),
            message,
        }
    }

    fn print_stack(&self) {
        let start = self.frame().stack_offset;
        print!("    {:3} [", start);
        for (i, s) in self.stack.iter().skip(start).enumerate() {
            if i != 0 {
                print!(" ");
            }
            print!("{:?}", s.green());
        }
        println!("]");

        println!(
            "{:5} {:05} {:?}",
            self.frame().block.borrow().line(self.frame().ip).blue(),
            self.frame().ip.red(),
            self.frame().block.borrow().ops[self.frame().ip]
        );
    }

    #[doc(hidden)]
    pub fn init(&mut self, prog: &Prog) {
        let block = Rc::clone(&prog.blocks[0]);
        self.constants = prog.constants.clone();
        self.strings = prog.strings.clone();
        self.blocks = prog.blocks.clone();
        self.blobs = prog.blobs.clone();

        self.extern_functions = prog.functions.clone();
        self.stack.clear();
        self.frames.clear();

        self.push(Value::Function(
            Rc::new(Vec::new()),
            Type::Function(Vec::new(), Box::new(Type::Void)),
            0,
        ));

        self.frames.push(Frame {
            stack_offset: 0,
            block,
            ip: 0,
            contains_upvalues: false,
        });
    }

    /// Simulates the program.
    pub fn run(&mut self) -> Result<OpResult, Error> {
        if self.print_bytecode {
            println!("\n    [[{}]]\n", "RUNNING".red());
            self.frame()
                .block
                .borrow()
                .debug_print(Some(&self.constants));
        }

        loop {
            #[cfg(debug_assertions)]
            if self.print_exec {
                self.print_stack()
            }

            let op = self.eval_op(self.op())?;
            if matches!(op, OpResult::Done | OpResult::Yield) {
                return Ok(op);
            }
        }
    }
}

impl Machine for VM {
    fn stack_from_base(&self, base: usize) -> Cow<[Value]> {
        Cow::Borrowed(&self.stack[base..])
    }

    fn blobs(&self) -> &[Blob] {
        &self.blobs
    }

    /// Calls `callable` with `args`. Continues to run until the call returns and then returns the
    /// returned value.
    fn eval_call(&mut self, callable: Value, args: &[&Value]) -> Result<Value, Error> {
        self.push(callable);
        let num_args = args.len();
        args.iter().for_each(|value| self.push(Value::clone(value)));
        // Since the Op::Call below isn't a compiled instruction, we need to store the current
        // instruction pointer and restore it when we return to this frame.
        let ip = self.frame().ip;
        self.eval_op(Op::Call(num_args))?;

        let cur_frame = self.frames.len();
        while self.frames.len() >= cur_frame {
            #[cfg(debug_assertions)]
            if self.print_exec {
                self.print_stack()
            }

            self.eval_op(self.op())?;
        }
        // Restore the instruction pointer.
        self.frame_mut().ip = ip;
        // Take the return value from the stack.
        Ok(self.pop())
    }

    /// Runs a single operation on the VM
    fn eval_op(&mut self, op: Op) -> Result<OpResult, Error> {
        match op {
            Op::Illegal => {
                error!(self, RuntimeError::InvalidProgram);
            }

            Op::Unreachable => {
                error!(self, RuntimeError::Unreachable);
            }

            Op::Pop => {
                self.pop();
            }

            Op::Tuple(size) => {
                let values = self.stack.split_off(self.stack.len() - size);
                self.stack.push(Value::Tuple(Rc::new(values)));
            }

            Op::List(size) => {
                let values = self.stack.split_off(self.stack.len() - size);
                self.stack.push(Value::List(Rc::new(RefCell::new(values))));
            }

            Op::Set(size) => {
                let values: HashSet<_> = self
                    .stack
                    .split_off(self.stack.len() - size)
                    .into_iter()
                    .collect();
                self.stack.push(Value::Set(Rc::new(RefCell::new(values))));
            }

            Op::Dict(size) => {
                assert!(size % 2 == 0);
                let values = self.stack.split_off(self.stack.len() - size);
                let values: HashMap<_, _> = values
                    .chunks_exact(2)
                    .map(|a| (a[0].clone(), a[1].clone()))
                    .collect();
                self.stack.push(Value::Dict(Rc::new(RefCell::new(values))));
            }

            Op::PopUpvalue => {
                let value = self.pop();
                let slot = self.stack.len();
                self.drop_upvalue(slot, value);
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

            Op::Yield => {
                self.frame_mut().ip += 1;
                return Ok(OpResult::Yield);
            }

            Op::Constant(value) => {
                let offset = self.frame().stack_offset;
                let constant = self.constant(value).clone();
                let value = match constant {
                    Value::Function(ups, ty, block) => {
                        let inner = Rc::clone(&self.blocks[block]);
                        if matches!(inner.borrow().linking, BlockLinkState::Linked) {
                            Value::Function(ups, ty, block)
                        } else {
                            let mut ups = Vec::new();
                            for (slot, is_up, _) in inner.borrow().upvalues.iter() {
                                self.frame_mut().contains_upvalues = true;
                                let up = if *is_up {
                                    if let Value::Function(local_ups, _, _) = &self.stack[offset] {
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
                            Value::Function(Rc::new(ups), ty, block)
                        }
                    }
                    value => value,
                };
                self.push(value);
            }

            Op::Link(slot) => {
                let offset = self.frame().stack_offset;
                let constant = self.constant(slot).clone();
                let constant = match constant {
                    Value::Function(_, ty, block) => {
                        let inner = Rc::clone(&self.blocks[block]);
                        let mut ups = Vec::new();
                        for (slot, is_up, _) in inner.borrow().upvalues.iter() {
                            let up = if *is_up {
                                if let Value::Function(local_ups, _, _) = &self.stack[offset] {
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
                        Value::Function(Rc::new(ups), ty, block)
                    }
                    value => error!(
                        self,
                        RuntimeError::ValueError(op, vec![value]),
                        "Not a function {:?}",
                        value
                    ),
                };
                self.constants[slot] = constant;
            }

            Op::GetIndex => {
                let slot = self.pop();
                let val = self.pop();
                match (val, slot) {
                    (Value::Tuple(v), Value::Int(slot)) => {
                        let slot = slot as usize;
                        if v.len() <= slot {
                            self.stack.push(Value::Nil);
                            let len = v.len();
                            error!(
                                self,
                                RuntimeError::IndexOutOfBounds(Value::Tuple(v), len, slot)
                            );
                        }
                        self.stack.push(v[slot].clone());
                    }
                    (Value::List(rc_v), Value::Int(slot)) => {
                        let slot = slot as usize;
                        let v = rc_v.borrow();
                        if v.len() <= slot {
                            self.stack.push(Value::Nil);
                            let len = v.len();
                            drop(v);
                            error!(
                                self,
                                RuntimeError::IndexOutOfBounds(Value::List(rc_v), len, slot)
                            );
                        }
                        self.stack.push(v[slot].clone());
                    }
                    (Value::Dict(dict), i) => {
                        self.push(
                            dict.as_ref()
                                .borrow()
                                .get(&i)
                                .cloned()
                                .unwrap_or(Value::Nil),
                        );
                    }
                    (val, slot) => {
                        self.stack.push(Value::Nil);
                        error!(self, RuntimeError::IndexError(val, slot.into()));
                    }
                }
            }

            Op::GetConstIndex(slot) => {
                let val = self.pop();
                match val {
                    Value::Tuple(v) => {
                        let slot = slot as usize;
                        if v.len() <= slot {
                            self.stack.push(Value::Nil);
                            let len = v.len();
                            error!(
                                self,
                                RuntimeError::IndexOutOfBounds(Value::Tuple(v), len, slot)
                            );
                        }
                        self.stack.push(v[slot].clone());
                    }
                    Value::List(rc_v) => {
                        let slot = slot as usize;
                        let v = rc_v.borrow();
                        if v.len() <= slot {
                            self.stack.push(Value::Nil);
                            let len = v.len();
                            drop(v);
                            error!(
                                self,
                                RuntimeError::IndexOutOfBounds(Value::List(rc_v), len, slot)
                            );
                        }
                        self.stack.push(v[slot].clone());
                    }
                    Value::Dict(dict) => {
                        self.push(
                            dict.as_ref()
                                .borrow()
                                .get(&Value::Int(slot))
                                .cloned()
                                .unwrap_or(Value::Nil),
                        );
                    }
                    val => {
                        self.stack.push(Value::Nil);
                        error!(self, RuntimeError::IndexError(val, Type::Int));
                    }
                }
            }

            Op::AssignIndex => {
                let value = self.pop();
                let slot = self.pop();
                let indexable = self.pop();
                match (indexable, slot, value) {
                    (Value::List(rc_v), Value::Int(slot), n) => {
                        let slot = slot as usize;
                        let v = rc_v.borrow();
                        if v.len() <= slot {
                            self.stack.push(Value::Nil);
                            let len = v.len();
                            drop(v);
                            error!(
                                self,
                                RuntimeError::IndexOutOfBounds(Value::List(rc_v), len, slot)
                            );
                        }
                        drop(v);
                        rc_v.borrow_mut()[slot] = n;
                    }
                    (Value::Dict(rc_v), slot, n) => {
                        rc_v.as_ref().borrow_mut().insert(slot, n);
                    }
                    (indexable, slot, _) => {
                        self.push(Value::Nil);
                        error!(self, RuntimeError::IndexError(indexable, slot.into()));
                    }
                }
            }

            Op::ReadGlobal(slot) => {
                if self.stack.len() > slot {
                    let global = self.stack[slot].clone();
                    self.push(global);
                } else {
                    error!(self, RuntimeError::InvalidProgram);
                }
            }

            Op::AssignGlobal(slot) => {
                self.stack[slot] = self.pop();
            }

            Op::Contains => {
                let (element, container) = self.poppop();
                match (container, element) {
                    (Value::List(rc_v), e) => {
                        self.push(Value::Bool(rc_v.as_ref().borrow_mut().contains(&e)));
                    }
                    (Value::Dict(rc_v), e) => {
                        self.push(Value::Bool(rc_v.as_ref().borrow_mut().contains_key(&e)));
                    }
                    (Value::Set(rc_v), e) => {
                        self.push(Value::Bool(rc_v.as_ref().borrow_mut().contains(&e)));
                    }
                    (indexable, e) => {
                        self.push(Value::Nil);
                        error!(self, RuntimeError::IndexError(indexable, e.into()));
                    }
                }
            }

            Op::GetField(field) => {
                let inst = self.pop();
                match inst {
                    Value::Instance(ty, values) => {
                        let ty = &self.blobs[ty];
                        let field = self.string(field);
                        match values.borrow().get(field) {
                            Some(value) => {
                                self.push(value.clone());
                            }
                            _ => {
                                let err = Err(self.error(
                                    RuntimeError::UnknownField(ty.name.clone(), field.clone()),
                                    None,
                                ));
                                self.push(Value::Nil);
                                return err;
                            }
                        };
                    }
                    inst => {
                        error!(
                            self,
                            RuntimeError::TypeError(Op::GetField(field), vec![Type::from(inst)])
                        );
                    }
                }
            }

            Op::AssignField(field) => {
                let (inst, value) = self.poppop();
                match inst {
                    Value::Instance(ty, values) => {
                        let ty = &self.blobs[ty];
                        let field = self.string(field).clone();
                        if !ty.fields.contains_key(&field) {
                            error!(self, RuntimeError::UnknownField(ty.name.to_string(), field));
                        }
                        (*values).borrow_mut().insert(field, value);
                    }
                    inst => {
                        error!(
                            self,
                            RuntimeError::TypeError(Op::AssignField(field), vec![Type::from(inst)])
                        );
                    }
                }
            }

            Op::Is => {
                let (a, b) = self.poppop();
                let a = match a {
                    Value::Ty(ty) => ty,
                    val => Type::from(val),
                };
                let b = match b {
                    Value::Ty(ty) => ty,
                    val => Type::from(val),
                };
                let result = a.fits(&b, &self.blobs).is_ok();
                self.push(Value::Bool(result));
            }

            // TODO(ed): These look the same as in typechecker.rs, since the macros and functions hide the
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

            Op::And => {
                two_op!(self, Op::And, op::and);
            }

            Op::Or => {
                two_op!(self, Op::Or, op::or);
            }

            Op::Not => {
                one_op!(self, Op::Not, op::not);
            }

            Op::Jmp(line) => {
                self.frame_mut().ip = line;
                return Ok(OpResult::Continue);
            }

            Op::JmpFalse(line) => {
                if matches!(self.pop(), Value::Bool(false)) {
                    self.frame_mut().ip = line;
                    return Ok(OpResult::Continue);
                }
            }

            Op::JmpNPop(line, to_pop) => {
                let hi = self.stack.len();
                let lo = hi - to_pop;
                for slot in lo..hi {
                    if self.upvalues.contains_key(&slot) {
                        let value = self.stack[slot].clone();
                        self.drop_upvalue(slot, value);
                    }
                }
                self.stack.truncate(lo);
                self.frame_mut().ip = line;
                return Ok(OpResult::Continue);
            }

            Op::Assert => {
                if matches!(self.pop(), Value::Bool(false)) {
                    error!(self, RuntimeError::AssertFailed);
                }
                self.push(Value::Bool(true));
            }

            Op::ReadUpvalue(slot) => {
                let offset = self.frame().stack_offset;
                let value = match &self.stack[offset] {
                    Value::Function(ups, _, _) => ups[slot].borrow().get(&self.stack),
                    _ => unreachable!(),
                };
                self.push(value);
            }

            Op::AssignUpvalue(slot) => {
                let offset = self.frame().stack_offset;
                let value = self.pop();
                let slot = match &self.stack[offset] {
                    Value::Function(ups, _, _) => Rc::clone(&ups[slot]),
                    _ => unreachable!(),
                };
                slot.borrow_mut().set(&mut self.stack, value);
            }

            Op::ReadLocal(slot) => {
                let slot = self.frame().stack_offset + slot;
                self.push(self.stack[slot].clone());
            }

            Op::AssignLocal(slot) => {
                let slot = self.frame().stack_offset + slot;
                self.stack[slot] = self.pop();
            }

            Op::Define(_) => {}

            Op::Force(_) => {}

            Op::Union => {}

            Op::Call(num_args) => {
                let new_base = self.stack.len() - 1 - num_args;
                match self.stack[new_base].clone() {
                    Value::Blob(blob_slot) => {
                        let blob = &self.blobs[blob_slot];
                        let mut values = self.stack[new_base + 1..]
                            .chunks_exact(2)
                            .map(|b| {
                                if let Value::Field(name) = &b[0] {
                                    (name.clone(), b[1].clone())
                                } else {
                                    panic!("Expected Field but got {:?} for field names", b[0]);
                                }
                            })
                            .collect::<HashMap<_, _>>();
                        self.stack.truncate(new_base);
                        for name in blob.fields.keys() {
                            values.entry(name.clone()).or_insert(Value::Nil);
                        }
                        values.insert("_id".to_string(), Value::Int(blob.id as i64));
                        values.insert(
                            "_name".to_string(),
                            Value::String(Rc::new(blob.name.clone())),
                        );
                        self.push(Value::Instance(blob_slot, Rc::new(RefCell::new(values))));
                    }
                    Value::Function(_, _, block) => {
                        let inner = self.blocks[block].borrow();
                        let args = inner.args();
                        if args.len() != num_args {
                            error!(self, RuntimeError::ArgumentCount(args.len(), num_args));
                        }

                        #[cfg(debug_assertions)]
                        if self.print_bytecode {
                            inner.debug_print(Some(&self.constants));
                        }
                        self.frames.push(Frame {
                            stack_offset: new_base,
                            block: Rc::clone(&self.blocks[block]),
                            ip: 0,
                            contains_upvalues: true,
                        });
                        return Ok(OpResult::Continue);
                    }
                    Value::ExternFunction(slot) => {
                        let extern_func = self.extern_functions[slot];
                        let ctx = RuntimeContext {
                            typecheck: false,
                            stack_base: new_base + 1,
                            machine: self,
                        };
                        let res = match extern_func(ctx) {
                            Ok(value) => value,
                            Err(ek) => error!(self, ek, "Failed in external function"),
                        };
                        self.stack.truncate(new_base);
                        self.push(res);
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }

            Op::Print => {
                println!("PRINT: {:?}", self.pop());
            }

            Op::Return => {
                let last = self.frames.pop().unwrap();
                if self.frames.is_empty() {
                    return Ok(OpResult::Done);
                } else {
                    self.stack[last.stack_offset] = self.pop();
                    if last.contains_upvalues {
                        for slot in last.stack_offset + 1..self.stack.len() {
                            if self.upvalues.contains_key(&slot) {
                                let value = self.stack[slot].clone();
                                self.drop_upvalue(slot, value);
                            }
                        }
                    }
                    self.stack.truncate(last.stack_offset + 1);
                }
            }
        }
        self.frame_mut().ip += 1;
        Ok(OpResult::Continue)
    }
}

///
/// Module with all the operators that can be applied
/// to values.
///
/// Broken out because they need to be recursive.
mod op {
    use super::Rc;
    use super::Value;
    use std::collections::HashSet;

    fn tuple_dist_op(a: &Rc<Vec<Value>>, n: &Value, f: fn(&Value, &Value) -> Value) -> Value {
        Value::Tuple(Rc::new(
                a.iter().map(|a| f(a, n)).collect()
        ))
    }

    fn tuple_bin_op(
        a: &Rc<Vec<Value>>,
        b: &Rc<Vec<Value>>,
        f: fn(&Value, &Value) -> Value,
    ) -> Value {
        Value::Tuple(Rc::new(
            a.iter().zip(b.iter()).map(|(a, b)| f(a, b)).collect(),
        ))
    }

    fn tuple_un_op(a: &Rc<Vec<Value>>, f: fn(&Value) -> Value) -> Value {
        Value::Tuple(Rc::new(a.iter().map(f).collect()))
    }

    fn union_un_op(a: &HashSet<Value>, f: fn(&Value) -> Value) -> Value {
        a.iter()
            .find_map(|x| {
                let x = f(x);
                if x.is_nil() {
                    None
                } else {
                    Some(x)
                }
            })
            .unwrap_or(Value::Nil)
    }

    fn union_bin_op(a: &HashSet<Value>, b: &Value, f: fn(&Value, &Value) -> Value) -> Value {
        a.iter()
            .find_map(|x| {
                let x = f(x, b);
                if x.is_nil() {
                    None
                } else {
                    Some(x)
                }
            })
            .unwrap_or(Value::Nil)
    }

    pub fn neg(value: &Value) -> Value {
        match value {
            Value::Float(a) => Value::Float(-*a),
            Value::Int(a) => Value::Int(-*a),
            Value::Tuple(a) => tuple_un_op(a, neg),
            Value::Union(v) => union_un_op(&v, neg),
            Value::Unknown => Value::Unknown,
            _ => Value::Nil,
        }
    }

    pub fn not(value: &Value) -> Value {
        match value {
            Value::Bool(a) => Value::Bool(!*a),
            Value::Tuple(a) => tuple_un_op(a, not),
            Value::Union(v) => union_un_op(&v, not),
            Value::Unknown => Value::Bool(true),
            _ => Value::Nil,
        }
    }

    pub fn add(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Float(a + b),
            (Value::Int(a), Value::Int(b)) => Value::Int(a + b),
            (Value::String(a), Value::String(b)) => Value::String(Rc::from(format!("{}{}", a, b))),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, add),
            (Value::Tuple(t), n) | (n, Value::Tuple(t)) => tuple_dist_op(t, n, add),
            (Value::Unknown, a) | (a, Value::Unknown) if !matches!(a, Value::Unknown) => add(a, a),
            (Value::Unknown, Value::Unknown) => Value::Unknown,
            (Value::Union(a), b) | (b, Value::Union(a)) => union_bin_op(&a, b, add),
            _ => Value::Nil,
        }
    }

    pub fn sub(a: &Value, b: &Value) -> Value {
        add(a, &neg(b))
    }

    pub fn mul(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Float(a * b),
            (Value::Int(a), Value::Int(b)) => Value::Int(a * b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, mul),
            (Value::Tuple(t), n) | (n, Value::Tuple(t)) => tuple_dist_op(t, n, mul),
            (Value::Unknown, a) | (a, Value::Unknown) if !matches!(a, Value::Unknown) => mul(a, a),
            (Value::Unknown, Value::Unknown) => Value::Unknown,
            (Value::Union(a), b) | (b, Value::Union(a)) => union_bin_op(&a, b, mul),
            _ => Value::Nil,
        }
    }

    pub fn div(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Float(a / b),
            (Value::Int(a), Value::Int(b)) => Value::Int(a / b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, div),
            (Value::Tuple(t), n) => tuple_dist_op(t, n, div),
            (Value::Unknown, a) | (a, Value::Unknown) if !matches!(a, Value::Unknown) => div(a, a),
            (Value::Unknown, Value::Unknown) => Value::Unknown,
            (Value::Union(a), b) | (b, Value::Union(a)) => union_bin_op(&a, b, div),
            _ => Value::Nil,
        }
    }

    pub fn eq(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Bool(a == b),
            (Value::Int(a), Value::Int(b)) => Value::Bool(a == b),
            (Value::String(a), Value::String(b)) => Value::Bool(a == b),
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(a == b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b.iter()) {
                    match eq(a, b) {
                        Value::Bool(true) => {}
                        Value::Bool(false) => {
                            return Value::Bool(false);
                        }
                        Value::Nil => {
                            return Value::Nil;
                        }
                        _ => unreachable!("Equality should only return bool or nil."),
                    }
                }
                Value::Bool(true)
            }
            (Value::Unknown, a) | (a, Value::Unknown) if !matches!(a, Value::Unknown) => eq(a, a),
            (Value::Unknown, Value::Unknown) => Value::Unknown,
            (Value::Union(a), b) | (b, Value::Union(a)) => union_bin_op(&a, b, eq),
            (Value::Nil, Value::Nil) => Value::Bool(true),
            (Value::List(a), Value::List(b)) => {
                let a = a.borrow();
                let b = b.borrow();
                if a.len() != b.len() {
                    return Value::Bool(false);
                }
                for (a, b) in a.iter().zip(b.iter()) {
                    match eq(a, b) {
                        Value::Bool(true) => {}
                        Value::Bool(false) => {
                            return Value::Bool(false);
                        }
                        Value::Nil => {
                            return Value::Nil;
                        }
                        _ => unreachable!("Equality should only return bool or nil."),
                    }
                }
                Value::Bool(true)
            }
            _ => Value::Nil,
        }
    }

    pub fn less(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Bool(a < b),
            (Value::Float(a), Value::Int(b)) => Value::Bool(*a < (*b as f64)),
            (Value::Int(a), Value::Float(b)) => Value::Bool((*a as f64) < *b),
            (Value::Int(a), Value::Int(b)) => Value::Bool(a < b),
            (Value::String(a), Value::String(b)) => Value::Bool(a < b),
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(a < b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => a
                .iter()
                .zip(b.iter())
                .find_map(|(a, b)| match less(a, b) {
                    Value::Bool(true) => None,
                    a => Some(a),
                })
                .unwrap_or(Value::Bool(true)),
            (Value::Unknown, a) | (a, Value::Unknown) if !matches!(a, Value::Unknown) => less(a, a),
            (Value::Unknown, Value::Unknown) => Value::Unknown,
            (Value::Union(a), b) | (b, Value::Union(a)) => union_bin_op(&a, b, less),
            _ => Value::Nil,
        }
    }

    pub fn greater(a: &Value, b: &Value) -> Value {
        less(b, a)
    }

    pub fn and(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(*a && *b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, and),
            (Value::Unknown, a) | (a, Value::Unknown) if !matches!(a, Value::Unknown) => and(a, a),
            (Value::Unknown, Value::Unknown) => Value::Unknown,
            (Value::Union(a), b) | (b, Value::Union(a)) => union_bin_op(&a, b, and),
            _ => Value::Nil,
        }
    }

    pub fn or(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(*a || *b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, or),
            (Value::Unknown, a) | (a, Value::Unknown) if !matches!(a, Value::Unknown) => or(a, a),
            (Value::Unknown, Value::Unknown) => Value::Unknown,
            (Value::Union(a), b) | (b, Value::Union(a)) => union_bin_op(&a, b, or),
            _ => Value::Nil,
        }
    }
}
