use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt::Debug;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::hash::{Hash, Hasher};

use owo_colors::OwoColorize;

use error::Error;
use tokenizer::TokenStream;

use crate::error::ErrorKind;

pub mod error;
pub mod vm;

mod compiler;
mod tokenizer;

/// Compiles a file and links the supplied functions as callable external
/// functions. Use this if you want your programs to be able to yield.
pub fn compile_file(
    path: &Path,
    print: bool,
    functions: Vec<(String, RustFunction)>
) -> Result<vm::VM, Vec<Error>> {
    let tokens = tokenizer::file_to_tokens(path);
    match compiler::Compiler::new(path, &tokens).compile("main", path, &functions) {
        Ok(prog) => {
            let mut vm = vm::VM::new();
            vm.print_blocks = print;
            vm.print_ops = print;
            vm.typecheck(&prog)?;
            vm.init(&prog);
            Ok(vm)
        }
        Err(errors) => Err(errors),
    }
}

/// Compiles, links and runs the given file. Supplied functions are callable
/// external functions. If you want your program to be able to yield, use
/// [compile_file].
pub fn run_file(path: &Path, print: bool, functions: Vec<(String, RustFunction)>) -> Result<(), Vec<Error>> {
    run(tokenizer::file_to_tokens(path), path, print, functions)
}

/// Compile and run a string containing source code. The supplied functions are
/// linked as callable external functions. This is useful for short test
/// programs.
pub fn run_string(s: &str, print: bool, functions: Vec<(String, RustFunction)>) -> Result<(), Vec<Error>> {
    run(tokenizer::string_to_tokens(s), Path::new("builtin"), print, functions)
}

fn run(tokens: TokenStream, path: &Path, print: bool, functions: Vec<(String, RustFunction)>) -> Result<(), Vec<Error>> {
    match compiler::Compiler::new(path, &tokens).compile("main", path, &functions) {
        Ok(prog) => {
            let mut vm = vm::VM::new();
            vm.print_blocks = print;
            vm.print_ops = print;
            vm.typecheck(&prog)?;
            vm.init(&prog);
            if let Err(e) = vm.run() {
                Err(vec![e])
            } else {
                Ok(())
            }
        }
        Err(errors) => Err(errors),
    }
}

/// A linkable external function. Created either manually or using
/// [sylt_macro::extern_function].
pub type RustFunction = fn(&[Value], bool) -> Result<Value, ErrorKind>;

#[derive(Debug, Clone)]
pub enum Type {
    Void,
    Unknown,
    Int,
    Float,
    Bool,
    String,
    Tuple(Vec<Type>),
    Function(Vec<Type>, Box<Type>),
    Blob(Rc<Blob>),
    Instance(Rc<Blob>),
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Void, Type::Void) => true,
            (Type::Instance(a), Type::Instance(b)) => *a == *b,
            (Type::Blob(a), Type::Blob(b)) => *a == *b,
            (Type::Int, Type::Int) => true,
            (Type::Float, Type::Float) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::String, Type::String) => true,
            (Type::Tuple(a), Type::Tuple(b)) => {
                a.iter().zip(b.iter()).all(|(a, b)| a == b)
            }
            (Type::Function(a_args, a_ret), Type::Function(b_args, b_ret)) =>
                a_args == b_args && a_ret == b_ret,
            _ => false,
        }
    }
}

impl From<&Value> for Type {
    fn from(value: &Value) -> Type {
        match value {
            Value::Instance(b, _) => Type::Instance(Rc::clone(b)),
            Value::Blob(b) => Type::Blob(Rc::clone(b)),
            Value::Tuple(v) => {
                Type::Tuple(v.iter().map(|x| Type::from(x)).collect())
            }
            Value::Int(_) => Type::Int,
            Value::Float(_) => Type::Float,
            Value::Bool(_) => Type::Bool,
            Value::String(_) => Type::String,
            Value::Function(_, block) => block.borrow().ty.clone(),
            _ => Type::Void,
        }
    }
}

impl From<Value> for Type {
    fn from(value: Value) -> Type {
        Type::from(&value)
    }
}

impl From<&Type> for Value {
    fn from(ty: &Type) -> Self {
        match ty {
            Type::Void => Value::Nil,
            Type::Blob(b) => Value::Blob(Rc::clone(b)),
            Type::Instance(b) => {
                Value::Instance(Rc::clone(b),
                    Rc::new(RefCell::new(Vec::new())))
            }
            Type::Tuple(fields) => {
                Value::Tuple(Rc::new(fields.iter().map(Value::from).collect()))
            }
            Type::Unknown => Value::Unknown,
            Type::Int => Value::Int(1),
            Type::Float => Value::Float(1.0),
            Type::Bool => Value::Bool(true),
            Type::String => Value::String(Rc::new("".to_string())),
            Type::Function(_, _) => Value::Function(
                Vec::new(),
                Rc::new(RefCell::new(Block::stubbed_block(ty)))),
        }
    }
}

impl From<Type> for Value {
    fn from(ty: Type) -> Self {
        Value::from(&ty)
    }
}


#[derive(Clone)]
pub enum Value {
    Ty(Type),
    Blob(Rc<Blob>),
    Instance(Rc<Blob>, Rc<RefCell<Vec<Value>>>),
    Tuple(Rc<Vec<Value>>),
    Float(f64),
    Int(i64),
    Bool(bool),
    String(Rc<String>),
    Function(Vec<Rc<RefCell<UpValue>>>, Rc<RefCell<Block>>),
    ExternFunction(usize),
    Unknown,
    Nil,
}

impl Debug for Value {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Ty(ty) => write!(fmt, "(type {:?})", ty),
            Value::Blob(b) => write!(fmt, "(blob {})", b.name),
            Value::Instance(b, v) => write!(fmt, "(inst {} {:?})", b.name, v),
            Value::Float(f) => write!(fmt, "(float {})", f),
            Value::Int(i) => write!(fmt, "(int {})", i),
            Value::Bool(b) => write!(fmt, "(bool {})", b),
            Value::String(s) => write!(fmt, "(string \"{}\")", s),
            Value::Function(_, block) => write!(fmt, "(fn {}: {:?})", block.borrow().name, block.borrow().ty),
            Value::ExternFunction(slot) => write!(fmt, "(extern fn {})", slot),
            Value::Unknown => write!(fmt, "(unknown)"),
            Value::Nil => write!(fmt, "(nil)"),
            Value::Tuple(v) => write!(fmt, "({:?})", v),
        }
    }
}

impl PartialEq<Value> for Value {
    fn eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::String(a), Value::String(b)) => a == b,
            (Value::Tuple(a), Value::Tuple(b)) => {
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| a == b)
            }
            (Value::Nil, Value::Nil) => true,
            _ => false,
        }
    }
}

impl Eq for Value {}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Value::Float(a) => {
                // We have to limit the values, because
                // floats are wierd.
                assert!(a.is_finite());
                a.to_bits().hash(state);
            },
            Value::Int(a) => a.hash(state),
            Value::Bool(a) => a.hash(state),
            Value::String(a) => a.hash(state),
            Value::Tuple(a) => a.hash(state),
            Value::Nil => state.write_i8(0),
            _ => {},
        };
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

    fn is_nil(&self) -> bool {
        match self {
            Value::Nil => true,
            _ => false,
        }
    }
}

#[doc(hidden)]
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

#[derive(Debug, Clone)]
pub struct Blob {
    pub id: usize,
    pub name: String,
    /// Maps field names to their slot and type.
    pub fields: HashMap<String, (usize, Type)>,
}

impl PartialEq for Blob {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Blob {
    fn new(id: usize, name: &str) -> Self {
        Self {
            id: id,
            name: String::from(name),
            fields: HashMap::new(),
        }
    }

    fn add_field(&mut self, name: &str, ty: Type) -> Result<(), ()> {
        let size = self.fields.len();
        let entry = self.fields.entry(String::from(name));
        match entry {
            Entry::Occupied(_) => Err(()),
            Entry::Vacant(v) => {
                v.insert((size, ty));
                Ok(())
            }
        }
    }
}

///
/// Ops are opperations that the virtual
/// machine carries out when running the
/// "byte-code".
///
#[derive(Debug, Copy, Clone)]
pub enum Op {
    /// This instruction should never be run.
    /// Finding it in a program is a critical error.
    Illegal,

    /// Pops one value from the stack.
    ///
    /// {A, B} - Pop - {A}
    Pop,
    /// Assumes the value on the top of the
    /// stack has an upvalue, and closes that
    /// upvalue.
    ///
    /// {A, B} - Pop - {A}
    PopUpvalue,
    /// Copies the value on the top of the stack
    /// and puts it on top of the stack.
    ///
    /// {A, B} - Copy - {A, B, B}
    Copy,
    /// Adds the value indexed in the `constants-vector` to the top of the stack.
    /// Also links upvalues if the value is a function.
    ///
    /// {A} - Constant(B) - {A, B}
    Constant(usize),
    /// Creates a new [Tuple] with the given size and place it on the top
    /// of the stack.
    ///
    /// {A, B, C} - Tuple(3) - {D(A, B, C)}
    Tuple(usize),

    /// Indexes something indexable, currently only Tuples,
    /// and adds that element to the stack.
    ///
    /// {T, I} - Index - {T[I]}
    Index,
    /// Looks up a field by the given name
    /// and replaces the parent with it.
    /// Currently only expects [Value::Blob].
    /// (name is looked up in the internal string-list)
    ///
    /// {O} - Get(F) - {O.F}
    Get(usize),
    /// Looks up a field by the given name
    /// and replaces the current value in the object.
    /// Currently only expects [Value::Blob].
    /// (name is looked up in the internal string-list)
    ///
    /// {O} - Set(F) - {}
    Set(usize),

    /// Adds the two top elements on the stack,
    /// using the function [op::add]. The result
    /// is the pushed.
    ///
    /// {A, B} - Add - {A + B}
    Add,
    /// Sub the two top elements on the stack,
    /// using the function [op::sub]. The result
    /// is the pushed.
    ///
    /// {A, B} - Sub - {A - B}
    Sub,
    /// Multiples the two top elements on the stack,
    /// using the function [op::mul]. The result
    /// is the pushed.
    ///
    /// {A, B} - Mul - {A - B}
    Mul,
    /// Divides the two top elements on the stack,
    /// using the function [op::div]. The result
    /// is the pushed.
    ///
    /// {A, B} - Div - {A / B}
    Div,
    /// Negates the top element on the stack.
    ///
    /// {A} - Neg - {-A}
    Neg,

    /// Performs a boolean and on the
    /// top 2 stack elements using [op::and].
    ///
    /// {A, B} - And - {A && B}
    And,
    /// Performs a boolean or on the
    /// top 2 stack elements using [op::or].
    ///
    /// {A, B} - Or - {A || B}
    Or,
    /// Performs a boolean not on the
    /// top stack element using [op::not].
    ///
    /// {A} - Not - {!A}
    Not,

    /// Sets the instruction pointer
    /// to the given value.
    ///
    /// Does not affect the stack.
    Jmp(usize),
    /// Sets the instruction pointer
    /// to the given value, if the
    /// topmost value is false, also
    /// pops this value.
    ///
    /// {A} - JmpFalse(n) - {}
    JmpFalse(usize),
    /// Sets the instruction pointer
    /// to the given value and pops
    /// the given amount of values.
    ///
    /// Used for 'break' and 'continue'.
    ///
    /// {A, B, C} - JmpNPop(n, 2) - {A}
    JmpNPop(usize, usize),

    /// Compares the two topmost elements
    /// on the stack for equality, and pushes
    /// the result. Compares using [op::eq].
    ///
    /// {A, B} - Equal - {A == B}
    Equal,
    /// Compares the two topmost elements
    /// on the stack for order, and pushes the result.
    /// Compares using [op::less].
    ///
    /// {A, B} - Less - {A < B}
    Less,
    /// Compares the two topmost elements
    /// on the stack for order, and pushes the result.
    /// Compares using [op::less].
    ///
    /// {A, B} - Greater - {B < A}
    Greater,

    /// Pops the top value of the stack, and
    /// crashes the program if it is false.
    ///
    /// {A} - Assert - {}
    Assert,
    /// This instruction should not be executed.
    /// If it is the program crashes.
    ///
    /// Does not affect the stack.
    Unreachable,

    /// Reads the value counted from the
    /// bottom of the stack and adds it
    /// to the top.
    ///
    /// {A, B} - ReadLocal(0) - {A, B, A}
    ReadLocal(usize),
    /// Sets the value at the given index
    /// of the stack, to the topmost value.
    /// Pops the topsmost element.
    ///
    /// {A, B} - AssignLocal(0) - {B}
    AssignLocal(usize),

    /// Reads the upvalue, and adds it
    /// to the top of the stack.
    ///
    /// {} - ReadUpvalue(0) - {A}
    ReadUpvalue(usize),
    /// Sets the given upvalue, and pops
    /// the topmost element.
    ///
    /// {A} - AssignUpvalue(0) - {}
    AssignUpvalue(usize),

    /// A helper instruction for the typechecker,
    /// makes sure the top value on the stack
    /// is of the given type, and is ment to signal
    /// that the "variable" is added.
    /// (The type is looked up in the constants vector)
    ///
    /// Does not affect the stack.
    Define(usize),

    /// Links the upvalues for the given constant
    /// function. This updates the constant stack.
    ///
    /// Does not affect the stack.
    Link(usize),

    /// Calls "something" with the given number
    /// of arguments. The callable value is
    /// then replaced with the result.
    ///
    /// Callable things are: [Value::Blob], [Value::Function],
    /// and [Value::ExternFunction].
    ///
    /// {F, A, B} - Call(2) - {F(A, B)}
    Call(usize),

    /// Prints and pops the top value on the stack.
    ///
    /// {A} - Print - {}
    Print,

    /// Pops the current stackframe and replaces
    /// slot 0 with the top value. Also pops
    /// upvalues.
    ///
    /// {F, A, B} - Return - {..., B}
    Return,

    /// Temporarily stops execution and returns
    /// to the call site.
    ///
    /// Does not affect the stack.
    Yield,
}

///
/// Module with all the operators that can be applied
/// to values.
///
/// Broken out because they need to be recursive.
mod op {
    use super::Value;
    use std::rc::Rc;

    fn tuple_bin_op(a: &Rc<Vec<Value>>, b: &Rc<Vec<Value>>, f: fn (&Value, &Value) -> Value) -> Value {
        Value::Tuple(Rc::new(a.iter().zip(b.iter()).map(|(a, b)| f(a, b)).collect()))
    }

    fn tuple_un_op(a: &Rc<Vec<Value>>, f: fn (&Value) -> Value) -> Value {
        Value::Tuple(Rc::new(a.iter().map(f).collect()))
    }

    pub fn neg(value: &Value) -> Value {
        match value {
            Value::Float(a) => Value::Float(-*a),
            Value::Int(a) => Value::Int(-*a),
            Value::Tuple(a) => tuple_un_op(a, neg),
            _ => Value::Nil,
        }
    }

    pub fn not(value: &Value) -> Value {
        match value {
            Value::Bool(a) => Value::Bool(!*a),
            Value::Tuple(a) => tuple_un_op(a, not),
            _ => Value::Nil,
        }
    }


    pub fn add(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Float(a + b),
            (Value::Int(a), Value::Int(b)) => Value::Int(a + b),
            (Value::String(a), Value::String(b)) => Value::String(Rc::from(format!("{}{}", a, b))),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, add),
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
            _ => Value::Nil,
        }
    }

    pub fn div(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Float(a / b),
            (Value::Int(a), Value::Int(b)) => Value::Int(a / b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, div),
            _ => Value::Nil,
        }
    }

    pub fn eq(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Bool(a == b),
            (Value::Int(a), Value::Int(b)) => Value::Bool(a == b),
            (Value::String(a), Value::String(b)) => Value::Bool(a == b),
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(a == b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, eq),
            _ => Value::Nil,
        }
    }

    pub fn less(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Bool(a < b),
            (Value::Int(a), Value::Int(b)) => Value::Bool(a < b),
            (Value::String(a), Value::String(b)) => Value::Bool(a < b),
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(a < b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, less),
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
            _ => Value::Nil,
        }
    }

    pub fn or(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(*a || *b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, or),
            _ => Value::Nil,
        }
    }
}

#[derive(Debug)]
enum BlockLinkState {
    Linked,
    Unlinked,
    Nothing,
}

#[derive(Debug)]
pub struct Block {
    pub ty: Type,
    upvalues: Vec<(usize, bool, Type)>,
    linking: BlockLinkState,

    pub name: String,
    pub file: PathBuf,
    ops: Vec<Op>,
    last_line_offset: usize,
    line_offsets: HashMap<usize, usize>,
}

impl Block {
    fn new(name: &str, file: &Path) -> Self {
        Self {
            ty: Type::Void,
            upvalues: Vec::new(),
            linking: BlockLinkState::Nothing,

            name: String::from(name),
            file: file.to_owned(),
            ops: Vec::new(),
            last_line_offset: 0,
            line_offsets: HashMap::new(),
        }
    }

    fn mark_constant(&mut self) {
        if self.upvalues.is_empty() {
            return;
        }
        self.linking = BlockLinkState::Unlinked;
    }

    fn link(&mut self) {
        self.linking = BlockLinkState::Linked;
    }

    fn needs_linking(&self) -> bool {
        matches!(self.linking, BlockLinkState::Unlinked)
    }

    // Used to create empty functions.
    fn stubbed_block(ty: &Type) -> Self {
        let mut block = Block::new("/empty/", Path::new(""));
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

    fn add_line(&mut self, token_position: usize) {
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
            println!("{}{}",
                     if self.line_offsets.contains_key(&i) {
                         format!("{:5} ", self.line_offsets[&i].red())
                     } else {
                         format!("    {} ", "|".red())
                     },
                     format!("{:05} {:?}", i.blue(), s)
            );
        }
        println!();
    }

    fn add(&mut self, op: Op, token_position: usize) -> usize {
        let len = self.curr();
        self.add_line(token_position);
        self.ops.push(op);
        len
    }

    fn add_from(&mut self, ops: &[Op], token_position: usize) -> usize {
        let len = self.curr();
        self.add_line(token_position);
        self.ops.extend_from_slice(ops);
        len
    }

    fn curr(&self) -> usize {
        self.ops.len()
    }

    fn patch(&mut self, op: Op, pos: usize) {
        self.ops[pos] = op;
    }
}

#[derive(Clone)]
pub struct Prog {
    pub blocks: Vec<Rc<RefCell<Block>>>,
    pub functions: Vec<RustFunction>,
    pub constants: Vec<Value>,
    pub strings: Vec<String>,
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::error::ErrorKind;

    use super::{run_file, run_string};

    #[macro_export]
    macro_rules! assert_errs {
        ($result:expr, [ $( $kind:pat ),* ]) => {
            let errs = if let Err(errs) = $result {
                errs
            } else {
                eprintln!("    Program succeeded when it should've failed");
                unreachable!();
            };
            if !matches!(
                errs.as_slice(),
                &[$($crate::error::Error {
                    kind: $kind,
                    file: _,
                    line: _,
                    message: _,
                },
                )*]
            ) {
                eprintln!("Unexpected errors");
                eprint!("    Got:  [");
                for err in errs {
                    eprint!(" ErrorKind::{:?} ", err.kind);
                }
                eprint!("]\n    Want: [");
                $(
                eprint!(" {} ", stringify!($kind));
                )*
                eprintln!("]");
                assert!(false);
            }
        };
    }

    use std::time::Duration;
    use std::sync::mpsc;
    use std::thread;
    use owo_colors::OwoColorize;

    // Shamelessly stolen from https://github.com/rust-lang/rfcs/issues/2798
    pub fn panic_after<T, F>(d: Duration, f: F) -> T
    where
        T: Send + 'static,
        F: FnOnce() -> T,
        F: Send + 'static,
    {
        let (done_tx, done_rx) = mpsc::channel();
        let handle = thread::spawn(move || {
            let val = f();
            done_tx.send(()).expect("Unable to send completion signal");
            val
        });

        let msg = match done_rx.recv_timeout(d) {
            Ok(_) => {
                return handle.join().expect("Thread panicked");
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {
                "Test took too long to complete"
            },
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                "Test produced incorrect result"
            },
        };
        eprintln!("    #### {} ####", msg.red());
        panic!(msg);
    }

    #[macro_export]
    macro_rules! test_string {
        ($fn:ident, $prog:literal) => {
            #[test]
            fn $fn() {
                crate::tests::panic_after(std::time::Duration::from_millis(500), || {
                    let prog = std::concat!("q :: fn {", $prog, "\n{}\n}\nq()");
                    match $crate::run_string(&prog, true, Vec::new()) {
                        Ok(()) => {},
                        Err(errs) => {
                            for e in errs.iter() {
                                eprintln!("{}", e);
                            }
                            eprintln!("  {} - failed\n", stringify!($fn));
                            unreachable!();
                        }
                    }
                });
            }
        };
        ($fn:ident, $prog:literal, $errs:tt) => {
            #[test]
            fn $fn() {
                crate::tests::panic_after(std::time::Duration::from_millis(500), || {
                    let prog = std::concat!("q :: fn {", $prog, "\n{}\n}\nq()");
                    $crate::assert_errs!($crate::run_string(&prog, true, Vec::new()), $errs);
                })
            }
        }
    }

    #[macro_export]
    macro_rules! test_file {
        ($fn:ident, $path:literal) => {
            #[test]
            fn $fn() {
                let file = Path::new($path);
                run_file(&file, true, Vec::new()).unwrap();
            }
        };
    }

    #[test]
    fn unreachable_token() {
        assert_errs!(run_string("<!>\n", true, Vec::new()), [ErrorKind::Unreachable]);
    }

    #[test]
    fn assign_to_constant() {
        assert_errs!(run_string("a :: 2\na = 2", true, Vec::new()), [ErrorKind::SyntaxError(_, _)]);
    }

    #[test]
    fn assign_to_constant_upvalue() {
        assert_errs!(run_string("a :: 2\nq :: fn { a = 2 }\nq()\na", true, Vec::new()), [ErrorKind::SyntaxError(_, _)]);
    }

    #[test]
    fn undefined_blob() {
        assert_errs!(run_string("a :: B()\n", true, Vec::new()), [ErrorKind::SyntaxError(_, _)]);
    }

    #[test]
    fn call_before_link() {
        let prog = "
a := 1
f()
c := 5

f :: fn {
    c <=> 5
}
a
        ";
        assert_errs!(run_string(prog, true, Vec::new()), [ErrorKind::InvalidProgram, ErrorKind::TypeError(_, _)]);
    }

    #[test]
    fn unused_variable() {
        assert_errs!(run_string("a := 1", true, Vec::new()), [ErrorKind::SyntaxError(1, _)]);
    }

    #[test]
    fn unused_upvalue() {
        assert_errs!(run_string("a := 1\nf :: fn { a = 2 }\nf()", true, Vec::new()), [ErrorKind::SyntaxError(1, _)]);
    }

    #[test]
    fn unused_function() {
        assert_errs!(run_string("a := 1\nf := fn { a }\n", true, Vec::new()), [ErrorKind::SyntaxError(2, _)]);
    }

    macro_rules! test_multiple {
        ($mod:ident, $( $fn:ident : $prog:literal ),+ $( , )? ) => {
            mod $mod {
                $( test_string!($fn, $prog); )+
            }
        }
    }

    test_multiple!(
        order_of_operations,
        terms_and_factors: "1 + 1 * 2 <=> 3
                            1 * 2 + 3 <=> 5",
        in_rhs: "5 <=> 1 * 2 + 3",
        parenthesis: "(1 + 2) * 3 <=> 9",
        negation: "-1 <=> 0 - 1
                   -1 + 2 <=> 1
                   -(1 + 2) <=> -3
                   1 + -1 <=> 0
                   2 * -1 <=> -2",
    );

    test_multiple!(
        variables,
        single_variable: "a := 1
                          a <=> 1",
        two_variables: "a := 1
                        b := 2
                        a <=> 1
                        b <=> 2",
        stack_ordering: "a := 1
                         b := 2
                         b <=> 2
                         a <=> 1",
        assignment: "a := 1
                     b := 2
                     a = b
                     a <=> 2
                     b <=> 2",
    );

    test_multiple!(
        if_,
        compare_constants_equality: "if 1 == 2 {
                                        <!>
                                     }",
        compare_constants_unequality: "if 1 != 1 {
                                         <!>
                                       }",
        compare_variable: "a := 1
                           if a == 0 {
                             <!>
                           }
                           if a != 1 {
                             <!>
                           }",
        else_: "a := 1
                res := 0
                if a == 0 {
                  <!>
                } else {
                  res = 1
                }
                res <=> 1",
        else_if: "a := 1
                  res := 0
                  if a == 0 {
                    <!>
                  } else if a == 1 {
                    res = 1
                  } else {
                    <!>
                  }
                  res <=> 1",
    );

    test_multiple!(
        fun,
        simplest: "f := fn {}
                   f()",
        param_1: "f := fn a: int {}
                  f(1)",
        return_1: "f := fn -> int {
                     ret 1
                   }
                   f() <=> 1",
        param_and_return: "f := fn a: int -> int {
                             ret a * 2
                           }
                           f(1) <=> 2
                           f(5) <=> 10",
        param_2: "add := fn a: int, b: int -> int {
                    ret a + b
                  }
                  add(1, 1) <=> 2
                  add(10, 20) <=> 30",
        /*
        calls_inside_calls: "one := fn -> int {
                               ret 1
                             }
                             add := fn a: int, b: int -> int {
                               ret a + b
                             }
                             add(one(), one()) <=> 2
                             add(add(one(), one()), one()) <=> 3
                             add(one(), add(one(), one())) <=> 3",
        passing_functions: "g := fn -> int {
                              ret 1
                            }
                            f := fn inner: fn -> int -> int {
                              ret inner()
                            }
                            f(g) <=> 1",
        passing_functions_mixed: "g := fn a: int -> int {
                                    ret a * 2
                                  }
                                  f := fn inner: fn int -> int, a: int -> int {
                                    ret inner(a)
                                  }
                                  f(g, 2) <=> 4",
        */
        multiple_returns: "f := fn a: int -> int {
                             if a == 1 {
                               ret 2
                             } else {
                               ret 3
                             }
                           }
                           f(0) <=> 3
                           f(1) <=> 2
                           f(2) <=> 3",
        precedence: "f := fn a: int, b: int -> int {
                       ret a + b
                     }
                     1 + f(2, 3) <=> 6
                     2 * f(2, 3) <=> 10
                     f(2, 3) - (2 + 3) <=> 0",
        factorial: "factorial : fn int -> int = fn n: int -> int {
                      if n <= 1 {
                        ret 1
                      }
                      ret n * factorial(n - 1)
                    }
                    factorial(5) <=> 120
                    factorial(6) <=> 720
                    factorial(12) <=> 479001600",

/*
        returning_closures: "
f : fn -> fn -> int = fn -> fn -> int {
    x : int = 0
    f := fn -> int {
        x = x + 1
        ret x
    }
    f() <=> 1
    ret f
}

a := f()
b := f()

a() <=> 2
a() <=> 3

b() <=> 2
b() <=> 3

a() <=> 4
",
*/
    );

    test_multiple!(
        blob,
        simple: "blob A {}",
        field: "blob A { a: int }",
        /*
        instantiate: "blob A {}
                      a := A()
                      a",
        field_assign: "blob A { a: int }
                       a := A()
                       a.a = 2",
        field_get: "blob A { a: int }
                       a := A()
                       a.a = 2
                       a.a <=> 2
                       2 <=> a.a",
        multiple_fields: "blob A {
                            a: int
                            b: int
                          }
                          a := A()
                          a.a = 2
                          a.b = 3
                          a.a + a.b <=> 5
                          5 <=> a.a + a.b",
        */
        blob_infer: "
blob A { }
a : A = A()
a
",
    );

    test_multiple!(tuples,
        add: "(1, 2, 3, 4) + (4, 3, 2, 1) <=> (5, 5, 5, 5)",
        sub: "(1, -2, 3, -4) - (4, 3, -2, -1) <=> (-3, 1, 1, -5)",
        mul: "(0, 1, 2) * (2, 3, 4) <=> (0, 3, 8)",
        types: "a: (int, float, int) = (1, 1., 1)\na",
        more_types: "a: (str, bool, int) = (\"abc\", true, 1)\na",
    );

    test_file!(scoping, "progs/tests/scoping.sy");
    // test_file!(for_, "progs/tests/for.sy");

    test_multiple!(
        op_assign,
        add: "a := 1\na += 1\na <=> 2",
        sub: "a := 2\na -= 1\na <=> 1",
        mul: "a := 2\na *= 2\na <=> 4",
        div: "a := 2\na /= 2\na <=> 1",
/*
        cluster: "
blob A { a: int }
a := A()
a.a = 0
a.a += 1
a.a <=> 1
a.a *= 2
a.a <=> 2
a.a /= 2
a.a <=> 1
a.a -= 1
a.a <=> 0"
*/
    );

    test_multiple!(
        fancy_call,
        not: "f := fn {}\n f!\n",
        one_arg: "f := fn a:int { a <=> 1 }\n f! 1\n",
        two_arg: "f := fn a:int, b:int { b <=> 3 }\n f! 1, 1 + 2\n",
        three_arg: "f := fn a:int, b:int, c:int { c <=> 13 }\n f! 1, 1 + 2, 1 + 4 * 3\n",
    );

    test_multiple!(
        newline_regression,
        simple: "a := 1 // blargh \na += 1 // blargh \n a <=> 2 // HARGH",
        expressions: "1 + 1 // blargh \n 2 // blargh \n // HARGH \n",
    );

    test_multiple!(
        break_and_continue,
        simple_break: "
a := 0
for i := 0, i < 10, i += 1 {
    a = a + 1
    if i == 2 {
        break
    }
}
a <=> 3
",

        simple_continue: "
a := 0
for i := 0, i < 4, i += 1 {
    if i == 2 {
        continue
    }
    a = a + 1
}
a <=> 3
",

        advanced_break: "
a := 0
for i := 0, i < 10, i += 1 {
    q := 0
    qq := 0
    qqq := 0
    qqqq := 0

    a = a + 1
    if i == 2 {
        break
    }

    q
    qq
    qqq
    qqqq
}
a <=> 3
",

        advanced_continue: "
a := 0
for i := 0, i < 4, i += 1 {
    q := 0
    qq := 0
    qqq := 0
    qqqq := 0

    if i == 2 {
        continue
    }
    a = a + 1

    q
    qq
    qqq
    qqqq
}
a <=> 3
",
    );

    test_multiple!(
        read_constants,
        simple: "
a :: 1
a <=> 1
b := 2
{
    a <=> 1
    b <=> 2
}",
    );

    test_multiple!(
        assignment_op_regression,
        simple_add: "
a := 0
b := 99999
a += 1
a <=> 1
b <=> 99999
",

        simple_sub: "
a := 0
b := 99999
a -= 1
a <=> -1
b <=> 99999
",

        strange: "
a := 0
{
    b := 99999
    {
        a := 99999
        a
    }
    b
    a -= 1
}
a <=> -1
",
    );

    test_multiple!(
        declaration_order,
        blob_simple: "
a := A()
a

blob A {
    a: int
}
",

        blob_complex: "
a := A()
b := B()
c := C()
b2 := B()

a
b
c
b2

blob A {
    c: C
}
blob C { }
blob B { }
",

        blob_infer: "
blob A { }

a : A = A()
a
",


/*
        constant_function: "
a()
a :: fn {}
",

        constant_function_complex: "
h :: fn -> int {
    ret 3
}

a() <=> 3

k :: fn -> int {
    ret h()
}

a :: fn -> int {
    ret q()
}

q :: fn -> int {
    ret k()
}
",
        constants_in_inner_functions: "
q : int = 0

f :: fn -> fn -> {
    g :: fn {
        q += 1
    }
    ret g
}

g := f()
g()
q <=> 1
g()
q <=> 2
g()
q <=> 3
",
*/

        constant_function_closure: "
q := 1

f :: fn -> int {
    q += 1
    ret q
}

f() <=> 2
f() <=> 3
f() <=> 4
f() <=> 5
",
    );

/*
    test_string!(conflict_markers, "
<<<<<<< HEAD
print extern_test(4.0)
=======
print extern_test(5.0)
>>>>>>> 2
",
                 [ErrorKind::SyntaxError(_, _), ErrorKind::GitConflictError(2, 6)]
    );
*/

}
