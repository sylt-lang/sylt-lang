use gumdrop::Options;
use owo_colors::OwoColorize;
use serde::{Deserialize, Serialize};
use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use error::Error;

use crate::error::ErrorKind;

pub mod error;
pub mod vm;

mod compiler;
mod sectionizer;
mod tokenizer;

pub trait Next {
    fn next(&self) -> Self;
}

/// Compiles, links and runs the given file. The supplied functions are callable
/// external functions.
pub fn run_file(args: &Args, functions: Vec<(String, RustFunction)>) -> Result<(), Vec<Error>> {
    run(compile(args, functions)?, args)
}

pub fn run(prog: Prog, args: &Args) -> Result<(), Vec<Error>> {
    let mut vm = vm::VM::new();
    vm.print_bytecode = args.verbosity >= 1;
    vm.print_exec = args.verbosity >= 2;
    vm.typecheck(&prog)?;
    vm.init(&prog);
    if let Err(e) = vm.run() {
        Err(vec![e])
    } else {
        Ok(())
    }
}

/// Compiles and serializes the given file.
pub fn serialize(args: &Args) -> Result<Vec<u8>, Vec<Error>> {
    let prog = compile(args, vec![])?;
    bincode::serialize(&prog).map_err(|_| vec![]) //TODO
}

/// Deserializes and links the given file.
pub fn deserialize(bytes: Vec<u8>) -> Result<Prog, Vec<Error>> {
    bincode::deserialize(&bytes).map_err(|_| vec![])
}

fn compile(args: &Args, functions: Vec<(String, RustFunction)>) -> Result<Prog, Vec<Error>> {
    let path = match &args.file {
        Some(file) => file,
        None => {
            return Err(vec![Error {
                kind: ErrorKind::NoFileGiven,
                file: PathBuf::from(""),
                line: 0,
                message: None,
            }]);
        }
    };
    let sections = sectionizer::sectionize(&path)?;
    compiler::Compiler::new(sections).compile("/preamble", &path, &functions)
}

#[derive(Default, Debug, Options)]
pub struct Args {
    #[options(free)]
    pub file: Option<PathBuf>,

    #[options(short = "r", long = "run", help = "Runs a precompiled sylt binary")]
    pub is_binary: bool,

    #[options(short = "c", long = "compile", help = "Compile a sylt binary")]
    pub compile_target: Option<PathBuf>,

    #[options(short = "v", no_long, count, help = "Increase verbosity, up to max 2")]
    pub verbosity: u32,

    #[options(help = "Print this help")]
    pub help: bool,
}

pub fn path_to_module(current_file: &Path, module: &str) -> PathBuf {
    let mut res = PathBuf::from(current_file);
    res.pop();
    res.push(format!("{}.sy", module));
    res
}

/// A linkable external function. Created either manually or using
/// [sylt_macro::extern_function].
pub type RustFunction = fn(&[Value], bool) -> Result<Value, ErrorKind>;

#[derive(Debug, Clone, Deserialize, Serialize)]
pub enum Type {
    Void,
    Unknown,
    Int,
    Float,
    Bool,
    String,
    Tuple(Vec<Type>),
    Union(HashSet<Type>),
    List(Box<Type>),
    Set(Box<Type>),
    Dict(Box<Type>, Box<Type>),
    Function(Vec<Type>, Box<Type>),
    Blob(Rc<Blob>),
    Instance(Rc<Blob>),
}

impl Hash for Type {
    fn hash<H: Hasher>(&self, h: &mut H) {
        match self {
            Type::Void => 0,
            Type::Unknown => 1,
            Type::Int => 2,
            Type::Float => 3,
            Type::Bool => 4,
            Type::String => 5,
            Type::Tuple(ts) => {
                for t in ts.iter() {
                    t.hash(h);
                }
                6
            }
            Type::List(t) => {
                t.as_ref().hash(h);
                12
            }
            Type::Set(t) => {
                t.as_ref().hash(h);
                13
            }
            Type::Dict(k, v) => {
                k.as_ref().hash(h);
                v.as_ref().hash(h);
                14
            }
            Type::Union(ts) => {
                for t in ts {
                    t.hash(h);
                }
                7
            }
            Type::Function(args, ret) => {
                ret.hash(h);
                for t in args.iter() {
                    t.hash(h);
                }
                8
            }
            Type::Blob(b) => {
                for (_, t) in b.fields.values() {
                    t.hash(h);
                }
                10
            }
            Type::Instance(b) => {
                for (_, t) in b.fields.values() {
                    t.hash(h);
                }
                11
            }
        }
        .hash(h);
    }
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
            (Type::Tuple(a), Type::Tuple(b)) => a.iter().zip(b.iter()).all(|(a, b)| a == b),
            (Type::Union(a), b) | (b, Type::Union(a)) => a.iter().any(|x| x == b),
            (Type::List(a), Type::List(b)) => a == b,
            (Type::Set(a), Type::Set(b)) => a == b,
            (Type::Dict(ak, av), Type::Dict(bk, bv)) => ak == bk && av == bv,
            (Type::Function(a_args, a_ret), Type::Function(b_args, b_ret)) => {
                a_args == b_args && a_ret == b_ret
            }
            _ => false,
        }
    }
}

impl Eq for Type {}

fn maybe_union_type<'a>(v: impl Iterator<Item = &'a Value>) -> Type {
    let set: HashSet<_> = v.map(|x| Type::from(x)).collect();
    match set.len() {
        0 => Type::Unknown,
        1 => set.into_iter().next().unwrap(),
        _ => Type::Union(set),
    }
}

impl From<&Value> for Type {
    fn from(value: &Value) -> Type {
        match value {
            Value::Instance(b, _) => Type::Instance(Rc::clone(b)),
            Value::Blob(b) => Type::Blob(Rc::clone(b)),
            Value::Tuple(v) => Type::Tuple(v.iter().map(|x| Type::from(x)).collect()),
            Value::List(v) => {
                let v: &RefCell<_> = v.borrow();
                let v = &v.borrow();
                let t = maybe_union_type(v.iter());
                Type::List(Box::new(t))
            }
            Value::Set(v) => {
                let v: &RefCell<_> = v.borrow();
                let v = &v.borrow();
                let t = maybe_union_type(v.iter());
                Type::Set(Box::new(t))
            }
            Value::Dict(v) => {
                let v: &RefCell<_> = v.borrow();
                let v = &v.borrow();
                let k = maybe_union_type(v.keys());
                let v = maybe_union_type(v.values());
                Type::Dict(Box::new(k), Box::new(v))
            }
            Value::Union(v) => Type::Union(v.iter().map(|x| Type::from(x)).collect()),
            Value::Int(_) => Type::Int,
            Value::Float(_) => Type::Float,
            Value::Bool(_) => Type::Bool,
            Value::String(_) => Type::String,
            Value::Function(_, block) => {
                let block: &RefCell<_> = block.borrow();
                let block = &block.borrow();
                block.borrow().ty.clone()
            }
            Value::Unknown => Type::Unknown,
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
            Type::Instance(b) => Value::Instance(Rc::clone(b), Rc::new(RefCell::new(Vec::new()))),
            Type::Tuple(fields) => Value::Tuple(Rc::new(fields.iter().map(Value::from).collect())),
            Type::Union(v) => Value::Union(v.iter().map(Value::from).collect()),
            Type::List(v) => Value::List(Rc::new(RefCell::new(vec![Value::from(v.as_ref())]))),
            Type::Set(v) => {
                let mut s = HashSet::new();
                s.insert(Value::from(v.as_ref()));
                Value::Set(Rc::new(RefCell::new(s)))
            }
            Type::Dict(k, v) => {
                let mut s = HashMap::new();
                s.insert(Value::from(k.as_ref()), Value::from(v.as_ref()));
                Value::Dict(Rc::new(RefCell::new(s)))
            }
            Type::Unknown => Value::Unknown,
            Type::Int => Value::Int(1),
            Type::Float => Value::Float(1.0),
            Type::Bool => Value::Bool(true),
            Type::String => Value::String(Rc::new("".to_string())),
            Type::Function(_, _) => Value::Function(
                Rc::new(Vec::new()),
                Rc::new(RefCell::new(Block::stubbed_block(ty))),
            ),
        }
    }
}

impl From<Type> for Value {
    fn from(ty: Type) -> Self {
        Value::from(&ty)
    }
}

impl Type {
    /// Checks if the other type is valid in a place where the self type is. It's an asymmetrical
    /// comparison for types useful when checking assignment.
    pub fn fits(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Type::Unknown) => true,
            (Type::List(a), Type::List(b)) => a.fits(b),
            (Type::Set(a), Type::Set(b)) => a.fits(b),
            (Type::Dict(ak, av), Type::Dict(bk, bv)) => ak.fits(bk) && av.fits(bv),
            (Type::Union(a), Type::Union(b)) => b.iter().all(|x| a.contains(x)),
            (_, Type::Union(_)) => false,
            (a, b) => a == b,
        }
    }
}

#[derive(Clone, Deserialize, Serialize)]
pub enum Value {
    Ty(Type),
    Blob(Rc<Blob>),
    Instance(Rc<Blob>, Rc<RefCell<Vec<Value>>>),
    Tuple(Rc<Vec<Value>>),
    List(Rc<RefCell<Vec<Value>>>),
    Set(Rc<RefCell<HashSet<Value>>>),
    Dict(Rc<RefCell<HashMap<Value, Value>>>),
    Union(HashSet<Value>),
    Float(f64),
    Int(i64),
    Bool(bool),
    String(Rc<String>),
    Function(Rc<Vec<Rc<RefCell<UpValue>>>>, Rc<RefCell<Block>>),
    ExternFunction(usize),
    /// This value should not be present when running, only when type checking.
    /// Most operations are valid but produce funky results.
    Unknown,
    /// Should not be present when running.
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
            Value::List(v) => write!(fmt, "(array {:?})", v),
            Value::Set(v) => write!(fmt, "(set {:?})", v),
            Value::Dict(v) => write!(fmt, "(dict {:?})", v),
            Value::Function(_, block) => {
                let block: &RefCell<_> = block.borrow();
                let block = &block.borrow();
                write!(fmt, "(fn {}: {:?})", block.name, block.ty)
            }
            Value::ExternFunction(slot) => write!(fmt, "(extern fn {})", slot),
            Value::Unknown => write!(fmt, "(unknown)"),
            Value::Nil => write!(fmt, "(nil)"),
            Value::Tuple(v) => write!(fmt, "({:?})", v),
            Value::Union(v) => write!(fmt, "(U {:?})", v),
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
            (Value::List(a), Value::List(b)) => a == b,
            (Value::Set(a), Value::Set(b)) => a == b,
            (Value::Dict(a), Value::Dict(b)) => a == b,
            (Value::Tuple(a), Value::Tuple(b)) => {
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| a == b)
            }
            (Value::Union(a), b) | (b, Value::Union(a)) => a.iter().any(|x| x == b),
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
            }
            Value::Int(a) => a.hash(state),
            Value::Bool(a) => a.hash(state),
            Value::String(a) => a.hash(state),
            Value::Tuple(a) => a.hash(state),
            Value::Nil => state.write_i8(0),
            _ => {}
        };
    }
}

impl Value {
    fn identity(self) -> Self {
        match self {
            Value::Float(_) => Value::Float(1.0),
            Value::Int(_) => Value::Int(1),
            Value::Bool(_) => Value::Bool(true),
            x if matches!(x, Value::List(_)) => {
                let x = Type::from(x);
                Value::from(&x)
            }
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
#[derive(Clone, Debug, Serialize, Deserialize)]
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

#[derive(Debug, Clone, Deserialize, Serialize)]
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
#[derive(Debug, Copy, Clone, Deserialize, Serialize)]
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
    /// Copies the N values on the top of the stack
    /// and puts them on top of the stack.
    ///
    /// {A, B} - Copy(2) - {A, B, A, B}
    Copy(usize),
    /// Adds the value indexed in the `constants-vector` to the top of the stack.
    /// Also links upvalues if the value is a function.
    ///
    /// {A} - Constant(B) - {A, B}
    Constant(usize),

    /// Creates a new [Value::Tuple] with the given size and place it on the top
    /// of the stack.
    ///
    /// {A, B, C} - Tuple(3) - {D(A, B, C)}
    Tuple(usize),
    /// Creates a new [Value::List] with the given size and place it on the top
    /// of the stack.
    ///
    /// {A, B, C} - List(3) - {D(A, B, C)}
    List(usize),
    /// Creates a new [Value::Set] with the given elements and place it on the top
    /// of the stack.
    ///
    /// {A, B, A} - Set(3) - {D(A, B)}
    Set(usize),
    /// Creates a new [Value::Dict] with the given elements and place it on the top
    /// of the stack.
    ///
    /// {A, B, C, D, A, E} - Dict(6) - {D(A:E, C:D)}
    Dict(usize),

    /// Indexes something indexable,
    /// and adds that element to the stack.
    ///
    /// {T, I} - Index - {T[I]}
    GetIndex,
    /// Assigns the indexes of something indexable.
    /// T[I] = V
    ///
    /// {T, I, V} - Index - {}
    AssignIndex,
    /// Looks up a field by the given name
    /// and replaces the parent with it.
    /// Currently only expects [Value::Blob].
    /// (name is looked up in the internal string-list)
    ///
    /// {O} - Get(F) - {O.F}
    GetField(usize),
    /// Looks up a field by the given name
    /// and replaces the current value in the object.
    /// Currently only expects [Value::Blob].
    /// (name is looked up in the internal string-list)
    ///
    /// {O} - Set(F) - {}
    AssignField(usize),

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

    /// A helper instruction for the type checker.
    /// *Makes sure* that the top value on the stack
    /// is of the given type, and is meant to signal
    /// that the "variable" is added.
    /// (The type is looked up in the constants vector.)
    ///
    /// Does not affect the stack.
    Define(usize),
    /// A helper instruction for the typechecker,
    /// *assumes* top value on the stack
    /// is of the given type. Usefull for helping the
    /// type system where it just can't do it.
    /// (The type is looked up in the constants vector)
    ///
    /// Does not affect the stack.
    Force(usize),

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
    use super::{Type, Value};
    use std::collections::HashSet;
    use std::rc::Rc;

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
            Value::Unknown => Value::from(Type::Bool),
            _ => Value::Nil,
        }
    }

    pub fn add(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Float(a + b),
            (Value::Int(a), Value::Int(b)) => Value::Int(a + b),
            (Value::String(a), Value::String(b)) => Value::String(Rc::from(format!("{}{}", a, b))),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, add),
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

#[derive(Debug, Deserialize, Serialize)]
enum BlockLinkState {
    Linked,
    Unlinked,
    Nothing,
}

#[derive(Debug, Serialize, Deserialize)]
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
            println!(
                "{}{}",
                if self.line_offsets.contains_key(&i) {
                    format!("{:5} ", self.line_offsets[&i].blue())
                } else {
                    format!("    {} ", "|".blue())
                },
                format!("{:05} {:?}", i.red(), s)
            );
        }
        println!();
    }

    fn add(&mut self, op: Op, token_position: usize) -> usize {
        let mut len = self.curr();
        if matches!(op, Op::Pop) && len > 1 {
            len -= 1;
            match self.ops.last().unwrap() {
                Op::Copy(n) => {
                    if *n == 1 {
                        self.ops.pop();
                        return len - 1;
                    } else {
                        self.ops[len] = Op::Copy(*n - 1);
                        return len;
                    }
                }
                Op::Constant(_) | Op::ReadLocal(_) | Op::ReadUpvalue(_) => {
                    self.ops.pop();
                    return len - 1;
                }
                _ => {}
            }
        }
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

#[derive(Clone, Serialize, Deserialize)]
pub struct Prog {
    pub blocks: Vec<Rc<RefCell<Block>>>,
    #[serde(skip)]
    pub functions: Vec<RustFunction>,
    pub constants: Vec<Value>,
    pub strings: Vec<String>,
}

#[cfg(test)]
mod tests {
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

    use owo_colors::OwoColorize;
    use std::sync::mpsc;
    use std::thread;
    use std::time::Duration;

    // Shamelessly stolen from https://github.com/rust-lang/rfcs/issues/2798
    #[allow(dead_code)]
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
            Err(mpsc::RecvTimeoutError::Timeout) => "Test took too long to complete",
            Err(mpsc::RecvTimeoutError::Disconnected) => "Test produced incorrect result",
        };
        eprintln!("    #### {} ####", msg.red());
        panic!(msg);
    }

    #[macro_export]
    macro_rules! test_file {
        ($fn:ident, $path:literal, $print:expr) => {
            #[test]
            fn $fn() {
                let mut args = $crate::Args::default();
                args.file = Some(std::path::PathBuf::from($path));
                args.verbosity = if $print { 1 } else { 0 };
                $crate::run_file(
                    &args,
                    sylt_macro::link!(crate::dbg as dbg, crate::push as push, crate::len as len,),
                )
                .unwrap();
            }
        };
        ($fn:ident, $path:literal, $print:expr, $errs:tt) => {
            #[test]
            fn $fn() {
                use $crate::error::ErrorKind;
                #[allow(unused_imports)]
                use $crate::Type;

                let mut args = $crate::Args::default();
                args.file = Some(std::path::PathBuf::from($path));
                args.verbosity = if $print { 1 } else { 0 };
                let res = $crate::run_file(
                    &args,
                    sylt_macro::link!(crate::dbg as dbg, crate::push as push, crate::len as len,),
                );
                $crate::assert_errs!(res, $errs);
            }
        };
    }

    sylt_macro::find_tests!();
}

// The "standard library"
use crate as sylt;

pub fn dbg(values: &[Value], _typecheck: bool) -> Result<Value, ErrorKind> {
    println!(
        "{}: {:?}, {:?}",
        "DBG".purple(),
        values.iter().map(Type::from).collect::<Vec<_>>(),
        values
    );
    Ok(Value::Nil)
}

pub fn push(values: &[Value], typecheck: bool) -> Result<Value, ErrorKind> {
    match (values, typecheck) {
        ([Value::List(ls), v], true) => {
            let ls: &RefCell<_> = ls.borrow();
            let ls = &ls.borrow();
            assert!(ls.len() == 1);
            let ls = Type::from(&ls[0]);
            let v: Type = Type::from(&*v);
            if ls == v {
                Ok(Value::Nil)
            } else {
                Err(ErrorKind::TypeMismatch(ls, v))
            }
        }
        ([Value::List(ls), v], false) => {
            // NOTE(ed): Deliberately no type checking.
            let ls: &RefCell<_> = ls.borrow();
            ls.borrow_mut().push(v.clone());
            Ok(Value::Nil)
        }
        (values, _) => Err(ErrorKind::ExternTypeMismatch(
            "push".to_string(),
            values.iter().map(|x| Type::from(x)).collect(),
        )),
    }
}

sylt_macro::extern_function!(
    len
    [Value::List(ls)] -> Type::Int => {
        let ls: &RefCell<Vec<Value>> = ls.borrow();
        let ls = ls.borrow();
        Ok(Value::Int(ls.len() as i64))
    },
    [Value::Tuple(ls)] -> Type::Int => {
        Ok(Value::Int(ls.len() as i64))
    },
);
