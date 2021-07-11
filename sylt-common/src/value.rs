use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::upvalue::OwnedUpValue;
use crate::{ty::Type, upvalue::UpValue};

#[derive(Clone)]
#[derive(Deserialize, Serialize)]
pub enum Value {
    Field(String),
    Ty(Type),
    Blob(usize),
    Instance(usize, Rc<RefCell<HashMap<String, Value>>>),
    Tuple(Rc<Vec<Value>>),
    List(Rc<RefCell<Vec<Value>>>),
    Set(Rc<RefCell<HashSet<Value>>>),
    Dict(Rc<RefCell<HashMap<Value, Value>>>),
    Union(HashSet<Value>),
    Float(f64),
    Int(i64),
    Bool(bool),
    String(Rc<String>),
    Function(Rc<Vec<Rc<RefCell<UpValue>>>>, Type, usize),
    ExternFunction(usize),
    /// This value should not be present when running, only when type checking.
    /// Most operations are valid but produce funky results.
    Unknown,
    /// Should not be present when running.
    Nil,
}

#[derive(Clone, Debug)]
#[derive(Deserialize, Serialize)]
pub enum OwnedValue {
    Field(String),
    Ty(Type),
    Blob(usize),
    Instance(usize, HashMap<String, OwnedValue>),
    Tuple(Vec<OwnedValue>),
    List(Vec<OwnedValue>),
    Set(HashSet<OwnedValue>),
    Dict(HashMap<OwnedValue, OwnedValue>),
    Union(HashSet<OwnedValue>),
    Float(f64),
    Int(i64),
    Bool(bool),
    String(String),
    Function(Vec<OwnedUpValue>, Type, usize),
    ExternFunction(usize),
    Unknown,
    Nil,
}

impl PartialEq for OwnedValue {
    fn eq(&self, other: &Self) -> bool {
        Value::from(self.clone()).eq(&Value::from(other.clone()))
    }
}

impl Eq for OwnedValue {}

impl Hash for OwnedValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Value::from(self.clone()).hash(state)
    }
}

impl From<OwnedValue> for Value {
    fn from(value: OwnedValue) -> Self {
        match value {
            OwnedValue::Field(s) => Value::Field(s),
            OwnedValue::Ty(ty) => Value::Ty(ty),
            OwnedValue::Blob(slot) => Value::Blob(slot),
            OwnedValue::Instance(ty_slot, values) => Value::Instance(ty_slot, Rc::new(RefCell::new(values.into_iter().map(|(field, value)| (field, value.into())).collect()))),
            OwnedValue::Tuple(values) => Value::Tuple(Rc::new(values.into_iter().map(|value| value.into()).collect())),
            OwnedValue::List(values) => Value::List(Rc::new(RefCell::new(values.into_iter().map(|value| value.into()).collect()))),
            OwnedValue::Set(values) => Value::Set(Rc::new(RefCell::new(values.into_iter().map(|value| value.into()).collect()))),
            OwnedValue::Dict(values) => Value::Dict(Rc::new(RefCell::new(values.into_iter().map(|(v1, v2)| (v1.into(), v2.into())).collect()))),
            OwnedValue::Union(values) => Value::Union(values.into_iter().map(|value| value.into()).collect()),
            OwnedValue::Float(f) => Value::Float(f),
            OwnedValue::Int(i) => Value::Int(i),
            OwnedValue::Bool(b) => Value::Bool(b),
            OwnedValue::String(s) => Value::String(Rc::new(s)),
            OwnedValue::Function(captured, ty, slot) => Value::Function(Rc::new(captured.into_iter().map(|param| Rc::new(RefCell::new(param.into()))).collect()), ty, slot),
            OwnedValue::ExternFunction(slot) => Value::ExternFunction(slot),
            OwnedValue::Unknown => Value::Unknown,
            OwnedValue::Nil => Value::Nil,
        }
    }
}

impl From<&Value> for OwnedValue {
    fn from(value: &Value) -> Self {
        match value {
            Value::Field(s) => OwnedValue::Field(s.clone()),
            Value::Ty(ty) => OwnedValue::Ty(ty.clone()),
            Value::Blob(slot) => OwnedValue::Blob(*slot),
            Value::Instance(ty_slot, values) => OwnedValue::Instance(*ty_slot, values.borrow().iter().map(|(field, value)| (field.clone(), value.into())).collect()),
            Value::Tuple(values) => OwnedValue::Tuple(values.iter().map(|value| value.into()).collect()),
            Value::List(values) => OwnedValue::List(values.borrow().iter().map(|value| value.into()).collect()),
            Value::Set(values) => OwnedValue::Set(values.borrow().iter().map(|value| value.into()).collect()),
            Value::Dict(values) => OwnedValue::Dict(values.borrow().iter().map(|(v1, v2)| (v1.into(), v2.into())).collect()),
            Value::Union(values) => OwnedValue::Union(values.iter().map(|value| value.into()).collect()),
            Value::Float(f) => OwnedValue::Float(*f),
            Value::Int(i) => OwnedValue::Int(*i),
            Value::Bool(b) => OwnedValue::Bool(*b),
            Value::String(s) => OwnedValue::String(String::clone(s)),
            Value::Function(captured, ty, slot) => OwnedValue::Function(captured.iter().map(|param| (&*param.borrow()).into()).collect(), ty.clone(), *slot),
            Value::ExternFunction(slot) => OwnedValue::ExternFunction(*slot),
            Value::Unknown => OwnedValue::Unknown,
            Value::Nil => OwnedValue::Nil,
        }
    }
}

impl From<&Type> for Value {
    fn from(ty: &Type) -> Self {
        match ty {
            Type::Field(s) => Value::Field(s.clone()),
            Type::Void => Value::Nil,
            Type::Blob(b) => Value::Blob(*b),
            Type::Instance(b) => Value::Instance(*b, Rc::new(RefCell::new(HashMap::new()))),
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
            Type::Unknown | Type::Invalid => Value::Unknown,
            Type::Int => Value::Int(1),
            Type::Float => Value::Float(1.0),
            Type::Bool => Value::Bool(true),
            Type::String => Value::String(Rc::new("".to_string())),
            Type::Function(a, r) => {
                Value::Function(Rc::new(Vec::new()), Type::Function(a.clone(), r.clone()), 0)
            }
            Type::ExternFunction(x) => Value::ExternFunction(*x),
            Type::Ty => Value::Ty(Type::Void),
        }
    }
}

impl From<Type> for Value {
    fn from(ty: Type) -> Self {
        Value::from(&ty)
    }
}

impl Debug for Value {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO(ed): This needs some cleaning
        match self {
            Value::Field(s) => write!(fmt, "( .{} )", s),
            Value::Ty(ty) => write!(fmt, "(type {:?})", ty),
            Value::Blob(b) => write!(fmt, "(blob b{})", b),
            Value::Instance(b, v) => write!(fmt, "(inst b{} {:?})", b, v),
            Value::Float(f) => write!(fmt, "(float {})", f),
            Value::Int(i) => write!(fmt, "(int {})", i),
            Value::Bool(b) => write!(fmt, "(bool {})", b),
            Value::String(s) => write!(fmt, "(string \"{}\")", s),
            Value::List(v) => write!(fmt, "(array {:?})", v),
            Value::Set(v) => write!(fmt, "(set {:?})", v),
            Value::Dict(v) => write!(fmt, "(dict {:?})", v),
            Value::Function(_, ty, block) => {
                write!(fmt, "(fn #{} {:?})", block, ty)
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
            (Value::Tuple(a), Value::Tuple(b)) => {
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| a == b)
            }
            (Value::List(a), Value::List(b)) => a == b,
            (Value::Set(a), Value::Set(b)) => a == b,
            (Value::Dict(a), Value::Dict(b)) => a == b,
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
    pub fn is_nil(&self) -> bool {
        matches!(self, Value::Nil)
    }
}

#[derive(Clone)]
pub enum MatchableValue<'t> {
    Empty,
    One(&'t Value),
    Two(&'t Value, &'t Value),
    Three(&'t Value, &'t Value, &'t Value),
    Four(&'t Value, &'t Value, &'t Value, &'t Value),
    Five(&'t Value, &'t Value, &'t Value, &'t Value, &'t Value),
}

pub fn make_matchable<'t>(value: &'t Value) -> MatchableValue<'t> {
    use MatchableValue::*;
    use Value::*;

    match value {
        #[rustfmt::skip]
        Tuple(inner) => {
            match (inner.get(0), inner.get(1), inner.get(2), inner.get(3), inner.get(4)) {
                (Some(a), Some(b), Some(c), Some(d), Some(e), ..) => Five(a, b, c, d, e),
                (Some(a), Some(b), Some(c), Some(d), ..) => Four(a, b, c, d),
                (Some(a), Some(b), Some(c), ..) => Three(a, b, c),
                (Some(a), Some(b), ..) => Two(a, b),
                (Some(a), ..) => One(a),
                _ => Empty,
            }
        },
        x => One(x),
    }
}
