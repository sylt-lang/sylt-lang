use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::{Type, UpValue, Value};

#[derive(Clone, Debug, Deserialize, Serialize)]
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
            OwnedValue::Instance(ty_slot, values) => Value::Instance(
                ty_slot,
                Rc::new(RefCell::new(
                    values
                        .into_iter()
                        .map(|(field, value)| (field, value.into()))
                        .collect(),
                )),
            ),
            OwnedValue::Tuple(values) => Value::Tuple(Rc::new(
                values.into_iter().map(|value| value.into()).collect(),
            )),
            OwnedValue::List(values) => Value::List(Rc::new(RefCell::new(
                values.into_iter().map(|value| value.into()).collect(),
            ))),
            OwnedValue::Set(values) => Value::Set(Rc::new(RefCell::new(
                values.into_iter().map(|value| value.into()).collect(),
            ))),
            OwnedValue::Dict(values) => Value::Dict(Rc::new(RefCell::new(
                values
                    .into_iter()
                    .map(|(v1, v2)| (v1.into(), v2.into()))
                    .collect(),
            ))),
            OwnedValue::Union(values) => {
                Value::Union(values.into_iter().map(|value| value.into()).collect())
            }
            OwnedValue::Float(f) => Value::Float(f),
            OwnedValue::Int(i) => Value::Int(i),
            OwnedValue::Bool(b) => Value::Bool(b),
            OwnedValue::String(s) => Value::String(Rc::new(s)),
            OwnedValue::Function(captured, ty, slot) => Value::Function(
                Rc::new(
                    captured
                        .into_iter()
                        .map(|param| Rc::new(RefCell::new(param.into())))
                        .collect(),
                ),
                ty,
                slot,
            ),
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
            Value::Instance(ty_slot, values) => OwnedValue::Instance(
                *ty_slot,
                values
                    .borrow()
                    .iter()
                    .map(|(field, value)| (field.clone(), value.into()))
                    .collect(),
            ),
            Value::Tuple(values) => {
                OwnedValue::Tuple(values.iter().map(|value| value.into()).collect())
            }
            Value::List(values) => {
                OwnedValue::List(values.borrow().iter().map(|value| value.into()).collect())
            }
            Value::Set(values) => {
                OwnedValue::Set(values.borrow().iter().map(|value| value.into()).collect())
            }
            Value::Dict(values) => OwnedValue::Dict(
                values
                    .borrow()
                    .iter()
                    .map(|(v1, v2)| (v1.into(), v2.into()))
                    .collect(),
            ),
            Value::Union(values) => {
                OwnedValue::Union(values.iter().map(|value| value.into()).collect())
            }
            Value::Float(f) => OwnedValue::Float(*f),
            Value::Int(i) => OwnedValue::Int(*i),
            Value::Bool(b) => OwnedValue::Bool(*b),
            Value::String(s) => OwnedValue::String(String::clone(s)),
            Value::Function(captured, ty, slot) => OwnedValue::Function(
                captured
                    .iter()
                    .map(|param| (&*param.borrow()).into())
                    .collect(),
                ty.clone(),
                *slot,
            ),
            Value::ExternFunction(slot) => OwnedValue::ExternFunction(*slot),
            Value::Unknown => OwnedValue::Unknown,
            Value::Nil => OwnedValue::Nil,
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct OwnedUpValue {
    slot: usize,
    value: OwnedValue,
}

impl From<OwnedUpValue> for UpValue {
    fn from(value: OwnedUpValue) -> Self {
        Self {
            slot: value.slot,
            value: value.value.into(),
        }
    }
}

impl From<&UpValue> for OwnedUpValue {
    fn from(value: &UpValue) -> Self {
        Self {
            slot: value.slot,
            value: (&value.value).into(),
        }
    }
}
