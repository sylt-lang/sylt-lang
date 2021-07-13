use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::{Type, UpValue, Value};

type FlatValueID = usize;

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum FlatValue {
    Field(String),
    Ty(Type),
    Blob(usize),
    Instance(usize, HashMap<String, FlatValueID>),
    Tuple(Vec<FlatValueID>),
    List(Vec<FlatValueID>),
    Set(HashSet<FlatValueID>),
    Dict(HashMap<FlatValueID, FlatValueID>),
    Float(f64),
    Int(i64),
    Bool(bool),
    String(String),
    Function(Vec<FlatUpValue>, Type, usize),
    ExternFunction(usize),
    Unknown,
    Nil,
}

impl FlatValue {
    fn pack(value: &Value, pack: &mut Vec<FlatValue>, seen: &mut HashMap<usize, FlatValueID>) -> FlatValueID {
        let ptr = value.unique_id();
        if seen.contains_key(&ptr) {
            return *seen.get(&ptr).unwrap();
        }

        let id = pack.len();
        seen.insert(ptr, id);
        pack.push(FlatValue::Nil);

        let val = match value {
            Value::Field(s) => FlatValue::Field(s.into()),
            Value::Ty(ty) => FlatValue::Ty(ty.clone()),
            Value::Blob(slot) => FlatValue::Blob(*slot),
            Value::Instance(ty_slot, values) => FlatValue::Instance(
                *ty_slot,
                values
                    .borrow()
                    .iter()
                    .map(|(field, value)| (field.clone(), Self::pack(value, pack, seen)))
                    .collect(),
            ),
            Value::Tuple(values) => FlatValue::Tuple(
                values.iter().map(|value| Self::pack(value, pack, seen)).collect(),
            ),
            Value::List(values) => FlatValue::List(
                values.borrow().iter().map(|value| Self::pack(value, pack, seen)).collect(),
            ),
            Value::Set(values) => FlatValue::Set(
                values.borrow().iter().map(|value| Self::pack(value, pack, seen)).collect(),
            ),
            Value::Dict(values) => FlatValue::Dict(
                values
                    .borrow()
                    .iter()
                    .map(|(v1, v2)| (Self::pack(v1, pack, seen), Self::pack(v2, pack, seen)))
                    .collect(),
            ),
            Value::Float(f) => FlatValue::Float(*f),
            Value::Int(i) => FlatValue::Int(*i),
            Value::Bool(b) => FlatValue::Bool(*b),
            Value::String(s) => FlatValue::String(String::clone(s)),
            Value::Function(captured, ty, slot) => FlatValue::Function(
                captured
                    .iter()
                    .map(|upvalue| FlatUpValue { slot: upvalue.borrow().slot, value: Self::pack(&upvalue.borrow().value, pack, seen) })
                    .collect(),
                ty.clone(),
                *slot,
            ),
            Value::ExternFunction(slot) => FlatValue::ExternFunction(*slot),
            Value::Unknown => FlatValue::Unknown,
            Value::Nil => FlatValue::Nil,
            Value::Union(_) => {
                unreachable!("Cannot send union values over the network");
            }
        };
        pack[id] = val;
        id
    }

    fn partial_unpack(value: FlatValue) -> Value {
        match value {
            FlatValue::Field(s) => Value::Field(s),
            FlatValue::Ty(ty) => Value::Ty(ty),
            FlatValue::Blob(slot) => Value::Blob(slot),
            FlatValue::Instance(ty_slot, _) => Value::Instance(
                ty_slot,
                Rc::new(RefCell::new(HashMap::new())),
            ),
            FlatValue::Tuple(_) => Value::Tuple(Rc::new(Vec::new())),
            FlatValue::List(_) => Value::List(Rc::new(RefCell::new(Vec::new()))),
            FlatValue::Set(_) => Value::Set(Rc::new(RefCell::new(HashSet::new()))),
            FlatValue::Dict(_) => Value::Dict(Rc::new(RefCell::new(HashMap::new()))),
            FlatValue::Float(f) => Value::Float(f),
            FlatValue::Int(i) => Value::Int(i),
            FlatValue::Bool(b) => Value::Bool(b),
            FlatValue::String(s) => Value::String(Rc::new(s)),
            FlatValue::Function(_, ty, slot) => Value::Function(
                Rc::new(Vec::new()),
                ty,
                slot,
            ),
            FlatValue::ExternFunction(slot) => Value::ExternFunction(slot),
            FlatValue::Unknown => Value::Unknown,
            FlatValue::Nil => Value::Nil,
        }
    }

    fn unpack(pack: &mut Vec<FlatValue>) -> Value {
        let mut mapping: Vec<Value> = pack.iter().cloned().map(Self::partial_unpack).collect();
        for (i, x) in mapping.iter().enumerate().rev() {
            match (&pack[i], x) {
                (FlatValue::Instance(_, flat), Value::Instance(_, values)) => {
                    let mut values = values.borrow_mut();
                    for (key, id) in flat {
                        values.insert(key.clone(), mapping[*id].clone());
                    }
                }
                (FlatValue::Tuple(flat), Value::Tuple(values)) => {
                    let values = unsafe { (Rc::as_ptr(values) as *mut Vec<Value>).as_mut() }.unwrap();
                    for id in flat {
                        values.push(mapping[*id].clone());
                    }
                }
                (FlatValue::List(flat), Value::List(values)) => {
                    let mut values = values.borrow_mut();
                    for id in flat {
                        values.push(mapping[*id].clone());
                    }
                }
                (FlatValue::Set(flat), Value::Set(values)) => {
                    let mut values = values.borrow_mut();
                    for id in flat {
                        values.insert(mapping[*id].clone());
                    }
                }
                (FlatValue::Dict(flat), Value::Dict(values)) => {
                    let mut values = values.borrow_mut();
                    for (key_id, value_id) in flat {
                        values.insert(mapping[*key_id].clone(), mapping[*value_id].clone());
                    }
                }
                (FlatValue::Function(flat, _, _), Value::Function(values, _, _)) => {
                    let values = unsafe { (Rc::as_ptr(values) as *mut Vec<Rc<RefCell<UpValue>>>).as_mut() }.unwrap();
                    for up in flat {
                        values.push(Rc::new(RefCell::new(UpValue { slot: up.slot, value: mapping[up.value].clone() })));
                    }
                }
                _ => {}
            }
        }

        mapping.remove(0)
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct FlatUpValue {
    slot: usize,
    value: FlatValueID,
}

