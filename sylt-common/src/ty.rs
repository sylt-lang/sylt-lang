use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::hash::Hash;
use std::fmt::{Debug, Display};

use crate::{Blob, Value};

pub trait Numbered {
    fn to_number(&self) -> usize;
}

#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd, sylt_macro::Numbered)]
#[derive(Deserialize, Serialize)]
pub enum Type {
    Ty,
    Generic(String),
    Void,
    Unknown,
    Int,
    Float,
    Bool,
    String,
    Tuple(Vec<Type>),
    Union(BTreeSet<Type>),
    List(Box<Type>),
    Set(Box<Type>),
    Dict(Box<Type>, Box<Type>),
    Function(Vec<Type>, Box<Type>),
    Blob(String, BTreeMap<String, Type>),
    Instance(String, BTreeMap<String, Type>),
    ExternFunction(usize),

    Invalid,
}

impl Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Ty => write!(f, "Type"),
            Type::Generic(name) => write!(f, "#{}", name),
            Type::Void => write!(f, "void"),
            Type::Unknown => write!(f, "?"),
            Type::Int => write!(f, "int"),
            Type::Float => write!(f, "float"),
            Type::Bool => write!(f, "bool"),
            Type::String => write!(f, "str"),
            Type::Tuple(names) => {
                write!(f, "(")?;
                for (i, n) in names.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", n)?;
                }
                write!(f, ")")
            }
            Type::Union(names) => {
                for (i, n) in names.iter().enumerate() {
                    if i != 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{}", n)?;
                }
                Ok(())
            }
            Type::List(name) => write!(f, "[{}]", name),
            Type::Set(name) => write!(f, "{{{}}}", name),
            Type::Dict(key, value) => write!(f, "{{{}: {}}}", key, value),
            Type::Function(args, ret) => {
                write!(f, "fn ")?;
                for (i, n) in args.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", n)?;
                }
                write!(f, " -> {}", ret)
            }
            Type::Blob(..) => write!(f, "TODO"),
            Type::Instance(..) => write!(f, "TODO"),
            Type::ExternFunction(id) => write!(f, "ExternFunction({})", id),
            Type::Invalid => write!(f, "Invalid"),
        }
    }
}

fn maybe_union_from_type<'a>(v: impl Iterator<Item = &'a Value>) -> Type {
    let types: Vec<_> = v.map(Type::from).collect();
    Type::maybe_union(types.iter())
}

impl From<&Value> for Type {
    fn from(value: &Value) -> Type {
        match value {
            Value::Instance(f) => Type::Blob("anonymous".to_string(), f.borrow()
                .iter()
                .map(|(n, v)| (n.clone(), v.into()))
                .collect()),
            Value::Blob(b) => b.clone(),
            Value::Tuple(v) => Type::Tuple(v.iter().map(Type::from).collect()),
            Value::List(v) => {
                let t = maybe_union_from_type(v.borrow().iter());
                Type::List(Box::new(t))
            }
            Value::Set(v) => {
                let t = maybe_union_from_type(v.borrow().iter());
                Type::Set(Box::new(t))
            }
            Value::Dict(v) => {
                let v = v.borrow();
                let k = maybe_union_from_type(v.keys());
                let v = maybe_union_from_type(v.values());
                Type::Dict(Box::new(k), Box::new(v))
            }
            Value::Int(_) => Type::Int,
            Value::Float(_) => Type::Float,
            Value::Bool(_) => Type::Bool,
            Value::String(_) => Type::String,
            Value::Function(_, ty, _) => ty.clone(),
            Value::ExternFunction(n) => Type::ExternFunction(*n),
            Value::Nil => Type::Void,
            Value::Ty(_) => Type::Ty,
        }
    }
}

impl From<Value> for Type {
    fn from(value: Value) -> Type {
        Type::from(&value)
    }
}

impl Type {
    // TODO(ed): Swap order of arguments
    /// Checks if the other type is valid in a place where the self type is. It's an asymmetrical
    /// comparison for types useful when checking assignment.
    pub fn fits(&self, other: &Self) -> Result<(), String> {
        let mut same = HashSet::new();
        self.inner_fits(other, &mut same)
    }

    /// The type-comparison heavy-weight champion.
    /// Compares types recursively by proving they're not equal.
    fn inner_fits<'t>(
        &'t self,
        other: &'t Self,
        same: &mut HashSet<(&'t Type, &'t Type)>
    ) -> Result<(), String> {

        // If we've seen the pair before - they have to match,
        // otherwise it isn't done and will fail later. We don't
        // need to do (infinitely) more work.
        if same.contains(&(self, other)) {
            return Ok(());
        }
        same.insert((self, other));

        match (self, other) {
            (Type::Unknown, _) | (_, Type::Unknown) => Ok(()),
            (Type::List(a), Type::List(b)) => a.inner_fits(b, same),
            (Type::Set(a), Type::Set(b)) => a.inner_fits(b, same),
            (Type::Dict(ak, av), Type::Dict(bk, bv)) => {
                ak.inner_fits(bk, same)?;
                av.inner_fits(bv, same)
            }
            (Type::Tuple(a), Type::Tuple(b)) => {
                for (i, (x, y)) in a.iter().zip(b).enumerate() {
                    if x.inner_fits(y, same).is_err() {
                        return Err(
                            format!(
                                "'{:?}' is not a '{:?}', element #{} has type '{:?}' but expected '{:?}'",
                                self,
                                other,
                                i,
                                y,
                                x
                            ));
                    }
                }
                Ok(())
            }
            (Type::Function(a_args, a_ret), Type::Function(b_args, b_ret)) => {
                for (i, (x, y)) in a_args.iter().zip(b_args).enumerate() {
                    if x.inner_fits(y, same).is_err() {
                        return Err(
                            format!(
                                "'{:?}' is not a '{:?}', argument #{} has type '{:?}' but expected '{:?}'",
                                self,
                                other,
                                i,
                                y,
                                x
                        ));
                    }
                }
                if a_args.len() != b_args.len() {
                    return Err(
                        format!(
                            "mismatching arity, {} != {}",
                            a_args.len(),
                            b_args.len()
                        ));
                }
                a_ret.inner_fits(b_ret, same)
            }
            (Type::Union(_), Type::Union(b)) => {
                if let Err(msg) = b.iter().map(|x| self.inner_fits(x, same)).collect::<Result<Vec<_>, _>>() {
                    Err(format!("'{:?}' doesn't fit a '{:?}, because {}'", self, other, msg))
                } else {
                    Ok(())
                }
            }

            | (Type::Instance(an, a), Type::Instance(bn, b))
            | (Type::Blob(an, a), Type::Blob(bn, b)) => {
                if a == b {
                    return Ok(());
                }
                for (f, t) in a.iter() {
                    if let Some(y) = b.get(f) {
                        if t.inner_fits(y, same).is_err() {
                            return Err(
                                format!(
                                    "'{}' is not a '{}', field '{:?}' has type '{:?}' but expected '{:?}'",
                                    an,
                                    bn,
                                    f,
                                    y,
                                    t
                            ));
                        }
                    } else {
                        return Err(format!(
                            "'{:?}' is not a '{:?}', '{:?}' has no field '{:?}'",
                            an, bn, bn, f
                        ));
                    }
                }
                Ok(())
            }
            (a, Type::Union(b)) => {
                if !b.iter().all(|x| x.inner_fits(a, same).is_ok()) {
                    Err(format!("'{:?}' cannot fit a union '{:?}'", self, other))
                } else {
                    Ok(())
                }
            }
            (Type::Union(a), b) => {
                if a.iter().any(|x| x.inner_fits(b, same).is_ok()) {
                    Ok(())
                } else {
                    Err(format!("Union '{:?}' cannot fit a '{:?}'", self, other))
                }
            }
            (a, b) => {
                if a == b {
                    Ok(())
                } else {
                    Err(format!("'{:?}' is not a '{:?}'", b, a))
                }
            }
        }
    }

    pub fn is_nil(&self) -> bool {
        matches!(self, Type::Void | Type::Invalid)
    }

    pub fn is_number(&self) -> bool {
        matches!(self, Type::Int | Type::Float)
    }

    pub fn maybe_union<'a>(tys: impl Iterator<Item = &'a Type>) -> Type {
        let mut set = BTreeSet::<Type>::new();
        for ty in tys {
            // Invalid types cannot be unioned
            if matches!(ty, Type::Invalid) {
                return Type::Invalid;
            }
            if !set.iter().any(|x| x.fits(ty).is_ok()) {
                set.insert(ty.clone());
            }
        }
        match set.len() {
            0 => Type::Unknown,
            1 => set.into_iter().next().unwrap(),
            _ => Type::Union(set),
        }
    }
}
