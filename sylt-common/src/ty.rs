use std::collections::HashSet;
use std::hash::{Hash, Hasher};

use crate::{Blob, Value};

pub trait Numbered {
    fn to_number(&self) -> usize;
}

#[derive(Debug, Clone, sylt_macro::Numbered)]
pub enum Type {
    Ty,
    Field(String),
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
    Blob(usize),
    Instance(usize),
    ExternFunction(usize),

    Invalid,
}

impl Hash for Type {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.to_number().hash(h);
        match self {
            Type::Field(_) | Type::Invalid => unimplemented!(),

            Type::List(t) | Type::Set(t)
                => t.as_ref().hash(h),

            Type::Tuple(ts) => {
                for t in ts.iter() {
                    t.hash(h);
                }
            }
            Type::Dict(k, v) => {
                k.as_ref().hash(h);
                v.as_ref().hash(h);
            }
            Type::Union(ts) => {
                for t in ts {
                    t.hash(h);
                }
            }
            Type::Function(args, ret) => {
                ret.hash(h);
                for t in args.iter() {
                    t.hash(h);
                }
            }
            Type::Blob(b) | Type::Instance(b) => b.hash(h),

            Type::Ty
            | Type::Void
            | Type::Unknown
            | Type::Int
            | Type::Float
            | Type::Bool
            | Type::ExternFunction(..)
            | Type::String => {}
        }
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
    let set: HashSet<_> = v.map(Type::from).collect();
    match set.len() {
        0 => Type::Unknown,
        1 => set.into_iter().next().unwrap(),
        _ => Type::Union(set),
    }
}

impl From<&Value> for Type {
    fn from(value: &Value) -> Type {
        match value {
            Value::Field(s) => Type::Field(s.clone()),
            Value::Instance(b, _) => Type::Instance(*b),
            Value::Blob(b) => Type::Blob(*b),
            Value::Tuple(v) => Type::Tuple(v.iter().map(Type::from).collect()),
            Value::List(v) => {
                let t = maybe_union_type(v.borrow().iter());
                Type::List(Box::new(t))
            }
            Value::Set(v) => {
                let t = maybe_union_type(v.borrow().iter());
                Type::Set(Box::new(t))
            }
            Value::Dict(v) => {
                let v = v.borrow();
                let k = maybe_union_type(v.keys());
                let v = maybe_union_type(v.values());
                Type::Dict(Box::new(k), Box::new(v))
            }
            Value::Union(v) => Type::Union(v.iter().map(Type::from).collect()),
            Value::Int(_) => Type::Int,
            Value::Float(_) => Type::Float,
            Value::Bool(_) => Type::Bool,
            Value::String(_) => Type::String,
            Value::Function(_, ty, _) => ty.clone(),
            Value::Unknown => Type::Unknown,
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
    pub fn fits(&self, other: &Self, blobs: &[Blob]) -> Result<(), String> {
        match (self, other) {
            (Type::Unknown, _) | (_, Type::Unknown) => Ok(()),
            (Type::List(a), Type::List(b)) => a.fits(b, blobs),
            (Type::Set(a), Type::Set(b)) => a.fits(b, blobs),
            (Type::Dict(ak, av), Type::Dict(bk, bv)) => {
                ak.fits(bk, blobs)?;
                av.fits(bv, blobs)
            }
            (Type::Union(_), Type::Union(b)) => {
                // NOTE(ed): Does this cause infinite recursion?
                if b.iter().any(|x| self.fits(x, blobs).is_err()) {
                    Err(format!("'{:?}' doesn't fit a '{:?}'", self, other))
                } else {
                    Ok(())
                }
            }
            (Type::Instance(a), Type::Instance(b)) => {
                let a_fields = &blobs[*a].fields;
                let b_fields = &blobs[*b].fields;
                for (f, t) in a_fields.iter() {
                    if let Some(y) = b_fields.get(f) {
                        // NOTE(ed): It might be tempting to put a `fits`
                        // call here. Don't! It will cause infinite recursion
                        // if a type that has itself as a field in any way.
                        if t != y {
                            return Err(
                                format!(
                                    "'{}' is not a '{}', field '{:?}' has type '{:?}' but expected '{:?}'",
                                    blobs[*a].name,
                                    blobs[*b].name,
                                    f,
                                    y,
                                    t
                            ));
                        }
                    } else {
                        return Err(format!(
                            "'{:?}' is not a '{:?}', '{:?}' has no field '{:?}'",
                            blobs[*a].name, blobs[*b].name, blobs[*b].name, f
                        ));
                    }
                }
                Ok(())
            }
            (a, Type::Union(b)) => {
                if !b.iter().all(|x| x == a) {
                    Err(format!("'{:?}' cannot fit a '{:?}'", a, other))
                } else {
                    Ok(())
                }
            }
            (Type::Union(a), b) => {
                if a.iter().any(|x| x == b) {
                    Ok(())
                } else {
                    Err(format!("'{:?}' cannot fit a '{:?}'", self, other))
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

    pub fn maybe_union<'a>(v: impl Iterator<Item = &'a Type>) -> Type {
        let set: HashSet<_> = v.cloned().collect();
        match set.len() {
            0 => Type::Unknown,
            1 => set.into_iter().next().unwrap(),
            _ => Type::Union(set),
        }
    }
}
