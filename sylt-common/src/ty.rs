use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::hash::{Hash, Hasher};

use crate::{Blob, Value};

pub trait Numbered {
    fn to_number(&self) -> usize;
}

#[derive(Debug, Clone, sylt_macro::Numbered)]
#[derive(Deserialize, Serialize)]
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
            Type::Field(f) => f.hash(h),

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
            | Type::Invalid
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

fn maybe_union_from_type<'a>(v: impl Iterator<Item = &'a Value>) -> Type {
    let types: Vec<_> = v.map(Type::from).collect();
    Type::maybe_union(types.iter(), None)
}

impl From<&Value> for Type {
    fn from(value: &Value) -> Type {
        match value {
            Value::Field(s) => Type::Field(s.clone()),
            Value::Instance(b, _) => Type::Instance(*b),
            Value::Blob(b) => Type::Blob(*b),
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
        let mut same = HashSet::new();
        self.inner_fits(other, blobs, &mut same)
    }

    /// The type-comparison heavy-weight champion.
    /// Compares types recursively by proving they're not equal.
    fn inner_fits<'t>(
        &'t self,
        other: &'t Self,
        blobs: &'t [Blob],
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
            (Type::List(a), Type::List(b)) => a.inner_fits(b, blobs, same),
            (Type::Set(a), Type::Set(b)) => a.inner_fits(b, blobs, same),
            (Type::Dict(ak, av), Type::Dict(bk, bv)) => {
                ak.inner_fits(bk, blobs, same)?;
                av.inner_fits(bv, blobs, same)
            }
            (Type::Tuple(a), Type::Tuple(b)) => {
                for (i, (x, y)) in a.iter().zip(b).enumerate() {
                    if x.inner_fits(y, blobs, same).is_err() {
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
                    if x.inner_fits(y, blobs, same).is_err() {
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
                a_ret.inner_fits(b_ret, blobs, same)
            }
            (Type::Union(_), Type::Union(b)) => {
                if b.iter().any(|x| self.inner_fits(x, blobs, same).is_err()) {
                    Err(format!("'{:?}' doesn't fit a '{:?}'", self, other))
                } else {
                    Ok(())
                }
            }
            (Type::Instance(a), Type::Instance(b)) | (Type::Blob(a), Type::Blob(b)) => {
                if a == b {
                    return Ok(());
                }
                let a_fields = &blobs[*a].fields;
                let b_fields = &blobs[*b].fields;
                for (f, t) in a_fields.iter() {
                    if let Some(y) = b_fields.get(f) {
                        if t.inner_fits(y, blobs, same).is_err() {
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
                if !b.iter().all(|x| x.inner_fits(a, blobs, same).is_ok()) {
                    Err(format!("'{:?}' cannot fit a '{:?}'", self, other))
                } else {
                    Ok(())
                }
            }
            (Type::Union(a), b) => {
                if a.iter().any(|x| x.inner_fits(b, blobs, same).is_ok()) {
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

    pub fn maybe_union<'a, B>(tys: impl Iterator<Item = &'a Type>, blobs: B) -> Type
        where
            B: Into<Option<&'a [Blob]>>,

    {
        let blobs: Option<_> = blobs.into();
        let mut set = HashSet::new();
        for ty in tys {
            match blobs {
                None => {
                    set.insert(ty.clone());
                }
                Some(blobs) if !set.iter().any(|x| x.fits(ty, blobs).is_ok()) => {
                    set.insert(ty.clone());
                }
                _ => {}
            }
        }
        match set.len() {
            0 => Type::Unknown,
            1 => set.into_iter().next().unwrap(),
            _ => Type::Union(set),
        }
    }
}
