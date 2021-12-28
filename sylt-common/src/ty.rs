use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{Debug, Display};
use std::hash::Hash;

pub trait Numbered {
    fn to_number(&self) -> usize;
}

#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd, sylt_macro::Numbered)]
pub enum Type {
    Ty,
    Generic(String),
    Void,
    Nil,
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
    Enum(String, BTreeMap<String, Type>),
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
            Type::Nil => write!(f, "nil"),
            Type::Unknown => write!(f, "*"),
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
                write!(f, "(fn ")?;
                for (i, n) in args.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", n)?;
                }
                write!(f, " -> {})", ret)
            }
            Type::Blob(name, _) => write!(f, "{}", name),
            Type::Enum(name, _) => write!(f, "{}", name),
            Type::ExternFunction(id) => write!(f, "ExternFunction({})", id),
            Type::Invalid => write!(f, "Invalid"),
        }
    }
}
