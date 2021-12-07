pub mod error;
pub mod ty;
pub mod value;

use std::path::PathBuf;

pub use error::Error;
pub use ty::Type;
pub use value::Value;

#[derive(Eq, PartialEq, Ord, PartialOrd, Debug, Clone, Copy, Hash)]
pub struct TyID(pub usize);

impl std::fmt::Display for TyID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let TyID(id) = self;
        write!(f, "TyID({})", id)
    }
}

/// Differentiates lib imports and file imports
#[derive(Hash, Eq, PartialEq, PartialOrd, Clone, Debug)]
pub enum FileOrLib {
    File(PathBuf),
    Lib(&'static str),
}

/// The standard library
const STD_LIB_FILES: &[(&str, &str)] = &[("std", include_str!("../../std/std.sy"))];

pub fn library_name(name: &str) -> Option<&'static str> {
    STD_LIB_FILES
        .iter()
        .find(|(x, _)| x == &name)
        .map(|(p, _)| *p)
}

pub fn library_source(name: &str) -> Option<&'static str> {
    STD_LIB_FILES
        .iter()
        .find(|(x, _)| x == &name)
        .map(|(_, s)| *s)
}
