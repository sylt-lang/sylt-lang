use std::collections::HashMap;

use crate::Type;

// TODO(ed): We need to rewrite this with indexes to this struct instead
// of an RC - otherwise we cannot support all recursive types.
#[derive(Debug, Clone)]
pub struct Blob {
    pub id: usize,
    pub namespace: usize,
    pub name: String,
    /// Maps field names to their type
    pub fields: HashMap<String, Type>,
}

impl PartialEq for Blob {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Blob {
    pub fn new(id: usize, namespace: usize, name: &str) -> Self {
        Self {
            id,
            namespace,
            name: String::from(name),
            fields: HashMap::new(),
        }
    }
}
