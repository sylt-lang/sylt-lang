use std::collections::HashMap;
use sylt_common::error::{Error, Helper, TypeError};
use sylt_common::{FileOrLib, TyID, Type as RuntimeType};
use sylt_parser::{
    expression::ComparisonKind, Assignable, AssignableKind, Expression, ExpressionKind, Identifier,
    Op as ParserOp, Span, Statement, StatementKind, Type as ParserType, TypeAssignable,
    TypeAssignableKind, TypeConstraint, TypeKind, VarKind,
};

use crate::{ty::Type, NamespaceID, typechecker::TypeChecker};

#[derive(Debug, Clone)]
pub enum IR {
    Nop,
    Int(i64),
    AddInt,
}

struct IRCodeGen<'a> {
    typechecker: &'a TypeChecker,
    namespace_to_file: HashMap<NamespaceID, FileOrLib>,
    // TODO(ed): This can probably be removed via some trickery
    file_to_namespace: HashMap<FileOrLib, NamespaceID>,
}

impl<'a> IRCodeGen<'a> {
    fn new(
        typechecker: &'a TypeChecker,
        namespace_to_file: &HashMap<NamespaceID, FileOrLib>,
    ) -> Self {
        Self {
            typechecker,
            namespace_to_file: namespace_to_file.clone(),
            file_to_namespace: namespace_to_file
                .iter()
                .map(|(a, b)| (b.clone(), a.clone()))
                .collect(),
        }
    }

    fn compile(&mut self, stmt: &Statement, namespace: NamespaceID) -> Vec<IR> {
        Vec::new()
    }
}

pub(crate) fn compile(
    typechecker: &TypeChecker,
    statements: &Vec<(Statement, NamespaceID)>,
    namespace_to_file: &HashMap<NamespaceID, FileOrLib>,
) -> Vec<IR> {
    let mut gen = IRCodeGen::new(typechecker, namespace_to_file);
    statements
        .iter()
        .map(|(stmt, namespace)| gen.compile(stmt, *namespace))
        .flatten()
        .collect()
}
