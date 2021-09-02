use std::collections::HashMap;
use crate::Compiler;
use sylt_parser::{
    AST, Expression, Statement, StatementKind,
};

struct Context {
}

pub(crate) fn initialization_order<'a>(tree: &'a AST, compiler: &Compiler) -> Vec<&'a Statement> {
    let path_to_namespace_id: HashMap<_, _> = compiler.namespace_id_to_path
        .iter()
        .map(|(a, b)| (b.clone(), *a))
        .collect();
    let globals: Vec<_> = compiler.namespaces.iter()
        .map(|ns| ns.values())
        .flatten()
        .collect();
    dbg!(globals);
    for (path, module) in tree.modules.iter() {
        let namespace = path_to_namespace_id.get(path).unwrap();
        for statement in module.statements.iter() {
            use StatementKind::*;
            match &statement.kind {
                Definition { ident, value, .. } => {
                    dbg!(ident);
                }
                _ => {}
            }
        }
    }
    Vec::new()
}
