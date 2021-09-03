use std::collections::{HashMap, HashSet};
use crate::{Compiler, Name};
use sylt_parser::{
    AST, Expression, Statement, StatementKind,
};

struct Context<'a> {
    compiler: &'a Compiler,
    namespace: usize,
}

fn dependencies(ctx: &Context, expression: &Expression) -> HashSet<Name> {
    use sylt_parser::ExpressionKind::*;
    match &expression.kind {
        Get(assignable) => {
            match &assignable.kind {
                sylt_parser::AssignableKind::Read(ident) => {
                    // Might be shadowed here
                    dbg!(&ident.name);
                    match ctx.compiler.namespaces[ctx.namespace].get(&ident.name) {
                        Some(&name) => [name].iter().cloned().collect(),
                        None => HashSet::new(),
                    }
                },
                sylt_parser::AssignableKind::Call(_, _) => todo!(),
                sylt_parser::AssignableKind::ArrowCall(_, _, _) => todo!(),
                sylt_parser::AssignableKind::Access(_, _) => todo!(),
                sylt_parser::AssignableKind::Index(_, _) => todo!(),
                sylt_parser::AssignableKind::Expression(_) => todo!(),
            }
        },

        | Neg(expr)
        | Not(expr) => dependencies(ctx, expr),

        | Add(lhs, rhs)
        | Sub(lhs, rhs)
        | Mul(lhs, rhs)
        | Div(lhs, rhs)
        | Is(lhs, rhs)
        | Eq(lhs, rhs)
        | Neq(lhs, rhs)
        | Gt(lhs, rhs)
        | Gteq(lhs, rhs)
        | Lt(lhs, rhs)
        | Lteq(lhs, rhs)
        | AssertEq(lhs, rhs)
        | In(lhs, rhs)
        | And(lhs, rhs)
        | Or(lhs, rhs) => dependencies(ctx, lhs)
            .union(&dependencies(ctx, rhs))
            .cloned()
            .collect(),

        IfExpression { condition, pass, fail } => todo!(),
        Duplicate(_) => todo!(),
        IfShort { lhs, condition, fail } => todo!(),
        Function { name, params, ret, body } => HashSet::new(),
        Instance { blob, fields } => todo!(),

        Tuple(_) => todo!(),
        List(_) => todo!(),
        Set(_) => todo!(),
        Dict(_) => todo!(),

        // No dependencies
        | TypeConstant(_)
        | Float(_)
        | Int(_)
        | Str(_)
        | Bool(_)
        | Nil => HashSet::new(),
    }
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
    for (path, module) in tree.modules.iter() {
        let namespace = *path_to_namespace_id.get(path).unwrap();
        let globals: Vec<_> = compiler.namespaces[namespace]
            .iter()
            .map(|(name, _global)| name)
            .cloned()
            .collect();
        dbg!(globals);
        for statement in module.statements.iter() {
            use StatementKind::*;
            match &statement.kind {
                Definition { ident, value, .. } => {
                    dbg!(
                        &ident.name,
                        dependencies(&Context{compiler, namespace}, value)
                    );
                }
                _ => {}
            }
        }
    }
    Vec::new()
}
