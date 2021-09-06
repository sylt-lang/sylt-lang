use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Entry::{Occupied, Vacant};
use crate::{Compiler, Name};
use sylt_parser::{
    AST, Assignable, AssignableKind, Expression, ExpressionKind, Identifier,
    Statement, StatementKind,
};
use sylt_parser::statement::NameIdentifier;

struct Context<'a> {
    compiler: &'a Compiler,
    namespace: usize,
}

fn assignable_dependencies(ctx: &Context, assignable: &Assignable) -> HashSet<Name> {
    use AssignableKind::*;
    match &assignable.kind {
        Read(ident) => {
            // Might be shadowed here
            dbg!(&ident.name);
            match ctx.compiler.namespaces[ctx.namespace].get(&ident.name) {
                Some(&name) => [name].iter().cloned().collect(),
                None => HashSet::new(),
            }
        },
        Call(ass, exprs) => assignable_dependencies(ctx, ass)
            .union(&exprs.iter()
                .map(|expr| dependencies(ctx, expr))
                .flatten()
                .collect()
            )
            .cloned()
            .collect(),
        ArrowCall(expr, ass, exprs) => dependencies(ctx, expr).iter()
            .chain(assignable_dependencies(ctx, ass).iter())
            .cloned()
            .chain(exprs.iter().map(|e| dependencies(ctx, e)).flatten())
            .collect(),
        Access(ass, field) => {
            let mut deps = assignable_dependencies(ctx, ass);

            // HACK: Find out which global is being accessed in another
            // namespace. This will not work for more nested structures.
            // It is possible to get uninitialized values by hiding a
            // namespace in a list for example.
            if let Read(ident) = &ass.kind {
                if let Some(Name::Namespace(ns)) =
                    ctx.compiler.namespaces[ctx.namespace].get(&ident.name)
                {
                    deps.insert(*ctx.compiler.namespaces[*ns].get(&field.name).unwrap());
                    return deps;
                }
            }
            return deps;
        },
        Index(ass, expr) => assignable_dependencies(ctx, ass)
            .union(&dependencies(ctx, expr))
            .cloned()
            .collect(),
        Expression(expr) => dependencies(ctx, expr),
    }
}

fn statement_dependencies(ctx: &Context, statement: &Statement) -> HashSet<Name> {
    use StatementKind::*;
    match &statement.kind {
        Assignment { target, value, .. } => dependencies(ctx, value)
            .union(&assignable_dependencies(ctx, target))
            .cloned()
            .collect(),
        If { condition, pass, fail } => [
                dependencies(ctx, condition),
                statement_dependencies(ctx, pass),
                statement_dependencies(ctx, fail),
            ].iter()
            .flatten()
            .cloned()
            .collect(),
        Loop { condition, body } => dependencies(ctx, condition)
            .union(&statement_dependencies(ctx, body))
            .cloned()
            .collect(),
        Block { statements } => statements.iter()
            .map(|stmt| statement_dependencies(ctx, stmt))
            .flatten()
            .collect(),

        | Ret { value }
        | Definition { value, .. } // TODO: Shadowing
        | StatementExpression { value } => dependencies(ctx, value),

        | Use { .. }
        | Blob { .. }
        | IsCheck { .. }
        | Break
        | Continue
        | Unreachable
        | EmptyStatement => HashSet::new(),
    }
}

fn dependencies(ctx: &Context, expression: &Expression) -> HashSet<Name> {
    use ExpressionKind::*;
    match &expression.kind {

        Get(assignable) => assignable_dependencies(ctx, assignable),

        | Neg(expr)
        | Not(expr)
        | Duplicate(expr)
        | Parenthesis(expr) => dependencies(ctx, expr),

        | Comparison(lhs, _, rhs)
        | Add(lhs, rhs)
        | Sub(lhs, rhs)
        | Mul(lhs, rhs)
        | Div(lhs, rhs)
        | AssertEq(lhs, rhs)
        | And(lhs, rhs)
        | Or(lhs, rhs) => dependencies(ctx, lhs)
            .union(&dependencies(ctx, rhs))
            .cloned()
            .collect(),

        | IfExpression { condition, pass, fail }
        | IfShort { lhs: pass, condition, fail } => {
            [pass, fail, condition].iter()
                .map(|expr| dependencies(ctx, expr))
                .flatten()
                .collect()
        },

        // Functions are a bit special. They only create dependencies once
        // called, which is a problem. It is currently impossible to know when
        // a function is going to be called after being read, so for our
        // purposes reading and calling is considered the same. Function
        // definitions are handled separately since they have no dependencies.
        Function { body, .. } => {
            //TODO: params shadow other variables
            statement_dependencies(ctx, body)
        },
        Instance { blob, .. } => {
            //TODO: The fields too.
            assignable_dependencies(ctx, blob)
        },

        | Tuple(exprs)
        | List(exprs)
        | Set(exprs)
        | Dict(exprs) => {
            exprs.iter()
                .map(|expr| dependencies(ctx, expr))
                .flatten()
                .collect()
        },

        // No dependencies
        | TypeConstant(_)
        | Float(_)
        | Int(_)
        | Str(_)
        | Bool(_)
        | Nil => HashSet::new(),
    }
}

fn order(to_order: HashMap<Name, (HashSet<Name>, (&Statement, usize))>) -> Vec<(&Statement, usize)> {

    enum State {
        Inserting,
        Inserted,
    }

    fn recurse<'a>(
        name: Name,
        to_order: &HashMap<Name, (HashSet<Name>, (&'a Statement, usize))>,
        inserted: &mut HashMap<Name, State>,
        ordered: &mut Vec<(&'a Statement, usize)>
    ) {
        match inserted.entry(name) {
            Vacant(entry) => entry.insert(State::Inserting),
            Occupied(entry) => match entry.get() {
                State::Inserting => panic!("Cycle"),
                State::Inserted => return,
            },
        };
        let (deps, statement) = to_order.get(&name).unwrap();
        for dep in deps {
            recurse(*dep, to_order, inserted, ordered);
        }

        inserted.insert(name, State::Inserted);
        ordered.push(*statement);
    }

    // TODO: detect cycles
    let mut ordered = Vec::new();
    let mut inserted = HashMap::new();
    for (name, _) in to_order.iter() {
        recurse(*name, &to_order, &mut inserted, &mut ordered);
    }

    ordered
}

pub(crate) fn initialization_order<'a>(tree: &'a AST, compiler: &Compiler) -> Vec<(&'a Statement, usize)> {
    let path_to_namespace_id: HashMap<_, _> = compiler.namespace_id_to_path
        .iter()
        .map(|(a, b)| (b.clone(), *a))
        .collect();
    let mut to_order = HashMap::new();
    let mut is_checks = Vec::new();
    for (path, module) in tree.modules.iter() {
        let namespace = *path_to_namespace_id.get(path).unwrap();
        //let globals: Vec<_> = compiler.namespaces[namespace]
        //    .iter()
        //    .map(|(name, _global)| name)
        //    .cloned()
        //    .collect();
        //dbg!(globals);
        for statement in module.statements.iter() {
            use StatementKind::*;
            match &statement.kind {
                | Use { name: NameIdentifier::Implicit(Identifier { name, .. }), .. }
                | Use { name: NameIdentifier::Alias(Identifier { name, .. }), .. }
                | Blob { name, .. } => {
                    to_order.insert(
                        *compiler.namespaces[namespace].get(name).unwrap(),
                        (HashSet::new(), (statement, namespace))
                    );
                }
                Definition { ident, value, .. } => {
                    // If it is a function definition it has no dependencies
                    let deps = if let ExpressionKind::Function{..} = &value.kind {
                        HashSet::new()
                    } else {
                        dependencies(&Context{compiler, namespace}, value)
                    };
                    //dbg!(
                    //    &ident.name,
                    //    &deps
                    //);
                    to_order.insert(
                        *compiler.namespaces[namespace].get(&ident.name).unwrap(),
                        (deps, (statement, namespace))
                    );
                }
                IsCheck { .. } => is_checks.push((statement, namespace)),
                _ => {}
            }
        }
    }
    let mut to_order = order(to_order);
    to_order.extend(is_checks);
    return to_order;
}
