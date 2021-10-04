use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::collections::btree_map::Entry::{Occupied, Vacant};
use crate::{Compiler, Name};
use sylt_parser::{
    AST, Assignable, AssignableKind, Expression, ExpressionKind, Identifier,
    Type as ParserType, TypeKind,
    Statement, StatementKind,
};
use sylt_parser::statement::NameIdentifier;

struct Context<'a> {
    compiler: &'a Compiler,
    namespace: usize,
    variables: Vec<String>,
}

impl Context<'_> {
    fn shadow(&mut self, variable: &str) {
        if !self.shadowed(variable) {
            self.variables.push(variable.to_string());
        }
    }

    fn shadowed(&self, variable: &str) -> bool {
        return self.variables.iter().rfind(|&v| v == variable).is_some();
    }
}

fn assignable_dependencies(ctx: &mut Context, assignable: &Assignable) -> BTreeSet<Name> {
    use AssignableKind::*;
    match &assignable.kind {
        Read(ident) => {
            match ctx.compiler.namespaces[ctx.namespace].get(&ident.name) {
                Some(&name) if !ctx.shadowed(&ident.name) => {
                    [name].iter().cloned().collect::<BTreeSet<_>>()
                },
                _ => BTreeSet::new(),
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
            // Get namespace access recursively
            // NOTE: This will ignore the actual namespace as a dependency, which
            // is not a problem since the compiler already initializes namespaces
            // before the dependency analysis.
            fn recursive_namespace(ctx: &mut Context, ass: &Assignable) -> Result<usize, ()> {
                match &ass.kind {
                    Access(lhs, field) => {
                        let namespace = recursive_namespace(ctx, lhs)?;
                        match ctx.compiler.namespaces[namespace].get(&field.name) {
                            Some(Name::Namespace(ns)) => Ok(*ns),
                            _ => Err(()),
                        }
                    },
                    Read(ident) => {
                        // Might be shadowed here
                        let shadowed = ctx.shadowed(&ident.name);
                        match ctx.compiler.namespaces[ctx.namespace].get(&ident.name) {
                            Some(Name::Namespace(ns)) if !shadowed => Ok(*ns),
                            _ => Err(()),
                        }
                    },
                    _ => Err(()),
                }
            }
            match recursive_namespace(ctx, ass) {
                Ok(namespace) => match ctx.compiler.namespaces[namespace].get(&field.name) {
                    Some(&name) => {
                        [name].iter().cloned().collect::<BTreeSet<_>>()
                    },
                    _ => BTreeSet::new(),
                },
                Err(_) => assignable_dependencies(ctx, ass),
            }
        },
        Index(ass, expr) => assignable_dependencies(ctx, ass)
            .union(&dependencies(ctx, expr))
            .cloned()
            .collect(),
        Expression(expr) => dependencies(ctx, expr),
    }
}

fn type_dependencies(ctx: &mut Context, ty: &ParserType) -> BTreeSet<Name> {
    use TypeKind::*;
    match &ty.kind {
        | Implied
        | Resolved(_)
        | Generic(_) => BTreeSet::new(),

        UserDefined(assignable) => assignable_dependencies(ctx, &assignable),

        Fn(params, ret) =>
            params.iter().chain([ret.as_ref()]).map(|t| type_dependencies(ctx, t)).flatten().collect(),

        Tuple(fields) =>
            fields.iter().map(|t| type_dependencies(ctx, t)).flatten().collect(),

        | List(kind)
        | Set(kind) => type_dependencies(ctx, kind),

        | Dict(a, b)
        | Union(a, b) => [
            type_dependencies(ctx, a),
            type_dependencies(ctx, b),
        ].iter().flatten().cloned().collect(),
    }
}

fn statement_dependencies(ctx: &mut Context, statement: &Statement) -> BTreeSet<Name> {
    use StatementKind::*;
    match &statement.kind {
        Assignment { target, value, .. } => dependencies(ctx, value)
            .union(&assignable_dependencies(ctx, target))
            .cloned()
            .collect(),
        If { condition, pass, fail } => {
            [
                dependencies(ctx, condition),
                statement_dependencies(ctx, pass),
                statement_dependencies(ctx, fail),
            ]
            .iter()
            .flatten()
            .cloned()
            .collect()
        },
        Loop { condition, body } => dependencies(ctx, condition)
            .union(&statement_dependencies(ctx, body))
            .cloned()
            .collect(),
        Block { statements } => {
            let vars_before = ctx.variables.len();
            let deps = statements.iter()
                .map(|stmt| statement_dependencies(ctx, stmt))
                .flatten()
                .collect();
            ctx.variables.truncate(vars_before);
            deps
        },
        Definition { ident, value, .. } => {
            ctx.shadow(&ident.name);
            dependencies(ctx, value)
        },

        | Ret { value }
        | StatementExpression { value } => dependencies(ctx, value),

        | Blob { .. }
        | Break
        | Continue
        | EmptyStatement
        | ExternalDefinition { .. }
        | IsCheck { .. }
        | Unreachable
        | Use { .. } => BTreeSet::new(),
    }
}

fn dependencies(ctx: &mut Context, expression: &Expression) -> BTreeSet<Name> {
    use ExpressionKind::*;
    match &expression.kind {

        Get(assignable) => assignable_dependencies(ctx, assignable),

        | Neg(expr)
        | Not(expr)
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

        IfExpression { condition, pass, fail } => {
            [pass, fail, condition].iter()
                .map(|expr| dependencies(ctx, expr))
                .flatten()
                .collect()
        },

        // Functions are a bit special. They only create dependencies once
        // called, which is a problem. It is currently impossible to know when
        // a function is going to be called after being read, so for our
        // purposes defining the function requires all dependencies.
        Function { body, params, .. } => {
            let vars_before = ctx.variables.len();
            params.iter().for_each(|(ident, _)| ctx.shadow(&ident.name));
            let type_deps = params.iter().map(|(_, ty)| type_dependencies(ctx, ty)).flatten().collect();
            let deps = statement_dependencies(ctx, body);
            ctx.variables.truncate(vars_before);
            [deps, type_deps].iter().flatten().cloned().collect()
        },
        Blob { blob, fields } => {
            assignable_dependencies(ctx, blob).union(&fields.iter()
                .map(|(_, expr)| dependencies(ctx, expr))
                .flatten()
                .collect()
            )
            .cloned()
            .collect()
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
        | Nil => BTreeSet::new(),
    }
}

fn order(
    to_order: BTreeMap<Name, (BTreeSet<Name>, (&Statement, usize))>
) -> Result<Vec<(&Statement, usize)>, Vec<(&Statement, usize)>> {
    enum State {
        Inserting,
        Inserted,
    }

    fn recurse<'a>(
        name: Name,
        to_order: &BTreeMap<Name, (BTreeSet<Name>, (&'a Statement, usize))>,
        inserted: &mut BTreeMap<Name, State>,
        ordered: &mut Vec<(&'a Statement, usize)>
    ) -> Result<(), Vec<(&'a Statement, usize)>> {
        match inserted.entry(name) {
            Vacant(entry) => entry.insert(State::Inserting),
            Occupied(entry) => return match entry.get() {
                State::Inserting => Err(Vec::new()),
                State::Inserted => Ok(()),
            },
        };

        let (deps, statement) = to_order.get(&name).expect("Trying to find an identifier that does not exist");
        for dep in deps {
            recurse(*dep, to_order, inserted, ordered)
                .map_err(|mut cycle| { cycle.push(*statement); cycle })?;
        }
        ordered.push(*statement);
        inserted.insert(name, State::Inserted);

        Ok(())
    }

    let mut ordered = Vec::new();
    let mut inserted = BTreeMap::new();
    for (name, _) in to_order.iter() {
        recurse(*name, &to_order, &mut inserted, &mut ordered)?;
    }

    Ok(ordered)
}

pub(crate) fn initialization_order<'a>(
    tree: &'a AST,
    compiler: &Compiler
) -> Result<Vec<(&'a Statement, usize)>, Vec<(&'a Statement, usize)>> {
    let path_to_namespace_id: HashMap<_, _> = compiler.namespace_id_to_path
        .iter()
        .map(|(a, b)| (b.clone(), *a))
        .collect();
    let mut to_order = BTreeMap::new();
    let mut is_checks = Vec::new();
    for (path, module) in tree.modules.iter() {
        let namespace = *path_to_namespace_id.get(path).unwrap();
        for statement in module.statements.iter() {
            use StatementKind::*;
            match &statement.kind {
                | Use { name: NameIdentifier::Implicit(Identifier { name, .. }), .. }
                | Use { name: NameIdentifier::Alias(Identifier { name, .. }), .. }
                | Blob { name, .. } => {
                    to_order.insert(
                        *compiler.namespaces[namespace].get(name).unwrap(),
                        (BTreeSet::new(), (statement, namespace))
                    );
                },
                ExternalDefinition { ident, .. } => {
                    to_order.insert(
                        *compiler.namespaces[namespace].get(&ident.name).unwrap(),
                        (BTreeSet::new(), (statement, namespace))
                    );
                },
                Definition { ident, value, .. } => {
                    let mut ctx = Context {
                        compiler,
                        namespace,
                        variables: Vec::new(),
                    };
                    ctx.shadow(&ident.name);
                    let deps = dependencies(&mut ctx, value);
                    to_order.insert(
                        *compiler.namespaces[namespace].get(&ident.name).unwrap(),
                        (deps, (statement, namespace))
                    );
                },
                IsCheck { .. } => is_checks.push((statement, namespace)),
                _ => {},
            }
        }
    }
    return order(to_order).map(|mut o| { o.extend(is_checks); o });
}
