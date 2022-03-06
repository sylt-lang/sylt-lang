use crate::name_resolution::{Expression, IfBranch, Statement, Var};
use std::collections::btree_map::Entry::{Occupied, Vacant};
use std::collections::{BTreeMap, BTreeSet, HashMap};

fn statement_dependencies(statement: &Statement) -> BTreeSet<usize> {
    use Statement as S;
    match &statement {
        S::Assignment { target, value, .. } => dependencies(value)
            .union(&dependencies(target))
            .cloned()
            .collect(),

        S::Block { statements, .. } => statements
            .iter()
            .map(|stmt| statement_dependencies(stmt))
            .flatten()
            .collect(),

        S::Loop { condition, body, .. } => dependencies(condition)
            .union(
                &body
                    .iter()
                    .map(|stmt| statement_dependencies(stmt))
                    .flatten()
                    .collect(),
            )
            .cloned()
            .collect(),

        S::Definition { var, value, .. } => {
            let mut deps = dependencies(value);
            // Functions can be recursive - it's fine!
            if matches!(value, Expression::Function { .. }) {
                deps.remove(var);
            }
            deps
        }

        S::Ret { value: Some(value), .. } | S::StatementExpression { value, .. } => {
            dependencies(value)
        }
        S::Ret { value: None, .. } => BTreeSet::new(),

        S::Blob { .. }
        | S::Enum { .. }
        | S::ExternalDefinition { .. }
        | S::Break(..)
        | S::Continue(..)
        | S::Unreachable(..) => BTreeSet::new(),
    }
}

fn dependencies(expression: &Expression) -> BTreeSet<usize> {
    use Expression as E;
    match &expression {
        E::Read { var, .. } => [*var].iter().map(|v| *v).collect(),
        E::Variant { value, .. } => dependencies(value),
        E::Call { function, args, span } => dependencies(function)
            .union(
                &args
                    .iter()
                    .map(|expr| dependencies(expr))
                    .flatten()
                    .collect(),
            )
            .cloned()
            .collect(),

        E::BlobAccess { value, .. } => dependencies(value),
        E::Index { value, index, .. } => dependencies(value)
            .union(&dependencies(index))
            .cloned()
            .collect(),
        E::BinOp { a, b, .. } => dependencies(a).union(&dependencies(b)).cloned().collect(),
        E::UniOp { a, .. } => dependencies(a),
        E::If { branches, .. } => branches
            .iter()
            .map(|IfBranch { condition, body, span: _ }| {
                [
                    condition
                        .as_ref()
                        .map(|cond| dependencies(&cond))
                        .unwrap_or_else(|| BTreeSet::new())
                        .clone(),
                    body.iter()
                        .map(|f| statement_dependencies(f))
                        .flatten()
                        .collect(),
                ]
                .iter()
                .flatten()
                .cloned()
                .collect::<BTreeSet<_>>()
            })
            .flatten()
            .collect(),

        E::Case { to_match, branches, fall_through, .. } => [
            dependencies(to_match),
            fall_through
                .clone()
                .unwrap_or_else(|| Vec::new())
                .iter()
                .map(|f| statement_dependencies(f))
                .flatten()
                .collect(),
            branches
                .iter()
                .map(|branch| {
                    branch
                        .body
                        .iter()
                        .map(|stmt| statement_dependencies(stmt))
                        .flatten()
                        .collect::<BTreeSet<_>>()
                })
                .flatten()
                .collect::<BTreeSet<_>>(),
        ]
        .iter()
        .cloned()
        .flatten()
        .collect(),

        // Functions are a bit special. They only create dependencies once
        // called, which is a problem. It is currently impossible to know when
        // a function is going to be called after being read, so for our
        // purposes defining the function requires all dependencies.
        //
        // NOTE(ed): It's not impossible anymore! We now track all the variables
        // in a nice list, so we can easily mark them as "strange" once they're read
        // and not called imediately. And to reason about "non-strange" functions is
        // quite easy! :D
        E::Function { body, .. } => body
            .iter()
            .map(|stmt| statement_dependencies(stmt))
            .flatten()
            .collect(),

        E::Blob { blob, fields, .. } => fields
            .iter()
            .map(|(_, expr)| dependencies(expr))
            .flatten()
            .collect(),

        E::Collection { values, .. } => values
            .iter()
            .map(|expr| dependencies(expr))
            .flatten()
            .collect(),

        // No dependencies
        E::Float(_, _) | E::Int(_, _) | E::Str(_, _) | E::Bool(_, _) | E::Nil(_) => BTreeSet::new(),
    }
}

fn order<'a>(
    vars: &'a [Var],
    to_order: BTreeMap<usize, (BTreeSet<usize>, &'a Statement)>,
) -> Result<Vec<&'a Statement>, Vec<&'a Statement>> {
    enum State {
        Inserting,
        Inserted,
    }

    fn recurse<'a>(
        global: &usize,
        to_order: &BTreeMap<usize, (BTreeSet<usize>, &'a Statement)>,
        inserted: &mut BTreeMap<usize, State>,
        ordered: &mut Vec<&'a Statement>,
        vars: &'a [Var],
    ) -> Result<(), Vec<&'a Statement>> {
        if !vars[*global].is_global {
            return Ok(());
        }
        let (deps, statement) = if let Some(thing) = to_order.get(&global) {
            thing
        } else  {
            return Ok(());
        };

        match inserted.entry(global.clone()) {
            Vacant(entry) => entry.insert(State::Inserting),
            Occupied(entry) => {
                return match entry.get() {
                    State::Inserting => Err(Vec::new()),
                    State::Inserted => Ok(()),
                }
            }
        };

        for dep in deps {
            recurse(dep, to_order, inserted, ordered, vars).map_err(|mut cycle| {
                cycle.push(*statement);
                cycle
            })?;
        }
        ordered.push(*statement);

        Ok(())
    }

    let mut ordered = Vec::new();
    let mut inserted = BTreeMap::new();
    for (var, _) in to_order.iter() {
        recurse(var, &to_order, &mut inserted, &mut ordered, vars)?;
    }

    Ok(ordered)
}

pub(crate) fn initialization_order<'a>(
    vars: &'a [Var],
    statements: &'a [Statement],
) -> Result<Vec<&'a Statement>, Vec<&'a Statement>> {
    let mut to_order = BTreeMap::new();
    for statement in statements.iter() {
        use Statement as S;
        match &statement {
            S::Blob { var, .. }
            | S::Enum { var, .. }
            | S::ExternalDefinition { var, .. }
            | S::Definition { var, .. } => {
                to_order.insert(
                    *var,
                    (statement_dependencies(statement), statement),
                );
            }

            _ => {}
        }
    }

    return order(vars, to_order);
}
