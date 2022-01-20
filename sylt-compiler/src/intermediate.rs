use std::{collections::HashMap, fmt::Display};

use sylt_parser::{
    expression::ComparisonKind, Assignable, AssignableKind, CaseBranch, Expression, ExpressionKind,
    Identifier, Op as ParserOp, Statement, StatementKind,
};

use crate::{typechecker::TypeChecker, NamespaceID};

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub struct Var(pub usize);

impl Var {
    pub fn format(self) -> String {
        format!("V{}", self.0)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Label(pub usize);

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Label(n) = self;
        write!(f, "L{}", n)
    }
}

#[derive(Debug, Clone)]
pub enum IR {
    Nil(Var),
    Int(Var, i64),
    Float(Var, f64),
    Str(Var, String),
    Bool(Var, bool),
    Add(Var, Var, Var),
    Sub(Var, Var, Var),
    Mul(Var, Var, Var),
    Div(Var, Var, Var),
    Neg(Var, Var),

    Not(Var, Var),

    External(Var, String),
    Call(Var, Var, Vec<Var>),

    Equals(Var, Var, Var),
    NotEquals(Var, Var, Var),
    Greater(Var, Var, Var),
    GreaterEqual(Var, Var, Var),
    Less(Var, Var, Var),
    LessEqual(Var, Var, Var),
    In(Var, Var, Var),

    Assert(Var),

    List(Var, Vec<Var>),
    Set(Var, Vec<Var>),
    Dict(Var, Vec<Var>),
    Tuple(Var, Vec<Var>),
    Blob(Var, Vec<(String, Var)>),
    Variant(Var, String, Var),

    // Name?
    Function(Var, Vec<Var>),

    Index(Var, Var, Var),
    AssignIndex(Var, Var, Var),

    Access(Var, Var, String),
    AssignAccess(Var, String, Var),

    Label(Label),
    Goto(Label),
    Copy(Var, Var),
    Define(Var),
    Assign(Var, Var),
    Return(Var),
    If(Var),
    HaltAndCatchFire(String),
    Loop,
    Break,
    Else,
    End,
}

#[derive(Debug, Clone, Copy)]
struct IRContext {
    namespace: usize,
    closest_loop: Label,
}

impl IRContext {
    pub fn from_namespace(namespace: usize) -> Self {
        Self { namespace, closest_loop: Label(0) }
    }
}

struct Variable {
    name: String,
    namespace: NamespaceID,
    var: Var,
}

#[derive(Debug, Clone)]
struct Namespace {
    name: String,
    namespace: NamespaceID,
    points_to: NamespaceID,
}

struct IRCodeGen<'a> {
    #[allow(unused)]
    typechecker: &'a TypeChecker,
    variables: Vec<Variable>,
    namespaces: Vec<Namespace>,

    counter: usize,
}

impl<'a> IRCodeGen<'a> {
    fn new(typechecker: &'a TypeChecker) -> Self {
        Self {
            counter: 0,
            typechecker,
            variables: Vec::new(),
            namespaces: Vec::new(),
        }
    }

    fn var(&mut self) -> Var {
        let i = self.counter;
        self.counter += 1;
        Var(i)
    }

    fn label(&mut self) -> Label {
        let i = self.counter;
        self.counter += 1;
        Label(i)
    }

    fn lookup(&self, search_name: &str, search_namespace: usize) -> Option<Var> {
        self.variables
            .iter()
            .rfind(|Variable { name, namespace, .. }| {
                search_namespace == *namespace && name == search_name
            })
            .map(|v| v.var)
    }

    fn lookup_namespace(&self, search_name: &str, search_namespace: usize) -> Option<NamespaceID> {
        self.namespaces
            .iter()
            .rfind(|Namespace { name, namespace, .. }| {
                search_namespace == *namespace && name == search_name
            })
            .map(|v| v.points_to)
    }

    fn namespace_chain(&self, assignable: &Assignable, ctx: IRContext) -> Option<IRContext> {
        match &assignable.kind {
            AssignableKind::Read(ident) => match self.lookup(&ident.name, ctx.namespace) {
                Some(_) => None,
                None => self
                    .lookup_namespace(&ident.name, ctx.namespace)
                    .map(IRContext::from_namespace),
            },
            AssignableKind::Access(ass, ident) => {
                let ctx = self.namespace_chain(ass, ctx)?;
                self.lookup_namespace(&ident.name, ctx.namespace)
                    .map(IRContext::from_namespace)
            }

            AssignableKind::Call(..)
            | AssignableKind::Variant { .. }
            | AssignableKind::ArrowCall(..)
            | AssignableKind::Index(..)
            | AssignableKind::Expression(..) => None,
        }
    }

    fn assignable(&mut self, assignable: &Assignable, ctx: IRContext) -> (Vec<IR>, Var) {
        match &assignable.kind {
            AssignableKind::Read(ident) => (
                Vec::new(),
                self.lookup(&ident.name, ctx.namespace).expect(&ident.name),
            ),
            AssignableKind::Variant { variant, value, .. } => {
                let (xops, x) = self.expression(&value, ctx);
                let out = self.var();
                (
                    [xops, vec![IR::Variant(out, variant.name.clone(), x)]].concat(),
                    out,
                )
            }
            AssignableKind::Call(ass, exprs) => {
                let (fn_code, fn_var) = self.assignable(ass, ctx);
                let (code, args): (Vec<_>, Vec<_>) =
                    exprs.iter().map(|expr| self.expression(expr, ctx)).unzip();
                let code = code.concat();

                let var = self.var();
                (
                    [fn_code, code, vec![IR::Call(var, fn_var, args)]].concat(),
                    var,
                )
            }
            AssignableKind::ArrowCall(extra, ass, exprs) => {
                let (fn_code, fn_var) = self.assignable(ass, ctx);
                let (extra_code, extra) = self.expression(extra, ctx);
                let (code, mut args): (Vec<_>, Vec<_>) =
                    exprs.iter().map(|expr| self.expression(expr, ctx)).unzip();
                let code = code.concat();
                args.insert(0, extra);

                let var = self.var();
                (
                    [fn_code, extra_code, code, vec![IR::Call(var, fn_var, args)]].concat(),
                    var,
                )
            }
            AssignableKind::Access(ass, ident) => match self.namespace_chain(ass, ctx) {
                Some(ctx) => (Vec::new(), self.lookup(&ident.name, ctx.namespace).unwrap()),
                None => {
                    let (code, a) = self.assignable(ass, ctx);
                    let b = self.var();
                    (
                        [code, vec![IR::Access(b, a, ident.name.clone())]].concat(),
                        b,
                    )
                }
            },
            AssignableKind::Index(ass, expr) => {
                let (aops, a) = self.assignable(&ass, ctx);
                let (bops, b) = self.expression(&expr, ctx);
                let c = self.var();

                ([aops, bops, vec![IR::Index(c, a, b)]].concat(), c)
            }
            AssignableKind::Expression(expr) => self.expression(expr, ctx),
        }
    }

    fn expression_block(&mut self, out: Var, mut block: Vec<Statement>, ctx: IRContext) -> Vec<IR> {
        let value = match block.last().cloned() {
            Some(Statement {
                kind: StatementKind::StatementExpression { value },
                ..
            }) => {
                block.pop();
                Some(value)
            }
            _ => None,
        };
        let ops = block
            .iter()
            .map(|stmt| self.statement(&stmt, ctx))
            .flatten()
            .collect();
        [
            ops,
            if let Some(value) = value {
                let (ops, var) = self.expression(&value, ctx);
                [ops, vec![IR::Assign(out, var)]].concat()
            } else {
                Vec::new()
            },
        ]
            .concat()
    }

    fn expression(&mut self, expr: &Expression, ctx: IRContext) -> (Vec<IR>, Var) {
        match &expr.kind {
            ExpressionKind::Get(ass) => {
                let (code, source) = self.assignable(ass, ctx);
                let dest = self.var();
                ([code, vec![IR::Copy(dest, source)]].concat(), dest)
            }
            ExpressionKind::Comparison(a, op, b) => {
                let (aops, a) = self.expression(&a, ctx);
                let (bops, b) = self.expression(&b, ctx);
                let c = self.var();
                let op = match op {
                    ComparisonKind::Equals => IR::Equals(c, a, b),
                    ComparisonKind::NotEquals => IR::NotEquals(c, a, b),
                    ComparisonKind::Greater => IR::Greater(c, a, b),
                    ComparisonKind::GreaterEqual => IR::GreaterEqual(c, a, b),
                    ComparisonKind::Less => IR::Less(c, a, b),
                    ComparisonKind::LessEqual => IR::LessEqual(c, a, b),
                    ComparisonKind::In => IR::In(c, a, b),
                };
                ([aops, bops, vec![op]].concat(), c)
            }
            ExpressionKind::And(a, b) => {
                let (aops, a) = self.expression(&a, ctx);
                let (bops, b) = self.expression(&b, ctx);
                let c = self.var();
                (
                    [
                        aops,
                        vec![IR::Bool(c, false), IR::If(a)],
                        bops,
                        vec![IR::Assign(c, b), IR::End],
                    ]
                    .concat(),
                    c,
                )
            }
            ExpressionKind::Or(a, b) => {
                let (aops, a) = self.expression(&a, ctx);
                let (bops, b) = self.expression(&b, ctx);
                let neg_a = self.var();
                let c = self.var();
                (
                    [
                        aops,
                        vec![IR::Bool(c, true), IR::Not(neg_a, a), IR::If(neg_a)],
                        bops,
                        vec![IR::Assign(c, b), IR::End],
                    ]
                    .concat(),
                    c,
                )
            }
            ExpressionKind::Not(a) => {
                let (aops, a) = self.expression(&a, ctx);
                let b = self.var();
                ([aops, vec![IR::Not(b, a)]].concat(), b)
            }

            ExpressionKind::If { condition, pass, fail } => {
                let (cops, c) = self.expression(&condition, ctx);
                let out = self.var();
                let aops = self.expression_block(out, pass.clone(), ctx);
                let bops = self.expression_block(out, fail.clone(), ctx);
                (
                    [
                        cops,
                        vec![IR::Define(out), IR::If(c)],
                        aops,
                        vec![IR::Else],
                        bops,
                        vec![IR::End],
                    ]
                    .concat(),
                    out,
                )
            }

            ExpressionKind::Blob { fields, .. } => {
                let ss = self.variables.len();

                let self_var = self.var();
                self.variables.push(Variable {
                    name: "self".into(),
                    namespace: ctx.namespace,
                    var: self_var,
                });
                let (fields, (code, exprs)): (Vec<_>, (Vec<_>, Vec<_>)) = fields
                    .iter()
                    .map(|(field, expr)| (field.clone(), self.expression(expr, ctx)))
                    .unzip();
                let code = code.concat();
                let fields: Vec<_> = fields.into_iter().zip(exprs.into_iter()).collect();
                let var = self.var();

                self.variables.truncate(ss);

                (
                    [
                        vec![IR::Define(self_var)],
                        code,
                        vec![IR::Blob(var, fields), IR::Assign(self_var, var)],
                    ]
                    .concat(),
                    var,
                )
            }

            ExpressionKind::List(exprs) => {
                let (code, exprs): (Vec<_>, Vec<_>) =
                    exprs.iter().map(|expr| self.expression(expr, ctx)).unzip();
                let code = code.concat();
                let var = self.var();

                ([code, vec![IR::List(var, exprs)]].concat(), var)
            }

            ExpressionKind::Set(exprs) => {
                let (code, exprs): (Vec<_>, Vec<_>) =
                    exprs.iter().map(|expr| self.expression(expr, ctx)).unzip();
                let code = code.concat();
                let var = self.var();

                ([code, vec![IR::Set(var, exprs)]].concat(), var)
            }
            ExpressionKind::Dict(exprs) => {
                let (code, exprs): (Vec<_>, Vec<_>) =
                    exprs.iter().map(|expr| self.expression(expr, ctx)).unzip();
                let code = code.concat();
                let var = self.var();

                ([code, vec![IR::Dict(var, exprs)]].concat(), var)
            }

            ExpressionKind::Tuple(exprs) => {
                let (code, exprs): (Vec<_>, Vec<_>) =
                    exprs.iter().map(|expr| self.expression(expr, ctx)).unzip();
                let code = code.concat();
                let var = self.var();

                ([code, vec![IR::Tuple(var, exprs)]].concat(), var)
            }

            ExpressionKind::Parenthesis(expr) => self.expression(expr, ctx),

            ExpressionKind::Float(a) => {
                let var = self.var();
                (vec![IR::Float(var, *a)], var)
            }
            ExpressionKind::Str(a) => {
                let var = self.var();
                (vec![IR::Str(var, a.into())], var)
            }

            ExpressionKind::AssertEq(a, b) => {
                let (aops, a) = self.expression(&a, ctx);
                let (bops, b) = self.expression(&b, ctx);
                let c = self.var();
                (
                    [aops, bops, vec![IR::Equals(c, a, b), IR::Assert(c)]].concat(),
                    c,
                )
            }

            ExpressionKind::Bool(b) => {
                let a = self.var();
                (vec![IR::Bool(a, *b)], a)
            }

            ExpressionKind::Function { name, body, params, .. } => {
                let ss = self.variables.len();
                let f = self.var();
                self.variables.push(Variable {
                    name: name.clone(),
                    namespace: ctx.namespace,
                    var: f,
                });
                let params = params
                    .iter()
                    .map(|(name, _)| {
                        let var = self.var();
                        self.variables.push(Variable {
                            name: name.name.clone(),
                            namespace: ctx.namespace,
                            var,
                        });
                        var
                    })
                    .collect();
                let body = self.statement(body, ctx);
                self.variables.truncate(ss);
                (
                    [vec![IR::Function(f, params)], body, vec![IR::End]].concat(),
                    f,
                )
            }

            ExpressionKind::Nil => {
                let a = self.var();
                (vec![IR::Nil(a)], a)
            }

            ExpressionKind::Int(i) => {
                let a = self.var();
                (vec![IR::Int(a, *i)], a)
            }

            ExpressionKind::Add(a, b) => {
                let (aops, a) = self.expression(&a, ctx);
                let (bops, b) = self.expression(&b, ctx);
                let c = self.var();
                ([aops, bops, vec![IR::Add(c, a, b)]].concat(), c)
            }

            ExpressionKind::Sub(a, b) => {
                let (aops, a) = self.expression(&a, ctx);
                let (bops, b) = self.expression(&b, ctx);
                let c = self.var();
                ([aops, bops, vec![IR::Sub(c, a, b)]].concat(), c)
            }

            ExpressionKind::Mul(a, b) => {
                let (aops, a) = self.expression(&a, ctx);
                let (bops, b) = self.expression(&b, ctx);
                let c = self.var();
                ([aops, bops, vec![IR::Mul(c, a, b)]].concat(), c)
            }
            ExpressionKind::Div(a, b) => {
                let (aops, a) = self.expression(&a, ctx);
                let (bops, b) = self.expression(&b, ctx);
                let c = self.var();
                ([aops, bops, vec![IR::Div(c, a, b)]].concat(), c)
            }

            ExpressionKind::Neg(a) => {
                let (aops, a) = self.expression(&a, ctx);
                let b = self.var();
                ([aops, vec![IR::Neg(b, a)]].concat(), b)
            }
        }
    }

    fn definition(&mut self, ident: &Identifier, value: &Expression, ctx: IRContext) -> Vec<IR> {
        if matches!(value.kind, ExpressionKind::Function { .. }) {
            let var = self.var();
            self.variables.push(Variable {
                name: ident.name.clone(),
                namespace: ctx.namespace,
                var,
            });
            let (mut code, _) = self.expression(&value, ctx);
            if let IR::Function(_, args) = &code[0] {
                code[0] = IR::Function(var, args.clone());
            } else {
                unreachable!();
            }

            code
        } else {
            let (code, var) = self.expression(&value, ctx);
            self.variables.push(Variable {
                name: ident.name.clone(),
                namespace: ctx.namespace,
                var,
            });
            code
        }
    }

    fn statement(&mut self, stmt: &Statement, ctx: IRContext) -> Vec<IR> {
        match &stmt.kind {
            StatementKind::Assignment { kind, target, value } => {
                let res = self.var();
                let (pre_code, current, post_code) = match &target.kind {
                    AssignableKind::Read(_) => {
                        let (_, var) = self.assignable(target, ctx);
                        (Vec::new(), var, vec![IR::Assign(var, res)])
                    }
                    AssignableKind::Index(ass, expr) => {
                        let (aops, a) = self.assignable(ass, ctx);
                        let (bops, b) = self.expression(expr, ctx);
                        let c = self.var();

                        (
                            [aops, bops, vec![IR::Index(c, a, b)]].concat(),
                            c,
                            vec![IR::AssignIndex(a, b, res)],
                        )
                    }
                    AssignableKind::Access(ass, ident) => match self.namespace_chain(ass, ctx) {
                        Some(ctx) => {
                            let a = self.lookup(&ident.name, ctx.namespace).unwrap();
                            (Vec::new(), a, vec![IR::Assign(a, res)])
                        }
                        None => {
                            let (code, a) = self.assignable(ass, ctx);
                            let b = self.var();
                            (
                                [code, vec![IR::Access(b, a, ident.name.clone())]].concat(),
                                b,
                                vec![IR::AssignAccess(a, ident.name.clone(), res)],
                            )
                        }
                    },
                    AssignableKind::Expression(..)
                    | AssignableKind::Variant { .. }
                    | AssignableKind::Call(..)
                    | AssignableKind::ArrowCall(..) => unreachable!(),
                };
                let (code, var) = self.expression(&value, ctx);
                [
                    pre_code,
                    code,
                    vec![match kind {
                        ParserOp::Nop => IR::Assign(res, var),
                        ParserOp::Add => IR::Add(res, current, var),
                        ParserOp::Sub => IR::Sub(res, current, var),
                        ParserOp::Mul => IR::Mul(res, current, var),
                        ParserOp::Div => IR::Div(res, current, var),
                    }],
                    post_code,
                ]
                .concat()
            }
            StatementKind::Definition { ident, value, .. } => self.definition(ident, value, ctx),
            StatementKind::Block { statements } => {
                let ss = self.variables.len();
                let stmt_code = statements
                    .iter()
                    .map(|stmt| self.statement(stmt, ctx))
                    .flatten()
                    .collect();
                self.variables.truncate(ss);
                stmt_code
            }

            StatementKind::Case { to_match, branches, fall_through } => {
                let ss = self.variables.len();
                let (cops, c) = self.expression(&to_match, ctx);
                let tag = self.var();
                let tag_index = self.var();
                let value = self.var();
                let value_index = self.var();

                let branches_code = branches
                    .iter()
                    .map(|CaseBranch { pattern, variable, body }| {
                        if let Some(var_name) = variable {
                            self.variables.push(Variable {
                                name: var_name.name.clone(),
                                namespace: ctx.namespace,
                                var: value,
                            });
                        }
                        let body = self.statement(body, ctx);
                        self.variables.truncate(ss);

                        let exp_str = self.var();
                        let cmp = self.var();
                        [
                            vec![
                                IR::Str(exp_str, pattern.name.clone()),
                                IR::Equals(cmp, exp_str, tag),
                                IR::If(cmp),
                            ],
                            body,
                            vec![IR::Else],
                        ]
                        .concat()
                    })
                    .flatten()
                    .collect();

                let fall_through_code = fall_through
                    .as_ref()
                    .map(|stmt| self.statement(stmt, ctx))
                    .unwrap_or_else(Vec::new);

                [
                    cops,
                    vec![
                        IR::Int(tag_index, 1),
                        IR::Index(tag, c, tag_index),
                        IR::Int(value_index, 2),
                        IR::Index(value, c, value_index),
                    ],
                    branches_code,
                    fall_through_code,
                    (0..branches.len()).map(|_| IR::End).collect(),
                ]
                .concat()
            }
            StatementKind::Loop { condition, body } => {
                let (cops, c) = self.expression(&condition, ctx);
                let l = self.label();
                let body = self.statement(&body, IRContext { closest_loop: l, ..ctx });

                [
                    vec![IR::Loop, IR::Label(l)],
                    cops,
                    vec![IR::If(c), IR::Else, IR::Break, IR::End],
                    body,
                    vec![IR::End],
                ]
                .concat()
            }
            StatementKind::Break => vec![IR::Break],
            StatementKind::Continue => vec![IR::Goto(ctx.closest_loop)],
            StatementKind::Ret { value: Some(value) } => {
                let (aops, a) = self.expression(&value, ctx);
                [aops, vec![IR::Return(a)]].concat()
            }
            StatementKind::Ret { value: None } => {
                // NOTE: In the runtime, we compile void to unit - don't tell Filip!
                let a = self.var();
                vec![IR::Nil(a), IR::Return(a)]
            }
            StatementKind::Unreachable => {
                vec![IR::HaltAndCatchFire(format!(
                    "Reached unreachable code on line {}",
                    stmt.span.line_start
                ))]
            }

            StatementKind::StatementExpression { value } => self.expression(value, ctx).0,

            StatementKind::EmptyStatement => Vec::new(),

            StatementKind::Blob { .. }
            | StatementKind::Enum { .. }
            | StatementKind::ExternalDefinition { .. }
            | StatementKind::FromUse { .. }
            | StatementKind::Use { .. } => unreachable!(),
        }
    }

    fn globals(&mut self, stmt: &Statement, namespace: NamespaceID) {
        match &stmt.kind {
            StatementKind::Use { name, file, .. } => {
                let other_namspace = self.typechecker.file_to_namespace[file];

                self.namespaces.push(Namespace {
                    name: name.name().into(),
                    namespace,
                    points_to: other_namspace,
                });
            }

            _ => {}
        }
    }

    fn compile(&mut self, stmt: &Statement, namespace: NamespaceID) -> Vec<IR> {
        let ctx = IRContext::from_namespace(namespace);
        match &stmt.kind {
            StatementKind::FromUse { imports, file, .. } => {
                let other_namspace = self.typechecker.file_to_namespace[file];

                imports.iter().for_each(|(other_name, maybe_rename)| {
                    // TODO(ed): From import namespaces
                    let var = match self.lookup(&other_name.name, other_namspace) {
                        Some(var) => var,
                        None => return, // Ignore Blobs and Enums
                    };
                    let name = match maybe_rename {
                        Some(rename) => rename.name.clone(),
                        None => other_name.name.clone(),
                    };
                    self.variables.push(Variable { name, namespace, var });
                });

                Vec::new()
            }

            StatementKind::ExternalDefinition { ident, .. } => {
                let var = self.var();
                self.variables.push(Variable {
                    name: ident.name.clone(),
                    namespace: ctx.namespace,
                    var,
                });
                vec![IR::External(var, ident.name.clone())]
            }

            StatementKind::Definition { value, ident, .. } => self.definition(ident, value, ctx),

            // Invalid statements should be caught in the typechecker
            // TODO: Specify the unreachable things here
            _ => Vec::new(),
        }
    }
}

pub(crate) fn compile(
    typechecker: &TypeChecker,
    statements: &Vec<(Statement, NamespaceID)>,
) -> Vec<IR> {
    let mut gen = IRCodeGen::new(typechecker);

    statements
        .iter()
        .for_each(|(stmt, namespace)| gen.globals(stmt, *namespace));

    let mut code: Vec<IR> = statements
        .iter()
        .map(|(stmt, namespace)| gen.compile(stmt, *namespace))
        .flatten()
        .collect();

    let start = gen
        .variables
        .iter()
        .find(|Variable { name, namespace, .. }| namespace == &0 && name == &"start")
        .unwrap()
        .var;

    let tmp = gen.var();
    code.push(IR::Call(tmp, start, Vec::new()));
    code
}

// TODO(ed): We could remove more dead-code if we built a dependency-graph
// and removed all paths without side-effects, since they don't have
// an observable effect.
pub(crate) fn count_usages(ops: &[IR]) -> HashMap<Var, usize> {
    let mut table = HashMap::new();
    for op in ops {
        match op {
            IR::Nil(_)
            | IR::Int(_, _)
            | IR::Float(_, _)
            | IR::Str(_, _)
            | IR::Bool(_, _)
            | IR::Loop
            | IR::Break
            | IR::Else
            | IR::End
            | IR::External(_, _)
            | IR::Label(_)
            | IR::Goto(_)
            | IR::HaltAndCatchFire(_) => {}

            // We cannot optimize things that are defined.
            IR::Function(a, _) | IR::Define(a) => {
                *table.entry(*a).or_insert(0) += 2;
            }

            IR::Add(_, a, b)
            | IR::Sub(_, a, b)
            | IR::Mul(_, a, b)
            | IR::Div(_, a, b)
            | IR::Equals(_, a, b)
            | IR::NotEquals(_, a, b)
            | IR::Greater(_, a, b)
            | IR::GreaterEqual(_, a, b)
            | IR::Less(_, a, b)
            | IR::LessEqual(_, a, b)
            | IR::Index(_, a, b)
            | IR::In(_, a, b)
            | IR::Assign(a, b)
            | IR::AssignAccess(a, _, b)
            | IR::AssignIndex(_, a, b) => {
                *table.entry(*a).or_insert(0) += 1;
                *table.entry(*b).or_insert(0) += 1;
            }
            IR::Neg(_, a)
            | IR::Not(_, a)
            | IR::Assert(a)
            | IR::Variant(_, _, a)
            | IR::Access(_, a, _)
            | IR::Copy(_, a)
            | IR::Return(a)
            | IR::If(a) => {
                *table.entry(*a).or_insert(0) += 1;
            }

            IR::Call(_, a, bs) => {
                *table.entry(*a).or_insert(0) += 1;
                for b in bs.iter() {
                    *table.entry(*b).or_insert(0) += 1;
                }
            }
            IR::List(_, xs) | IR::Set(_, xs) | IR::Dict(_, xs) | IR::Tuple(_, xs) => {
                for x in xs.iter() {
                    *table.entry(*x).or_insert(0) += 1;
                }
            }
            IR::Blob(_, blob_vars) => {
                for (_, x) in blob_vars.iter() {
                    *table.entry(*x).or_insert(0) += 1;
                }
            }
        }
    }
    table
}
