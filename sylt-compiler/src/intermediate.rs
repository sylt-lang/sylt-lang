#![allow(unused_variables, unused_imports)]
use std::collections::HashMap;
use std::fmt::Display;
use sylt_common::error::{Error, Helper, TypeError};
use sylt_common::{FileOrLib, TyID, Type as RuntimeType};
use sylt_parser::{
    expression::ComparisonKind, Assignable, AssignableKind, Expression, ExpressionKind, Identifier,
    Op as ParserOp, Span, Statement, StatementKind, Type as ParserType, TypeAssignable,
    TypeAssignableKind, TypeConstraint, TypeKind, VarKind,
};

use crate::{ty::Type, typechecker::TypeChecker, NamespaceID};

#[derive(Debug, Clone, Copy)]
pub struct Var(pub usize);

impl Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Var(n) = self;
        write!(f, "V{}", n)
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
    Copy(Var, Var),

    And(Var, Var, Var),
    Or(Var, Var, Var),
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

    Define(Var),
    Assign(Var, Var),
    Return(Var),
    If(Var),
    HaltAndCatchFire(String),
    Loop,
    Break,
    Continue,
    Else,
    End,
}

// 1 + 1
//
// t0 = 1
// t1 = 1
// t2 = t0 + t1
//
// if 1 + 1 == 2 do ...
//
// t0 = 1
// t1 = 1
// t2 = t0 + t1
// t3 = 2
// t4 = t2 == t3
// t5 = nil
// if t4 then
//  ...
//  t5 = t???
// else
//  ...
//  t5 = t???
// end
// t5

#[derive(Debug, Clone, Copy)]
struct IRContext {
    namespace: usize,
}

impl IRContext {
    pub fn from_namespace(namespace: usize) -> Self {
        Self { namespace }
    }
}

struct Variable {
    name: String,
    namespace: NamespaceID,
    var: Var,
}

struct IRCodeGen<'a> {
    typechecker: &'a TypeChecker,
    variables: Vec<Variable>,
    counter: usize,
}

impl<'a> IRCodeGen<'a> {
    fn new(typechecker: &'a TypeChecker) -> Self {
        Self { counter: 0, typechecker, variables: Vec::new() }
    }

    fn var(&mut self) -> Var {
        let i = self.counter;
        self.counter += 1;
        Var(i)
    }

    fn assignable(&mut self, assignable: &Assignable, ctx: IRContext) -> (Vec<IR>, Var) {
        match &assignable.kind {
            AssignableKind::Read(ident) => (
                Vec::new(),
                self.variables
                    .iter()
                    .rfind(|Variable { name, namespace, .. }| {
                        namespace == &ctx.namespace && name == &ident.name
                    })
                    .unwrap()
                    .var,
            ),
            AssignableKind::Variant { variant, value, .. } => {
                let (xops, x) = self.expression(&value, ctx);
                let v = self.var();
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
                let (extra_code, extra)  = self.expression(extra, ctx);
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
            AssignableKind::Access(_, _) => todo!(),
            AssignableKind::Index(_, _) => todo!(),
            AssignableKind::Expression(_) => todo!(),
        }
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
                ([aops, bops, vec![IR::And(c, a, b)]].concat(), c)
            }
            ExpressionKind::Or(a, b) => {
                let (aops, a) = self.expression(&a, ctx);
                let (bops, b) = self.expression(&b, ctx);
                let c = self.var();
                ([aops, bops, vec![IR::Or(c, a, b)]].concat(), c)
            }
            ExpressionKind::Not(a) => {
                let (aops, a) = self.expression(&a, ctx);
                let b = self.var();
                ([aops, vec![IR::Not(b, a)]].concat(), b)
            }

            ExpressionKind::IfExpression { condition, pass, fail } => {
                let (cops, c) = self.expression(&condition, ctx);
                let (aops, a) = self.expression(&pass, ctx);
                let (bops, b) = self.expression(&fail, ctx);
                let var = self.var();

                (
                    [
                        cops,
                        vec![IR::Define(var), IR::If(c)],
                        aops,
                        vec![IR::Assign(var, a), IR::Else],
                        bops,
                        vec![IR::Assign(var, b), IR::End],
                    ]
                    .concat(),
                    var,
                )
            }

            ExpressionKind::Blob { fields, .. } => {
                let (fields, (code, exprs)): (Vec<_>, (Vec<_>, Vec<_>)) = fields
                    .iter()
                    .map(|(field, expr)| (field.clone(), self.expression(expr, ctx)))
                    .unzip();
                let code = code.concat();
                let fields: Vec<_> = fields.into_iter().zip(exprs.into_iter()).collect();
                let var = self.var();

                ([code, vec![IR::Blob(var, fields)]].concat(), var)
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

            ExpressionKind::Function { body, params, .. } => {
                let ss = self.variables.len();
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
                let f = self.var();
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

    fn statement(&mut self, stmt: &Statement, ctx: IRContext) -> Vec<IR> {
        match &stmt.kind {
            StatementKind::Assignment { kind, target, value } => {
                let (ass_code, ass_var) = self.assignable(target, ctx);
                let (code, var) = self.expression(&value, ctx);
                let temp = self.var();
                [
                    ass_code,
                    code,
                    vec![
                        IR::Define(temp),
                        match kind {
                            ParserOp::Nop => IR::Assign(temp, var),
                            ParserOp::Add => IR::Add(temp, ass_var, var),
                            ParserOp::Sub => IR::Sub(temp, ass_var, var),
                            ParserOp::Mul => IR::Mul(temp, ass_var, var),
                            ParserOp::Div => IR::Div(temp, ass_var, var),
                        },
                        IR::Assign(ass_var, temp),
                    ],
                ]
                .concat()
            }
            StatementKind::Definition { ident, value, .. } => {
                let (code, var) = self.expression(&value, ctx);
                self.variables.push(Variable {
                    name: ident.name.clone(),
                    namespace: ctx.namespace,
                    var,
                });
                code
            }
            StatementKind::If { condition, pass, fail } => {
                let (cops, c) = self.expression(&condition, ctx);
                let aops = self.statement(&pass, ctx);
                let bops = self.statement(&fail, ctx);
                let var = self.var();

                [
                    cops,
                    vec![IR::If(c)],
                    aops,
                    vec![IR::Else],
                    bops,
                    vec![IR::End],
                ]
                .concat()
            }
            StatementKind::Case { to_match, branches, fall_through } => todo!(),
            StatementKind::Loop { condition, body } => {
                let (cops, c) = self.expression(&condition, ctx);
                let body = self.statement(&body, ctx);

                [
                    vec![IR::Loop],
                    cops,
                    vec![IR::If(c), IR::Else, IR::Break, IR::End],
                    body,
                    vec![IR::End],
                ]
                .concat()
            }
            StatementKind::Break => vec![IR::Break],
            StatementKind::Continue => vec![IR::Continue],
            StatementKind::Ret { value } => {
                let (aops, a) = self.expression(&value, ctx);
                [aops, vec![IR::Return(a)]].concat()
            }
            StatementKind::Unreachable => {
                vec![IR::HaltAndCatchFire("Reached unreachable code!".into())]
            }

            StatementKind::StatementExpression { value } => self.expression(value, ctx).0,
            StatementKind::Block { statements } => {
                let ss = self.variables.len();
                let code = statements
                    .iter()
                    .map(|stmt| self.statement(stmt, ctx))
                    .flatten()
                    .collect();
                self.variables.truncate(ss);
                code
            }

            StatementKind::EmptyStatement => Vec::new(),

            StatementKind::Blob { .. }
            | StatementKind::Enum { .. }
            | StatementKind::ExternalDefinition { .. }
            | StatementKind::FromUse { .. }
            | StatementKind::IsCheck { .. }
            | StatementKind::Use { .. } => unreachable!(),
        }
    }

    fn compile(&mut self, stmt: &Statement, namespace: NamespaceID) -> Vec<IR> {
        let ctx = IRContext::from_namespace(namespace);
        match &stmt.kind {
            StatementKind::ExternalDefinition { ident, .. } => {
                let var = self.var();
                self.variables.push(Variable {
                    name: ident.name.clone(),
                    namespace: ctx.namespace,
                    var,
                });
                vec![IR::External(var, ident.name.clone())]
            }

            StatementKind::Definition { value, ident, .. } => {
                let (code, var) = self.expression(&value, ctx);
                self.variables.push(Variable {
                    name: ident.name.clone(),
                    namespace: ctx.namespace,
                    var,
                });
                code
            }

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
