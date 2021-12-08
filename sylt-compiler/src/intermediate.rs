#![allow(unused_variables, unused_imports)]
use std::collections::HashMap;
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

#[derive(Debug, Clone)]
pub enum IR {
    Nil(Var),
    Int(Var, i64),
    Bool(Var, bool),
    Add(Var, Var, Var),
    Sub(Var, Var, Var),

    // Name?
    FunctionBegin(Var, Vec<Var>),
    FunctionEnd,
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

struct IRCodeGen<'a> {
    typechecker: &'a TypeChecker,
    namespace_to_file: HashMap<NamespaceID, FileOrLib>,
    // TODO(ed): This can probably be removed via some trickery
    file_to_namespace: HashMap<FileOrLib, NamespaceID>,
    counter: usize,
}

impl<'a> IRCodeGen<'a> {
    fn new(
        typechecker: &'a TypeChecker,
        namespace_to_file: &HashMap<NamespaceID, FileOrLib>,
    ) -> Self {
        Self {
            counter: 0,
            typechecker,
            namespace_to_file: namespace_to_file.clone(),
            file_to_namespace: namespace_to_file
                .iter()
                .map(|(a, b)| (b.clone(), a.clone()))
                .collect(),
        }
    }

    fn var(&mut self) -> Var {
        let i = self.counter;
        self.counter += 1;
        Var(i)
    }

    fn expression(&mut self, expr: &Expression, ctx: IRContext) -> (Vec<IR>, Var) {
        match &expr.kind {
            ExpressionKind::Get(_) => todo!(),
            ExpressionKind::Mul(_, _) => todo!(),
            ExpressionKind::Div(_, _) => todo!(),
            ExpressionKind::Neg(_) => todo!(),
            ExpressionKind::Comparison(_, _, _) => todo!(),
            ExpressionKind::AssertEq(_, _) => todo!(),
            ExpressionKind::And(_, _) => todo!(),
            ExpressionKind::Or(_, _) => todo!(),
            ExpressionKind::Not(_) => todo!(),
            ExpressionKind::Parenthesis(_) => todo!(),
            ExpressionKind::IfExpression { .. } => todo!(),
            ExpressionKind::Blob { .. } => todo!(),
            ExpressionKind::Tuple(_) => todo!(),
            ExpressionKind::List(_) => todo!(),
            ExpressionKind::Set(_) => todo!(),
            ExpressionKind::Dict(_) => todo!(),
            ExpressionKind::Float(_) => todo!(),
            ExpressionKind::Str(_) => todo!(),

            ExpressionKind::Bool(b) => {
                let a = self.var();
                (vec![IR::Bool(a, *b)], a)
            }

            ExpressionKind::Function { body, params, .. } => {
                let a = self.var();
                let params = params.iter().map(|_| self.var()).collect();
                let body = self.statement(body, ctx);
                (
                    [vec![IR::FunctionBegin(a, params)], body, vec![IR::FunctionEnd]].concat(),
                    self.var(),
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
        }
    }

    fn statement(&mut self, stmt: &Statement, ctx: IRContext) -> Vec<IR> {
        match &stmt.kind {
            StatementKind::Use { path, name, file } => todo!(),
            StatementKind::FromUse { path, imports, file } => todo!(),
            StatementKind::Blob { name, fields } => todo!(),
            StatementKind::Enum { name, variants } => todo!(),
            StatementKind::Assignment { kind, target, value } => todo!(),
            StatementKind::Definition { ident, kind, ty, value } => todo!(),
            StatementKind::ExternalDefinition { ident, kind, ty } => todo!(),
            StatementKind::If { condition, pass, fail } => todo!(),
            StatementKind::Case { to_match, branches, fall_through } => todo!(),
            StatementKind::Loop { condition, body } => todo!(),
            StatementKind::Break => todo!(),
            StatementKind::Continue => todo!(),
            StatementKind::IsCheck { lhs, rhs } => todo!(),
            StatementKind::Ret { value } => todo!(),
            StatementKind::Unreachable => todo!(),

            StatementKind::StatementExpression { value } => self.expression(value, ctx).0,
            StatementKind::EmptyStatement => Vec::new(),
            StatementKind::Block { statements } => statements
                .iter()
                .map(|stmt| self.statement(stmt, ctx))
                .flatten()
                .collect(),
        }
    }

    fn compile(&mut self, stmt: &Statement, namespace: NamespaceID) -> Vec<IR> {
        let ctx = IRContext::from_namespace(namespace);
        match &stmt.kind {
            StatementKind::Use { .. } => todo!(),
            StatementKind::FromUse { .. } => todo!(),
            StatementKind::Blob { .. } => todo!(),
            StatementKind::Enum { .. } => todo!(),
            StatementKind::ExternalDefinition { .. } => todo!(),

            StatementKind::Definition { value, .. } => self.expression(&value, ctx).0,

            _ => unreachable!("Not a valid outer statement"),
        }
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
