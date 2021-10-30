// TODO(ed, er): If you see these during code-review, remind us to remove it.
#![allow(unused_variables)]
#![allow(unused_imports)]
#![allow(unused_macros)]

use std::collections::HashMap;
use std::path::PathBuf;
use sylt_common::error::{Error, TypeError};
use sylt_common::Type as RuntimeType;
use sylt_parser::{
    Assignable, AssignableKind, Expression, ExpressionKind, Identifier, Op as ParserOp, Span,
    Statement, StatementKind, Type as ParserType, TypeKind, VarKind,
};

use crate::{self as compiler, ty::Type, Context, Name as CompilerName};
use std::collections::BTreeSet;

macro_rules! type_error_if_invalid {
    ($self:expr, $ty:expr, $span:expr, $ctx: expr, $kind:expr, $( $msg:expr ),+ ) => {
        if matches!($ty, Type::Invalid) {
            return err_type_error!($self, $span, $ctx, $kind, $( $msg ),*);
        }
    };
    ($self:expr, $ty:expr, $span:expr, $ctx: expr, $kind:expr) => {
        if matches!($ty, Type::Invalid) {
            return err_type_error!($self, $span, $ctx, $kind);
        }
    };
}

macro_rules! err_type_error {
    ($self:expr, $span:expr, $ctx: expr, $kind:expr, $( $msg:expr ),+ ) => {
        Err(vec![type_error!($self, $span, $ctx, $kind, $($msg),*)])
    };
    ($self:expr, $span:expr, $ctx: expr, $kind:expr) => {
        Err(vec![type_error!($self, $span, $ctx, $kind)])
    };
}

macro_rules! type_error {
    ($self:expr, $span:expr, $ctx: expr, $kind:expr, $( $msg:expr ),+ ) => {
        Error::TypeError {
            kind: $kind,
            file: $self.namespace_to_file[&$ctx.namespace].clone(),
            span: $span,
            message: Some(format!($( $msg ),*)),
        }
    };
    ($self:expr, $span:expr, $ctx: expr, $kind:expr) => {
        Error::TypeError {
            kind: $kind,
            file: $self.namespace_to_file[&$ctx.namespace].clone(),
            span: $span,
            message: None,
        }
    };
}

#[derive(Clone, Debug)]
struct Variable {
    ident: Identifier,
    ty: usize,
    kind: VarKind,
}

#[derive(Clone, Debug)]
struct TypeNode {
    ty: Type,
    parent: Option<usize>,
    size: usize,
    constraints: BTreeSet<Constraint>,
}

#[derive(Clone, Copy, Debug, Hash, PartialOrd, Ord, PartialEq, Eq)]
enum Constraint {
    Add(usize),
}

struct TypeChecker {
    globals: HashMap<(usize, String), Name>,
    stack: Vec<Variable>,
    types: Vec<TypeNode>,
    namespace_to_file: HashMap<usize, PathBuf>,
}

#[derive(Clone, Debug, Copy)]
struct TypeCtx {
    namespace: usize,
}

#[derive(Debug, Clone)]
enum Name {
    Blob(Type),
    Global(Variable),
    Namespace(usize),
}

impl TypeChecker {
    fn new(namespace_to_file: &HashMap<usize, PathBuf>) -> Self {
        Self {
            globals: HashMap::new(),
            stack: Vec::new(),
            types: Vec::new(),
            namespace_to_file: namespace_to_file.clone(),
        }
    }

    fn push_type(&mut self, ty: Type) -> usize {
        let ty_id = self.types.len();
        self.types.push(TypeNode {
            ty,
            parent: None,
            size: 1,
            constraints: BTreeSet::new(),
        });
        ty_id
    }

    fn type_assignable(&mut self, assignable: &Assignable, ctx: TypeCtx) -> usize {
        match &assignable.kind {
            AssignableKind::Read(ident) => match self
                .globals
                .get(&(ctx.namespace, ident.name.clone()))
                .cloned()
                .unwrap()
            {
                Name::Blob(ty) => self.push_type(ty.clone()),
                _ => panic!(),
            },
            AssignableKind::Access(_, _) => todo!(),
            AssignableKind::Call(_, _) => todo!(),
            AssignableKind::ArrowCall(_, _, _) => todo!(),
            AssignableKind::Index(_, _) => todo!(),
            AssignableKind::Expression(_) => todo!(),
        }
    }

    fn resolve_type(&mut self, ty: &ParserType, ctx: TypeCtx) -> usize {
        use TypeKind::*;
        let ty = match &ty.kind {
            Implied => Type::Unknown,

            Resolved(ty) => match ty {
                sylt_common::Type::Void => Type::Void,
                sylt_common::Type::Unknown => Type::Unknown,
                sylt_common::Type::Int => Type::Int,
                sylt_common::Type::Float => Type::Float,
                sylt_common::Type::Bool => Type::Bool,
                sylt_common::Type::String => Type::Str,
                _ => todo!(),
            },

            UserDefined(assignable) => {
                return self.type_assignable(assignable, ctx);
            }
            // Union(a, b) => panic!(),
            Fn(params, ret) => {
                let params = params.iter().map(|t| self.resolve_type(t, ctx)).collect();
                let ret = self.resolve_type(ret, ctx);
                Type::Function(params, ret)
            }
            Tuple(fields) => {
                Type::Tuple(fields.iter().map(|t| self.resolve_type(t, ctx)).collect())
            }
            List(kind) => Type::List(self.resolve_type(kind, ctx)),
            Set(kind) => Type::Set(self.resolve_type(kind, ctx)),
            Dict(key, value) => {
                Type::Dict(self.resolve_type(key, ctx), self.resolve_type(value, ctx))
            }
            Grouping(ty) => {
                return self.resolve_type(ty, ctx);
            }

            Union(_, _) => todo!(),
            Generic(_) => todo!(),
        };
        self.push_type(ty)
    }

    fn statement(
        &mut self,
        statement: &Statement,
        ctx: TypeCtx,
    ) -> Result<Option<usize>, Vec<Error>> {
        let span = statement.span;
        match &statement.kind {
            StatementKind::Use { path, name, file } => todo!(),
            StatementKind::Blob { name, fields } => todo!(),

            StatementKind::Block { statements } => {
                let rets = self.push_type(Type::Unknown);
                for stmt in statements.iter() {
                    if let Some(ret) = self.statement(stmt, ctx)? {
                        self.unify(span, ctx, rets, ret)?;
                    }
                }
                Ok(Some(rets))
            }

            StatementKind::Ret { value } => Ok(Some(self.expression(value, ctx)?)),

            StatementKind::StatementExpression { value } => {
                self.expression(value, ctx)?;
                Ok(None)
            }

            StatementKind::Assignment {
                kind,
                target,
                value,
            } => todo!(),
            StatementKind::Definition {
                ident,
                kind,
                ty,
                value,
            } => todo!(),
            StatementKind::ExternalDefinition { ident, kind, ty } => todo!(),
            StatementKind::If {
                condition,
                pass,
                fail,
            } => todo!(),
            StatementKind::Loop { condition, body } => todo!(),
            StatementKind::Break => todo!(),
            StatementKind::Continue => todo!(),
            StatementKind::IsCheck { lhs, rhs } => todo!(),
            StatementKind::Unreachable => todo!(),
            StatementKind::EmptyStatement => Ok(None),
        }
    }

    fn outer_statement(&mut self, statement: &Statement, ctx: TypeCtx) -> Result<(), Vec<Error>> {
        let span = statement.span;
        match &statement.kind {
            StatementKind::Use { path, name, file } => todo!(),
            StatementKind::Blob { name, fields } => {
                let ty = Type::Blob(
                    name.clone(),
                    fields
                        .iter()
                        .map(|(k, v)| (k.clone(), self.resolve_type(v, ctx)))
                        .collect(),
                );
                self.globals
                    .insert((ctx.namespace, name.clone()), Name::Blob(ty));
            }

            StatementKind::Assignment {
                kind,
                target,
                value,
            } => todo!(),

            StatementKind::Definition {
                ident,
                kind,
                ty,
                value,
            } => {
                let expression_ty = self.expression(value, ctx)?;
                let defined_ty = self.resolve_type(&ty, ctx);
                let expression_ty = if matches!(self.find_type(defined_ty), Type::Unknown) {
                    // TODO(ed): Not sure this is needed
                    self.copy(expression_ty)
                } else {
                    expression_ty
                };
                self.unify(span, ctx, expression_ty, defined_ty)?;

                let var = Variable {
                    ident: ident.clone(),
                    ty: defined_ty,
                    kind: *kind,
                };
                self.globals
                    .insert((ctx.namespace, ident.name.clone()), Name::Global(var));
            }

            StatementKind::ExternalDefinition { ident, kind, ty } => todo!(),
            StatementKind::If {
                condition,
                pass,
                fail,
            } => todo!(),
            StatementKind::Loop { condition, body } => todo!(),
            StatementKind::Break => todo!(),
            StatementKind::Continue => todo!(),
            StatementKind::IsCheck { lhs, rhs } => todo!(),
            StatementKind::Ret { value } => todo!(),
            StatementKind::Block { statements } => todo!(),
            StatementKind::StatementExpression { value } => todo!(),
            StatementKind::Unreachable => todo!(),
            StatementKind::EmptyStatement => {}
        }
        Ok(())
    }

    fn assignable(&mut self, assignable: &Assignable, ctx: TypeCtx) -> Result<usize, Vec<Error>> {
        let span = assignable.span;
        match &assignable.kind {
            AssignableKind::Read(ident) => {
                if let Some(var) = self.stack.iter().rfind(|v| v.ident.name == ident.name) {
                    Ok(var.ty)
                } else {
                    match self.globals.get(&(ctx.namespace, ident.name.clone())) {
                        Some(Name::Global(var)) => Ok(var.ty),
                        _ => todo!(),
                    }
                }
            }

            AssignableKind::Call(f, args) => {
                let dbg = if let AssignableKind::Read(name) = &f.kind {
                    name.name == "dbg"
                } else {
                    false
                };

                let f = self.assignable(f, ctx)?;
                let f_copy = self.copy(f);
                if let Type::Function(params, ret) = self.find_type(f_copy) {
                    if args.len() != params.len() {
                        return err_type_error!(
                            self,
                            span,
                            ctx,
                            TypeError::WrongArity {
                                got: args.len(),
                                expected: params.len()
                            }
                        );
                    }
                    // TODO(ed): Annotate the errors?
                    for (a, p) in args.iter().zip(params.iter()) {
                        let a = self.expression(a, ctx)?;
                        if dbg {
                            eprintln!(">> {:?} {:?}", span.line, self.bake_type(a),);
                        }
                        self.unify(span, ctx, *p, a)?;
                        let a = self.find(a);
                    }
                    Ok(ret)
                } else {
                    return err_type_error!(
                        self,
                        span,
                        ctx,
                        TypeError::Violating(self.bake_type(f_copy)),
                        "Not callable"
                    );
                }
            }

            AssignableKind::ArrowCall(_, _, _) => todo!(),
            AssignableKind::Access(_, _) => todo!(),
            AssignableKind::Index(_, _) => todo!(),
            AssignableKind::Expression(_) => todo!(),
        }
    }

    fn expression(&mut self, expression: &Expression, ctx: TypeCtx) -> Result<usize, Vec<Error>> {
        let span = expression.span;
        match &expression.kind {
            ExpressionKind::Get(ass) => self.assignable(ass, ctx),

            ExpressionKind::Add(a, b) => {
                let a = self.expression(&a, ctx)?;
                let b = self.expression(&b, ctx)?;
                self.add_constraint(a, Constraint::Add(b));
                self.add_constraint(b, Constraint::Add(b));
                self.unify(span, ctx, a, b)?;
                Ok(a)
            }

            ExpressionKind::Sub(_, _) => todo!(),

            ExpressionKind::Mul(a, b) => todo!(),

            ExpressionKind::Div(_, _) => todo!(),
            ExpressionKind::Neg(_) => todo!(),
            ExpressionKind::Comparison(_, _, _) => todo!(),
            ExpressionKind::AssertEq(_, _) => todo!(),
            ExpressionKind::And(_, _) => todo!(),
            ExpressionKind::Or(_, _) => todo!(),
            ExpressionKind::Not(_) => todo!(),
            ExpressionKind::Parenthesis(expr) => self.expression(expr, ctx),
            ExpressionKind::IfExpression {
                condition,
                pass,
                fail,
            } => todo!(),

            ExpressionKind::Function {
                name: _,
                params,
                ret,
                body,
            } => {
                let ss = self.stack.len();
                let mut args = Vec::new();
                for (ident, ty) in params.iter() {
                    let ty = self.resolve_type(ty, ctx);
                    args.push(ty);

                    let var = Variable {
                        ident: ident.clone(),
                        ty,
                        kind: VarKind::Const,
                    };
                    self.stack.push(var);
                }

                let ret = self.resolve_type(ret, ctx);
                if let Some(actual_ret) = self.statement(body, ctx)? {
                    self.unify(span, ctx, ret, actual_ret)?;
                } else {
                    panic!();
                }

                Ok(self.push_type(Type::Function(args, ret)))
            }

            ExpressionKind::Blob { blob, fields } => {
                // TODO: check the fields
                Ok(self.type_assignable(blob, ctx))
            }

            ExpressionKind::Tuple(exprs) => {
                let mut tys = Vec::new();
                for expr in exprs.iter() {
                    tys.push(self.expression(expr, ctx)?);
                }
                Ok(self.push_type(Type::Tuple(tys)))
            }

            ExpressionKind::List(exprs) => {
                let inner_ty = self.push_type(Type::Unknown);
                for expr in exprs.iter() {
                    let e = self.expression(expr, ctx)?;
                    self.unify(span, ctx, inner_ty, e)?;
                }
                Ok(self.push_type(Type::List(inner_ty)))
            }

            ExpressionKind::Set(_) => todo!(),
            ExpressionKind::Dict(_) => todo!(),

            ExpressionKind::Int(_) => Ok(self.push_type(Type::Int)),
            ExpressionKind::Float(_) => Ok(self.push_type(Type::Float)),
            ExpressionKind::Str(_) => Ok(self.push_type(Type::Str)),
            ExpressionKind::Bool(_) => Ok(self.push_type(Type::Bool)),
            ExpressionKind::Nil => Ok(self.push_type(Type::Void)),
        }
    }

    fn find(&mut self, a: usize) -> usize {
        let mut root = a;
        while let Some(next) = self.types[root].parent {
            root = next;
        }

        let mut node = a;
        while let Some(next) = self.types[node].parent {
            self.types[node].parent = Some(root);
            node = next;
        }

        root
    }

    fn bake_type(&mut self, a: usize) -> RuntimeType {
        match self.find_type(a) {
            Type::Unknown => RuntimeType::Unknown,
            Type::Ty => RuntimeType::Ty,
            Type::Void => RuntimeType::Ty,
            Type::Int => RuntimeType::Int,
            Type::Float => RuntimeType::Float,
            Type::Bool => RuntimeType::Bool,
            Type::Str => RuntimeType::String,
            Type::Tuple(tys) => {
                RuntimeType::Tuple(tys.iter().map(|ty| self.bake_type(*ty)).collect())
            }
            Type::List(ty) => RuntimeType::List(Box::new(self.bake_type(ty))),
            Type::Set(ty) => RuntimeType::Set(Box::new(self.bake_type(ty))),
            Type::Dict(ty_k, ty_v) => RuntimeType::Dict(
                Box::new(self.bake_type(ty_k)),
                Box::new(self.bake_type(ty_v)),
            ),
            Type::Function(args, ret) => RuntimeType::Function(
                args.iter().map(|ty| self.bake_type(*ty)).collect(),
                Box::new(self.bake_type(ret)),
            ),
            Type::Blob(name, fields) => RuntimeType::Blob(
                name.clone(),
                fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.bake_type(*ty)))
                    .collect(),
            ),

            Type::Invalid => RuntimeType::Invalid,
        }
    }

    // This span is wierd - is it weird?
    fn check_constraints(&mut self, span: Span, ctx: TypeCtx, a: usize) -> Result<(), Vec<Error>> {
        let a = self.find(a);
        for constraint in self.types[a].constraints.clone().iter() {
            match constraint {
                // It would be nice to know from where this came from
                Constraint::Add(b) => {
                    self.add(span, ctx, a, *b)?;
                }
            }
        }
        Ok(())
    }

    fn find_type(&mut self, a: usize) -> Type {
        let ta = self.find(a);
        self.types[ta].ty.clone()
    }

    fn union(&mut self, a: usize, b: usize) {
        let a = self.find(a);
        let b = self.find(b);

        if a == b {
            return;
        }

        let (a, b) = if self.types[a].size < self.types[b].size {
            (b, a)
        } else {
            (a, b)
        };

        self.types[b].parent = Some(a);
        self.types[a].size += self.types[b].size;
        self.types[a].constraints = self.types[a]
            .constraints
            .union(&self.types[b].constraints)
            .cloned()
            .collect();
    }

    fn unify(&mut self, span: Span, ctx: TypeCtx, a: usize, b: usize) -> Result<usize, Vec<Error>> {
        let a = self.find(a);
        let b = self.find(b);

        match (self.find_type(a), self.find_type(b)) {
            (_, Type::Unknown) => self.types[b].ty = self.find_type(a),

            (Type::Unknown, _) => self.types[a].ty = self.find_type(b),

            _ => match (self.find_type(a), self.find_type(b)) {
                (Type::Ty, Type::Ty) => {}
                (Type::Void, Type::Void) => {}
                (Type::Int, Type::Int) => {}
                (Type::Float, Type::Float) => {}
                (Type::Bool, Type::Bool) => {}
                (Type::Str, Type::Str) => {}

                (Type::List(a), Type::List(b)) => {
                    self.unify(span, ctx, a, b)?;
                }
                (Type::Set(a), Type::Set(b)) => {
                    self.unify(span, ctx, a, b)?;
                }
                (Type::Dict(a_k, a_v), Type::Dict(b_k, b_v)) => {
                    self.unify(span, ctx, a_k, b_k)?;
                    self.unify(span, ctx, a_v, b_v)?;
                }

                (Type::Tuple(a), Type::Tuple(b)) => {
                    for (a, b) in a.iter().zip(b.iter()) {
                        self.unify(span, ctx, *a, *b)?;
                    }
                }

                (Type::Function(a_args, a_ret), Type::Function(b_args, b_ret)) => {
                    for (a, b) in a_args.iter().zip(b_args.iter()) {
                        self.unify(span, ctx, *a, *b)?;
                    }
                    self.unify(span, ctx, a_ret, b_ret)?;
                }

                (Type::Blob(a_blob, a_field), Type::Blob(b_blob, b_field)) => {
                    for (a_name, a_ty) in a_field.iter() {
                        let b_ty = b_field[a_name];
                        self.unify(span, ctx, *a_ty, b_ty)?;
                    }
                }

                _ => {
                    return err_type_error!(
                        self,
                        span,
                        ctx,
                        TypeError::Mismatch {
                            got: self.bake_type(a),
                            expected: self.bake_type(b),
                        },
                        "Types don't match"
                    );
                }
            },
        }

        self.union(a, b);

        self.check_constraints(span, ctx, a)?;
        self.check_constraints(span, ctx, b)?;

        Ok(a)
    }

    fn print_type(&mut self, ty: usize) {
        let ty = self.find(ty);
        let mut same = BTreeSet::new();
        for i in 0..self.types.len() {
            if self.find(i) == ty {
                same.insert(i);
            }
        }
        eprintln!(
            "{}: {:?} {:?} = {:?}",
            ty,
            self.bake_type(ty),
            self.types[ty].constraints,
            same
        );
    }

    fn inner_copy(&mut self, old_ty: usize, seen: &mut HashMap<usize, usize>) -> usize {
        if let Some(res) = seen.get(&old_ty) {
            return *res;
        }
        let new_ty = self.push_type(Type::Unknown);
        self.types[new_ty].constraints = self.types[old_ty].constraints.clone();
        seen.insert(old_ty, new_ty);

        let ty = self.find_type(old_ty);
        self.types[new_ty].ty = match ty {
            Type::Invalid
            | Type::Unknown
            | Type::Ty
            | Type::Void
            | Type::Int
            | Type::Float
            | Type::Bool
            | Type::Str => ty,

            Type::Tuple(tys) => {
                Type::Tuple(tys.iter().map(|ty| self.inner_copy(*ty, seen)).collect())
            }

            Type::List(ty) => Type::List(self.inner_copy(ty, seen)),
            Type::Set(ty) => Type::Set(self.inner_copy(ty, seen)),

            Type::Dict(ty_k, ty_v) => {
                Type::Dict(self.inner_copy(ty_k, seen), self.inner_copy(ty_v, seen))
            }

            Type::Function(args, ret) => Type::Function(
                args.iter().map(|ty| self.inner_copy(*ty, seen)).collect(),
                self.inner_copy(ret, seen),
            ),

            // TODO(ed): We can cheat here and just copy the table directly.
            Type::Blob(name, fields) => Type::Blob(
                name.clone(),
                fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.inner_copy(*ty, seen)))
                    .collect(),
            ),
        };
        new_ty
    }

    fn copy(&mut self, ty: usize) -> usize {
        let mut seen = HashMap::new();
        self.inner_copy(ty, &mut seen)
    }

    fn add_constraint(&mut self, a: usize, constraint: Constraint) {
        let a = self.find(a);
        self.types[a].constraints.insert(constraint);
    }

    fn add(&mut self, span: Span, ctx: TypeCtx, a: usize, b: usize) -> Result<(), Vec<Error>> {
        match (self.find_type(a), self.find_type(b)) {
            // TODO(ed): We can't prove it's not possible, right?
            // This needs to be reasoned about later some how...
            (Type::Unknown, Type::Unknown) => Ok(()),

            // Make a guess at the type
            (Type::Unknown, _) => Ok(()),
            (_, Type::Unknown) => Ok(()),

            (Type::Float, Type::Float) => Ok(()),
            (Type::Int, Type::Int) => Ok(()),
            (Type::Str, Type::Str) => Ok(()),

            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b.iter()) {
                    self.add(span, ctx, *a, *b)?;
                }
                Ok(())
            }

            _ => {
                return err_type_error!(
                    self,
                    span,
                    ctx,
                    TypeError::BinOp {
                        lhs: self.bake_type(a),
                        rhs: self.bake_type(b),
                        op: "+".to_string(),
                    }
                )
            }
        }
    }

    fn solve(&mut self, statements: &Vec<(&Statement, usize)>) -> Result<(), Vec<Error>> {
        for (statement, namespace) in statements.iter() {
            self.outer_statement(
                statement,
                TypeCtx {
                    namespace: *namespace,
                },
            )?;
        }

        Ok(())
    }
}

pub(crate) fn solve(
    statements: &Vec<(&Statement, usize)>,
    namespace_to_file: &HashMap<usize, PathBuf>,
) -> Result<(), Vec<Error>> {
    TypeChecker::new(namespace_to_file).solve(statements)
}

/*
/// Module with all the operators that can be applied
/// to values.
///
/// Broken out because they need to be recursive.
mod constraints {
    // TODO(ed): Fix this
    use super::Type;
    use std::collections::BTreeSet;

    fn tuple_bin_op(a: &Vec<Type>, b: &Vec<Type>, f: fn(&Type, &Type) -> Type) -> Type {
        Type::Tuple(a.iter().zip(b.iter()).map(|(a, b)| f(a, b)).collect())
    }

    fn tuple_un_op<T>(a: &Vec<Type>, f: T) -> Type
    where
        T: FnMut(&Type) -> Type,
    {
        Type::Tuple(a.iter().map(f).collect())
    }

    fn union_bin_op(a: &BTreeSet<Type>, b: &Type, f: fn(&Type, &Type) -> Type) -> Type {
        a.iter()
            .find_map(|x| {
                let x = f(x, b);
                if matches!(x, Type::Void) {
                    None
                } else {
                    Some(x)
                }
            })
            .unwrap_or(Type::Invalid)
    }

    pub fn neg(value: &Type) -> Type {
        match value {
            Type::Float => Type::Float,
            Type::Int => Type::Int,
            Type::Tuple(a) => tuple_un_op(a, neg),
            Type::Unknown => Type::Unknown,
            _ => Type::Invalid,
        }
    }

    pub fn not(value: &Type) -> Type {
        match value {
            Type::Bool => Type::Bool,
            Type::Tuple(a) => tuple_un_op(a, not),
            Type::Unknown => Type::Bool,
            _ => Type::Invalid,
        }
    }

    pub fn sub(a: &Type, b: &Type) -> Type {
        add(a, &neg(b))
    }

    pub fn mul(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Float, Type::Float) => Type::Float,
            (Type::Int, Type::Int) => Type::Int,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, mul),
            (Type::Tuple(a), b) | (b, Type::Tuple(a)) => tuple_un_op(a, |t| mul(t, b)),
            _ => Type::Invalid,
        }
    }

    pub fn div(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Float, Type::Float) => Type::Float,
            (Type::Int, Type::Int) => Type::Int,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, div),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => div(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            _ => Type::Invalid,
        }
    }

    pub fn eq(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Float, Type::Float) => Type::Bool,
            (Type::Int, Type::Int) => Type::Bool,
            (Type::Str, Type::Str) => Type::Bool,
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => a
                .iter()
                .zip(b.iter())
                .find_map(|(a, b)| match eq(a, b) {
                    Type::Bool => None,
                    a => Some(a),
                })
                .unwrap_or(Type::Bool),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => eq(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            // (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, eq),
            (Type::Void, Type::Void) => Type::Bool,
            (Type::List(a), Type::List(b)) => eq(a, b),
            (Type::Set(a), Type::Set(b)) => eq(a, b),
            (Type::Dict(a, b), Type::Dict(c, d)) if matches!(eq(a, c), Type::Bool) => eq(b, d),
            _ => Type::Invalid,
        }
    }

    pub fn cmp(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Float, Type::Float)
            | (Type::Int, Type::Int)
            | (Type::Float, Type::Int)
            | (Type::Int, Type::Float) => Type::Bool,
            (Type::Str, Type::Str) => Type::Bool,
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => a
                .iter()
                .zip(b.iter())
                .find_map(|(a, b)| match cmp(a, b) {
                    Type::Bool => None,
                    a => Some(a),
                })
                .unwrap_or(Type::Bool),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => cmp(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            _ => Type::Invalid,
        }
    }

    pub fn and(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, and),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => and(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            _ => Type::Invalid,
        }
    }

    pub fn or(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, or),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => or(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            _ => Type::Invalid,
        }
    }
}
*/
