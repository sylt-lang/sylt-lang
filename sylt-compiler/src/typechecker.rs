#![allow(unused_variables)]
#![allow(unused_imports)]
use std::collections::HashMap;
use std::path::PathBuf;
use sylt_common::error::{Error, TypeError};
use sylt_common::Type;
use sylt_parser::{
    Assignable, AssignableKind, Expression, ExpressionKind, Identifier, Op as ParserOp, Span,
    Statement, StatementKind, Type as ParserType, TypeKind, VarKind,
};

use crate::{self as compiler, first_ok_or_errs, Context, Name as CompilerName};

//macro_rules! type_error_if_invalid {
//    ($self:expr, $ty:expr, $span:expr, $kind:expr, $( $msg:expr ),+ ) => {
//        if matches!($ty, Type::Invalid) {
//            return err_type_error!($self, $span, $kind, $( $msg ),*);
//        }
//    };
//    ($self:expr, $ty:expr, $span:expr, $kind:expr) => {
//        if matches!($ty, Type::Invalid) {
//            return err_type_error!($self, $span, $kind);
//        }
//    };
//}
//
//macro_rules! err_type_error {
//    ($self:expr, $span:expr, $kind:expr, $( $msg:expr ),+ ) => {
//        Err(vec![Error::TypeError {
//            kind: $kind,
//            file: $self.file(),
//            span: $span,
//            message: Some(format!($( $msg ),*)),
//        }])
//    };
//    ($self:expr, $span:expr, $kind:expr) => {
//        Err(vec![Error::TypeError {
//            kind: $kind,
//            file: $self.file(),
//            span: $span,
//            message: None,
//        }])
//    };
//}

macro_rules! type_error {
    ($self:expr, $span:expr, $ctx: expr, $kind:expr, $( $msg:expr ),+ ) => {
        Error::TypeError {
            kind: $kind,
            file: $self.namespace_to_file[&$ctx.namespace].clone(),
            span: $span,
            message: Some(format!($( $msg ),*)),
        }
    };
    ($self:expr, $span:expr, $kind:expr) => {
        Error::TypeError {
            kind: $kind,
            file: $self.namespace_to_file[&$ctx.namespace],
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

impl Variable {
    fn new(ident: Identifier, ty: usize, kind: VarKind) -> Self {
        Self { ident, ty, kind }
    }
}

struct TypeNode {
    ty: Type,
    parent: Option<usize>,
    size: usize,
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

    fn type_assignable(&self, assignable: &Assignable, ctx: TypeCtx) -> Type {
        match &assignable.kind {
            AssignableKind::Read(ident) => match self.globals.get(&(ctx.namespace, ident.name.clone())).unwrap() {
                Name::Blob(ty) => ty.clone(),
                _ => panic!(),
            },
            AssignableKind::Access(_, _) => todo!(),
            AssignableKind::Call(_, _) => todo!(),
            AssignableKind::ArrowCall(_, _, _) => todo!(),
            AssignableKind::Index(_, _) => todo!(),
            AssignableKind::Expression(_) => todo!(),
        }
    }

    fn resolve_type(&self, ty: &ParserType, ctx: TypeCtx) -> Type {
        use TypeKind::*;
        match &ty.kind {
            Implied => Type::Unknown,
            Resolved(ty) => ty.clone(),
            UserDefined(assignable) => self.type_assignable(assignable, ctx),
            Union(a, b) => match (self.resolve_type(a, ctx), self.resolve_type(b, ctx)) {
                (Type::Union(_), _) => panic!("Didn't expect union on RHS - check parser"),
                (a, Type::Union(mut us)) => {
                    us.insert(a);
                    Type::Union(us)
                }
                (a, b) => Type::Union(vec![a, b].into_iter().collect()),
            },
            Fn(params, ret) => {
                let params = params.iter().map(|t| self.resolve_type(t, ctx)).collect();
                let ret = Box::new(self.resolve_type(ret, ctx));
                Type::Function(params, ret)
            }
            Tuple(fields) => {
                Type::Tuple(fields.iter().map(|t| self.resolve_type(t, ctx)).collect())
            }
            List(kind) => Type::List(Box::new(self.resolve_type(kind, ctx))),
            Set(kind) => Type::Set(Box::new(self.resolve_type(kind, ctx))),
            Dict(key, value) => Type::Dict(
                Box::new(self.resolve_type(key, ctx)),
                Box::new(self.resolve_type(value, ctx)),
            ),
            Generic(name) => Type::Generic(name.name.clone()),
            Grouping(ty) => self.resolve_type(ty, ctx),
        }
    }

    fn outer_statement(&mut self, statement: &Statement, ctx: TypeCtx) -> Result<(), Vec<Error>> {
        let span = statement.span;
        match &statement.kind {
            StatementKind::Use { path, name, file } => todo!(),
            StatementKind::Blob { name, fields } => {
                let ty = Type::Blob(
                    name.clone(),
                    fields.iter()
                        .map(|(k, v)| (k.clone(), self.resolve_type(v, ctx)))
                        .collect()
                );
                self.globals.insert((ctx.namespace, name.clone()), Name::Blob(ty));
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
                let ty = match self.resolve_type(&ty, ctx) {
                    Type::Unknown => expression_ty,
                    x => {
                        let defined_ty = self.types.len();
                        let ty = TypeNode {
                            ty: x,
                            parent: None,
                            size: 1,
                        };
                        self.types.push(ty);
                        self.check_wider(span, ctx, expression_ty, defined_ty)?;
                        defined_ty
                    }
                };

                let var = Variable {
                    ident: ident.clone(),
                    ty,
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
            StatementKind::EmptyStatement => todo!(),
        }
        Ok(())
    }

    fn expression(&mut self, expression: &Expression, ctx: TypeCtx) -> Result<usize, Vec<Error>> {
        let span = expression.span;
        match &expression.kind {
            ExpressionKind::Get(ass) => match &ass.kind {
                AssignableKind::Read(ident) => {
                    match self.globals.get(&(ctx.namespace, ident.name.clone())) {
                        Some(Name::Global(var)) => Ok(var.ty),
                        _ => todo!(),
                    }
                }

                AssignableKind::Call(_, _) => todo!(),
                AssignableKind::ArrowCall(_, _, _) => todo!(),
                AssignableKind::Access(_, _) => todo!(),
                AssignableKind::Index(_, _) => todo!(),
                AssignableKind::Expression(_) => todo!(),
            },

            ExpressionKind::Add(a, b) => {
                let a = self.expression(&a, ctx)?;
                let b = self.expression(&b, ctx)?;
                self.unify(span, ctx, a, b)?;
                Ok(a)
            }

            ExpressionKind::Sub(_, _) => todo!(),
            ExpressionKind::Mul(_, _) => todo!(),
            ExpressionKind::Div(_, _) => todo!(),
            ExpressionKind::Neg(_) => todo!(),
            ExpressionKind::Comparison(_, _, _) => todo!(),
            ExpressionKind::AssertEq(_, _) => todo!(),
            ExpressionKind::And(_, _) => todo!(),
            ExpressionKind::Or(_, _) => todo!(),
            ExpressionKind::Not(_) => todo!(),
            ExpressionKind::Parenthesis(_) => todo!(),
            ExpressionKind::IfExpression {
                condition,
                pass,
                fail,
            } => todo!(),
            ExpressionKind::Function {
                name,
                params,
                ret,
                body,
            } => Ok(0),
            ExpressionKind::Blob { blob, fields } => {
                // TODO: check the fields
                let ty = self.types.len();
                self.types.push(TypeNode {
                    ty: self.type_assignable(blob, ctx),
                    parent: None,
                    size: 1,
                });
                Ok(ty)
            },
            ExpressionKind::Tuple(_) => todo!(),
            ExpressionKind::List(_) => todo!(),
            ExpressionKind::Set(_) => todo!(),
            ExpressionKind::Dict(_) => todo!(),
            ExpressionKind::Float(_) => todo!(),

            ExpressionKind::Int(_) => {
                let ty = self.types.len();
                self.types.push(TypeNode {
                    ty: Type::Int,
                    parent: None,
                    size: 1,
                });
                Ok(ty)
            }

            ExpressionKind::Str(_) => {
                let ty = self.types.len();
                self.types.push(TypeNode {
                    ty: Type::String,
                    parent: None,
                    size: 1,
                });
                Ok(ty)
            }

            ExpressionKind::Bool(_) => todo!(),
            ExpressionKind::Nil => todo!(),
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
    }

    fn unify(&mut self, span: Span, ctx: TypeCtx, a: usize, b: usize) -> Result<(), Vec<Error>> {
        let a = self.find(a);
        let b = self.find(b);

        let ta = &self.types[a].ty;
        let tb = &self.types[b].ty;

        // TODO
        match (ta.fits(tb), tb.fits(ta)) {
            (Ok(_), Ok(_)) => {}
            (Ok(_), _) => self.types[b].ty = ta.clone(),
            (_, Ok(_)) => self.types[a].ty = tb.clone(),
            (Err(a_err), Err(b_err)) => {
                return Err(vec![
                    type_error!(
                        self,
                        span,
                        ctx,
                        TypeError::Mismatch {
                            got: tb.clone(),
                            expected: ta.clone()
                        },
                        "{}",
                        a_err
                    ),
                    type_error!(
                        self,
                        span,
                        ctx,
                        TypeError::Mismatch {
                            got: ta.clone(),
                            expected: tb.clone()
                        },
                        "{}",
                        b_err
                    ),
                ])
            }
        }

        self.union(a, b);

        Ok(())
    }

    fn check_wider(
        &mut self,
        span: Span,
        ctx: TypeCtx,
        thin: usize,
        wide: usize,
    ) -> Result<(), Vec<Error>> {
        let t = self.find(thin);
        let w = self.find(wide);

        let tt = &self.types[t].ty;
        let tw = &self.types[w].ty;

        match tw.fits(tt) {
            Ok(_) => Ok(()),
            Err(err) => Err(vec![type_error!(
                self,
                span,
                ctx,
                TypeError::Mismatch {
                    got: tt.clone(),
                    expected: tw.clone()
                },
                "{}",
                err
            )])
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

/// Module with all the operators that can be applied
/// to values.
///
/// Broken out because they need to be recursive.
mod op {
    use super::Type;
    use std::collections::BTreeSet;

    fn tuple_bin_op(a: &Vec<Type>, b: &Vec<Type>, f: fn(&Type, &Type) -> Type) -> Type {
        Type::Tuple(a.iter().zip(b.iter()).map(|(a, b)| f(a, b)).collect())
    }

    fn tuple_un_op(a: &Vec<Type>, f: fn(&Type) -> Type) -> Type {
        Type::Tuple(a.iter().map(f).collect())
    }

    fn union_bin_op(a: &BTreeSet<Type>, b: &Type, f: fn(&Type, &Type) -> Type) -> Type {
        a.iter()
            .find_map(|x| {
                let x = f(x, b);
                if x.is_nil() {
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
            Type::Union(a) => {
                if a.iter().all(|ty| ty.is_number()) {
                    value.clone()
                } else {
                    Type::Invalid
                }
            }
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

    pub fn add(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Float, Type::Float) => Type::Float,
            (Type::Int, Type::Int) => Type::Int,
            (Type::String, Type::String) => Type::String,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, add),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => add(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
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
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => mul(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
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
            (Type::String, Type::String) => Type::Bool,
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
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, eq),
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
            (Type::String, Type::String) => Type::Bool,
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
