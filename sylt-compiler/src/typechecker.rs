// TODO(ed, er): If you see these during code-review, remind us to remove it.
#![allow(unused_variables)]
#![allow(unused_imports)]
#![allow(unused_macros)]

use std::collections::HashMap;
use std::path::PathBuf;
use sylt_common::error::{Error, TypeError};
use sylt_common::{RustFunction, Type as RuntimeType};
use sylt_parser::statement::NameIdentifier;
use sylt_parser::{
    Assignable, AssignableKind, Expression, ExpressionKind, Identifier, Op as ParserOp, Span,
    Statement, StatementKind, Type as ParserType, TypeKind, VarKind,
};

use crate::{self as compiler, ty::Type, Context, Name as CompilerName};
use std::collections::{BTreeMap, BTreeSet};

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

#[derive(Clone, Debug, Hash, PartialOrd, Ord, PartialEq, Eq)]
enum Constraint {
    Add(usize),
    Indexes(usize),
    IndexedBy(usize),
    IndexingGives(usize),
    GivenByIndex(usize),
    Field(String, usize),
}

struct TypeChecker {
    globals: HashMap<(usize, String), Name>,
    stack: Vec<Variable>,
    types: Vec<TypeNode>,
    namespace_to_file: HashMap<usize, PathBuf>,
    // TODO(ed): This can probably be removed via some trickery
    file_to_namespace: HashMap<PathBuf, usize>,
    functions: HashMap<String, usize>,
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
    fn new(
        namespace_to_file: &HashMap<usize, PathBuf>,
        functions: &HashMap<String, (usize, RustFunction, ParserType)>,
    ) -> Self {
        let mut res = Self {
            globals: HashMap::new(),
            stack: Vec::new(),
            types: Vec::new(),
            namespace_to_file: namespace_to_file.clone(),
            file_to_namespace: namespace_to_file
                .iter()
                .map(|(a, b)| (b.clone(), a.clone()))
                .collect(),
            functions: HashMap::new(),
        };
        res.functions = functions
            .iter()
            .map(|(name, (_, _, ty))| {
                (
                    name.clone(),
                    res.resolve_type(ty, TypeCtx { namespace: 0 })
                        // NOTE(ed): This is a special error - that a user should never see.
                        .map_err(|err| panic!("Failed to parse type for {:?}\n{}", name, err[0]))
                        .unwrap(),
                )
            })
            .collect();
        res
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

    fn type_namespace(&self, assignable: &Assignable, ctx: TypeCtx) -> Result<TypeCtx, Vec<Error>> {
        match &assignable.kind {
            AssignableKind::Read(ident) => match self
                .globals
                .get(&(ctx.namespace, ident.name.clone()))
                .cloned()
                .unwrap()
            {
                Name::Namespace(namespace) => Ok(TypeCtx { namespace, ..ctx }),
                _ => todo!(),
            },

            AssignableKind::Access(ass, ident) => {
                let ctx = self.type_namespace(ass, ctx)?;
                match self
                    .globals
                    .get(&(ctx.namespace, ident.name.clone()))
                    .cloned()
                    .unwrap()
                {
                    Name::Namespace(namespace) => Ok(TypeCtx { namespace, ..ctx }),
                    _ => todo!(),
                }
            }

            AssignableKind::Call(..)
            | AssignableKind::ArrowCall(..)
            | AssignableKind::Index(..)
            | AssignableKind::Expression(..) => todo!(),
        }
    }

    fn type_assignable(
        &mut self,
        assignable: &Assignable,
        ctx: TypeCtx,
    ) -> Result<usize, Vec<Error>> {
        match &assignable.kind {
            AssignableKind::Read(ident) => match self
                .globals
                .get(&(ctx.namespace, ident.name.clone()))
                .cloned()
                .unwrap()
            {
                Name::Blob(blob_ty) => {
                    let ty = self.push_type(blob_ty.clone());
                    match blob_ty {
                        Type::Blob(_, fields) => {
                            for (name, field_type) in fields.iter() {
                                self.add_constraint(
                                    ty,
                                    Constraint::Field(name.clone(), *field_type)
                                );
                            }
                        },
                        _ => unreachable!(),
                    }
                    Ok(ty)
                },
                _ => todo!(),
            },

            AssignableKind::Access(ass, ident) => {
                let ctx = self.type_namespace(ass, ctx)?;
                match self
                    .globals
                    .get(&(ctx.namespace, ident.name.clone()))
                    .cloned()
                    .unwrap()
                {
                    Name::Blob(ty) => Ok(self.push_type(ty.clone())),
                    _ => todo!(),
                }
            }

            AssignableKind::Call(..)
            | AssignableKind::ArrowCall(..)
            | AssignableKind::Index(..)
            | AssignableKind::Expression(..) => todo!(),
        }
    }

    fn resolve_type(&mut self, ty: &ParserType, ctx: TypeCtx) -> Result<usize, Vec<Error>> {
        self.inner_resolve_type(ty, ctx, &mut HashMap::new())
    }

    fn inner_resolve_type(
        &mut self,
        ty: &ParserType,
        ctx: TypeCtx,
        seen: &mut HashMap<String, usize>,
    ) -> Result<usize, Vec<Error>> {
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

            Fn(params, ret) => {
                let params = params
                    .iter()
                    .map(|t| self.inner_resolve_type(t, ctx, seen))
                    .collect::<Result<Vec<usize>, _>>()?;
                let ret = self.inner_resolve_type(ret, ctx, seen)?;
                Type::Function(params, ret)
            }

            Tuple(fields) => Type::Tuple(
                fields
                    .iter()
                    .map(|t| self.inner_resolve_type(t, ctx, seen))
                    .collect::<Result<Vec<usize>, _>>()?,
            ),

            List(kind) => Type::List(self.inner_resolve_type(kind, ctx, seen)?),

            Set(kind) => Type::Set(self.inner_resolve_type(kind, ctx, seen)?),

            Dict(key, value) => Type::Dict(
                self.inner_resolve_type(key, ctx, seen)?,
                self.inner_resolve_type(value, ctx, seen)?,
            ),

            Grouping(ty) => {
                return self.inner_resolve_type(ty, ctx, seen);
            }

            Generic(name) => {
                return Ok(*seen
                    .entry(name.clone())
                    .or_insert_with(|| self.push_type(Type::Unknown)))
            }

            // TODO(ed): This is very wrong - but works for now.
            Union(_, _) => Type::Void,
        };
        Ok(self.push_type(ty))
    }

    fn statement(
        &mut self,
        statement: &Statement,
        ctx: TypeCtx,
    ) -> Result<Option<usize>, Vec<Error>> {
        let span = statement.span;
        match &statement.kind {
            StatementKind::Block { statements } => {
                // Left this for Gustav
                let ss = self.stack.len();
                let rets = self.push_type(Type::Unknown);
                for stmt in statements.iter() {
                    if let Some(ret) = self.statement(stmt, ctx)? {
                        self.unify(span, ctx, rets, ret)?;
                    }
                }
                self.stack.truncate(ss);
                Ok(Some(rets))
            }

            StatementKind::Ret { value } => Ok(Some(self.expression(value, ctx)?)),

            StatementKind::StatementExpression { value } => {
                self.expression(value, ctx)?;
                Ok(None)
            }

            StatementKind::If {
                condition,
                pass,
                fail,
            } => {
                let condition = self.expression(condition, ctx)?;
                let boolean = self.push_type(Type::Bool);
                self.unify(span, ctx, boolean, condition)?;

                let pass = self.statement(pass, ctx)?;
                let fail = self.statement(fail, ctx)?;
                match (pass, fail) {
                    (Some(pass), Some(fail)) => Ok(Some(self.unify(span, ctx, pass, fail)?)),
                    (Some(pass), _) => Ok(Some(pass)),
                    (_, Some(fail)) => Ok(Some(fail)),
                    _ => Ok(None),
                }
            }

            StatementKind::Assignment {
                kind,
                target,
                value,
            } => {
                let expression_ty = self.expression(value, ctx)?;
                let target_ty = self.assignable(target, ctx)?;
                match kind {
                    ParserOp::Nop => {}
                    ParserOp::Add => {
                        self.add_constraint(expression_ty, Constraint::Add(target_ty));
                        self.add_constraint(target_ty, Constraint::Add(expression_ty));
                    }
                    ParserOp::Sub => todo!(),
                    ParserOp::Mul => todo!(),
                    ParserOp::Div => todo!(),
                }
                self.unify(span, ctx, expression_ty, target_ty)?;
                Ok(None)
            }

            StatementKind::Definition {
                ident,
                kind,
                ty,
                value,
            } => {
                let expression_ty = self.expression(value, ctx)?;
                let defined_ty = self.resolve_type(&ty, ctx)?;
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
                self.stack.push(var);
                Ok(None)
            }

            StatementKind::Loop { condition, body } => {
                let condition = self.expression(condition, ctx)?;
                let boolean = self.push_type(Type::Bool);
                self.unify(span, ctx, boolean, condition)?;

                self.statement(body, ctx)
            }

            StatementKind::Break => Ok(None),
            StatementKind::Continue => Ok(None),

            StatementKind::Unreachable => Ok(None),
            StatementKind::EmptyStatement => Ok(None),

            StatementKind::Use { .. }
            | StatementKind::Blob { .. }
            | StatementKind::IsCheck { .. }
            | StatementKind::ExternalDefinition { .. } => {
                todo!("Illegal inner statement! Parser should have caught this.")
            }
        }
    }

    fn outer_statement(&mut self, statement: &Statement, ctx: TypeCtx) -> Result<(), Vec<Error>> {
        let span = statement.span;
        match &statement.kind {
            StatementKind::Use { name, file, .. } => {
                let ident = match name {
                    NameIdentifier::Implicit(ident) => ident,
                    NameIdentifier::Alias(ident) => ident,
                };
                let other = self.file_to_namespace[file];
                self.globals
                    .insert((ctx.namespace, ident.name.clone()), Name::Namespace(other));
            }

            StatementKind::Blob { name, fields } => {
                let mut resolved_fields = BTreeMap::new();
                for (k, t) in fields.iter() {
                    resolved_fields.insert(k.clone(), self.resolve_type(t, ctx)?);
                }
                let ty = Type::Blob(name.clone(), resolved_fields);
                self.globals
                    .insert((ctx.namespace, name.clone()), Name::Blob(ty));
            }

            StatementKind::Definition {
                ident,
                kind,
                ty,
                value,
            } => {
                let expression_ty = self.expression(value, ctx)?;
                let defined_ty = self.resolve_type(&ty, ctx)?;
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

            StatementKind::ExternalDefinition { ident, kind, ty } => {
                let ty = self.resolve_type(ty, ctx)?;
                let var = Variable {
                    ident: ident.clone(),
                    ty,
                    kind: *kind,
                };
                self.globals
                    .insert((ctx.namespace, ident.name.clone()), Name::Global(var));
            }

            StatementKind::IsCheck { lhs, rhs } => {
                let lhs = self.resolve_type(lhs, ctx)?;
                let rhs = self.resolve_type(rhs, ctx)?;
                self.unify(span, ctx, lhs, rhs)?;
            }

            StatementKind::Assignment { .. }
            | StatementKind::Loop { .. }
            | StatementKind::Break
            | StatementKind::Continue
            | StatementKind::Ret { .. }
            | StatementKind::If { .. }
            | StatementKind::Block { .. }
            | StatementKind::StatementExpression { .. }
            | StatementKind::Unreachable
            | StatementKind::EmptyStatement => {
                panic!("Illegal outer statement! Parser should have caught this")
            }
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
                        None => match self.functions.get(&ident.name) {
                            Some(f) => Ok(*f),
                            None => panic!("Cannot read variable: {:?}", ident.name),
                        },
                        _ => panic!("Not a variable!"),
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

            AssignableKind::ArrowCall(pre_arg, f, args) => {
                let mut args = args.clone();
                args.insert(0, Expression::clone(pre_arg));
                let mapped_assignable = Assignable {
                    span,
                    kind: AssignableKind::Call(f.clone(), args),
                };
                self.assignable(&mapped_assignable, ctx)
            }

            AssignableKind::Access(ass, ident) => todo!(),

            AssignableKind::Index(outer, syn_index) => {
                let outer = self.assignable(outer, ctx)?;
                let index = self.expression(syn_index, ctx)?;
                self.add_constraint(index, Constraint::Indexes(outer));
                self.add_constraint(outer, Constraint::IndexedBy(index));
                self.check_constraints(span, ctx, outer)?;
                self.check_constraints(span, ctx, index)?;
                let outer_ty = self.find_type(outer);
                match outer_ty {
                    Type::Unknown => {
                        let ret = self.push_type(Type::Unknown);
                        // We don't add these if we don't have too.
                        self.add_constraint(outer, Constraint::IndexingGives(ret));
                        self.add_constraint(ret, Constraint::GivenByIndex(outer));
                        Ok(ret)
                    }

                    Type::Function(_, _)
                    | Type::Blob(_, _)
                    | Type::Invalid
                    | Type::Ty
                    | Type::Void
                    | Type::Int
                    | Type::Float
                    | Type::Bool
                    | Type::Str => {
                        return err_type_error!(
                            self,
                            span,
                            ctx,
                            TypeError::Exotic,
                            "{:?} cannot be index - at all",
                            outer
                        )
                    }

                    Type::Tuple(tys) => {
                        let int = self.push_type(Type::Int);
                        self.unify(span, ctx, index, int)?;
                        match syn_index.kind {
                            ExpressionKind::Int(index) => match tys.get(index as usize) {
                                Some(ty) => Ok(*ty),
                                None => {
                                    return err_type_error!(
                                        self,
                                        span,
                                        ctx,
                                        TypeError::Exotic,
                                        "Tuple index out of range, index {} but last index is {}",
                                        index,
                                        tys.len() - 1
                                    )
                                }
                            },
                            _ => {
                                return err_type_error!(
                                    self,
                                    span,
                                    ctx,
                                    TypeError::Exotic,
                                    "Tuples can only be index by integer constants"
                                )
                            }
                        }
                    }

                    Type::List(ty) => {
                        let int = self.push_type(Type::Int);
                        self.unify(span, ctx, index, int)?;
                        Ok(ty)
                    }
                    Type::Set(ty) => todo!("TODO(ed): Can a set be index?"),
                    Type::Dict(key, value) => {
                        self.unify(span, ctx, key, index)?;
                        Ok(value)
                    }
                }
            }

            AssignableKind::Expression(expression) => self.expression(expression, ctx),
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
                let mut seen = HashMap::new();
                for (ident, ty) in params.iter() {
                    let ty = self.inner_resolve_type(ty, ctx, &mut seen)?;
                    args.push(ty);

                    let var = Variable {
                        ident: ident.clone(),
                        ty,
                        kind: VarKind::Const,
                    };
                    self.stack.push(var);
                }

                let ret = self.inner_resolve_type(ret, ctx, &mut seen)?;
                if let Some(actual_ret) = self.statement(body, ctx)? {
                    self.unify(span, ctx, ret, actual_ret)?;
                } else {
                    panic!();
                }

                Ok(self.push_type(Type::Function(args, ret)))
            }

            ExpressionKind::Blob { blob, fields } => {
                // TODO: check the fields
                Ok(self.type_assignable(blob, ctx)?)
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
            Type::Void => RuntimeType::Void,
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
                Constraint::Add(b) => self.add(span, ctx, a, *b),

                Constraint::IndexedBy(b) => self.is_indexed_by(span, ctx, a, *b),
                Constraint::Indexes(b) => self.is_indexed_by(span, ctx, *b, a),

                Constraint::IndexingGives(b) => self.is_given_by_indexing(span, ctx, a, *b),
                Constraint::GivenByIndex(b) => self.is_given_by_indexing(span, ctx, *b, a),

                Constraint::Field(name, expected_ty) => match self.find_type(a).clone() {
                    Type::Unknown => Ok(()),
                    Type::Blob(blob_name, fields) => {
                        match fields.get(name) {
                            Some(actual_ty) => {
                                self.unify(span, ctx, *expected_ty, *actual_ty).map(|_| ())
                            },
                            None => err_type_error!(
                                self,
                                span,
                                ctx,
                                TypeError::MissingField {
                                    blob: blob_name.clone(),
                                    field: name.clone(),
                                }
                            ),
                        }
                    },
                    _ => err_type_error!(
                        self,
                        span,
                        ctx,
                        TypeError::Exotic,
                        "Only blobs can have fields, {} is not a blob, so it cannot have a fild {}",
                        self.bake_type(a),
                        name
                    ),
                }
            }?
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

        if a == b {
            return Ok(a);
        }

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

                (Type::Blob(a_blob, a_fields), Type::Blob(b_blob, b_fields)) => {
                    let mut c_fields = BTreeMap::new();
                    for (a_name, a_ty) in a_fields.iter() {
                        let b_ty = match b_fields.get(a_name) {
                            Some(b_ty) => *b_ty,
                            None => continue,
                        };
                        match self.unify(span, ctx, *a_ty, b_ty) {
                            Ok(_) => {
                                c_fields.insert(a_name.clone(), *a_ty);
                            }
                            Err(_) => {}
                        }
                    }

                    let c = self.push_type(Type::Unknown);
                    self.union(a, c);
                    self.union(b, c);
                    let c = self.find(c);
                    self.types[c].ty = Type::Blob(format!("{} & {}", a_blob, b_blob), c_fields);
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

    #[allow(unused)]
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

    fn is_indexed_by(
        &mut self,
        span: Span,
        ctx: TypeCtx,
        a: usize,
        b: usize,
    ) -> Result<(), Vec<Error>> {
        match (self.find_type(a), self.find_type(b)) {
            (Type::Unknown, _) => Ok(()),
            (_, Type::Unknown) => Ok(()),

            (Type::List(_), Type::Int) => Ok(()),
            (Type::Tuple(_), Type::Int) => Ok(()),
            // TODO(ed): Sets!
            (Type::Dict(k, _), _) => {
                self.unify(span, ctx, k, b)?;
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
                        op: "Indexing".to_string(),
                    }
                )
            }
        }
    }

    fn is_given_by_indexing(
        &mut self,
        span: Span,
        ctx: TypeCtx,
        a: usize,
        b: usize,
    ) -> Result<(), Vec<Error>> {
        match self.find_type(a) {
            Type::Unknown => Ok(()),

            Type::Tuple(_) => {
                // NOTE(ed): If we get here - it means we're checking the constraint, but the
                // constraint shouldn't be added because we only ever check constants.
                return err_type_error!(
                    self,
                    span,
                    ctx,
                    TypeError::Exotic,
                    "Tuples can only be indexed by integer constants"
                );
            }
            Type::List(given) => {
                self.unify(span, ctx, given, b)?;
                Ok(())
            }
            // TODO(ed): Sets!
            Type::Dict(_, given) => {
                self.unify(span, ctx, given, b)?;
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
                        op: "Indexing".to_string(),
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

        let ctx = TypeCtx { namespace: 0 };
        match self.globals.get(&(0, "start".to_string())).cloned() {
            Some(Name::Global(var)) => {
                let void = self.push_type(Type::Void);
                let start = self.push_type(Type::Function(Vec::new(), void));
                match self.unify(var.ident.span, ctx, var.ty, start) {
                    Ok(_) => {}
                    Err(_) => {
                        return err_type_error!(
                            self,
                            var.ident.span,
                            ctx,
                            TypeError::Mismatch {
                                got: self.bake_type(var.ty),
                                expected: self.bake_type(start),
                            },
                            "The start function has to have a given type"
                        )
                    }
                }
            }
            Some(_) => {
                return err_type_error!(
                    self,
                    Span::zero(),
                    ctx,
                    TypeError::Exotic,
                    "Expected a start function in the main module - but it was something else"
                )
            }
            None => {
                return err_type_error!(
                    self,
                    Span::zero(),
                    ctx,
                    TypeError::Exotic,
                    "Expected a start function in the main module - but couldn't find it"
                )
            }
        }

        Ok(())
    }
}

pub(crate) fn solve(
    statements: &Vec<(&Statement, usize)>,
    namespace_to_file: &HashMap<usize, PathBuf>,
    functions: &HashMap<String, (usize, RustFunction, ParserType)>,
) -> Result<(), Vec<Error>> {
    TypeChecker::new(namespace_to_file, functions).solve(statements)
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
