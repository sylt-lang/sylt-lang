#![allow(unused_imports, unused)]
use std::cell::RefCell;
use std::collections::{hash_map::Entry, HashMap};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use sylt_common::error::{Error, TypeError};
use sylt_common::prog::Prog;
use sylt_common::{Blob, Block, Op, RustFunction, Type, Value};
use sylt_parser::{
    Assignable, AssignableKind, Expression, ExpressionKind, Identifier, Module, Op as ParserOp,
    Span, Statement, StatementKind, Type as ParserType, TypeKind, VarKind, AST,
};

use crate::Compiler;

macro_rules! type_error_if_invalid {
    ($self:expr, $ty:expr, $span:expr, $kind:expr, $( $msg:expr ),+ ) => {
        if matches!($ty, Type::Invalid) {
            return type_error!($self, $span, $kind, $( $msg ),*);
        }
    };
    ($self:expr, $ty:expr, $span:expr, $kind:expr) => {
        if matches!($ty, Type::Invalid) {
            return type_error!($self, $span, $kind);
        }
    };
}

macro_rules! type_error {
    ($self:expr, $span:expr, $kind:expr, $( $msg:expr ),+ ) => {
        Err(vec![Error::TypeError {
            kind: $kind,
            file: $self.file(),
            span: $span,
            message: Some(format!($( $msg ),*)),
        }])
    };
    ($self:expr, $span:expr, $kind:expr) => {
        Err(vec![Error::TypeError {
            kind: $kind,
            file: $self.file(),
            span: $span,
            message: None,
        }])
    };
}

#[derive(Clone, Debug)]
struct Variable {
    ident: Identifier,
    ty: Type,
    kind: VarKind,
}

impl Variable {
    fn new(ident: Identifier, ty: Type, kind: VarKind) -> Self {
        Self { ident, ty, kind }
    }
}

struct TypeChecker<'c> {
    compiler: &'c mut Compiler,
    namespace: usize,
    namespaces: Vec<HashMap<String, Name>>,
    stack: Vec<Variable>,
}

#[derive(Debug, Clone)]
enum Name {
    Blob(usize),
    Global(Option<(Type, VarKind)>),
    Namespace(usize),
}

impl<'c> TypeChecker<'c> {
    fn new(compiler: &'c mut Compiler) -> Self {
        let mut namespaces = compiler
            .namespaces
            .iter()
            .map(|n| n
                .iter()
                .map(|(k, v)| (
                    k.clone(),
                    match v {
                        crate::Name::Global(_) => Name::Global(None),
                        crate::Name::Blob(b) => Name::Blob(*b),
                        crate::Name::Namespace(n) => Name::Namespace(*n),
                    }
                )).collect()
            ).collect();

        Self {
            compiler,
            namespace: 0,
            namespaces,
            stack: Vec::new(),
        }
    }


    fn file(&self) -> PathBuf {
        self.compiler.file_from_namespace(self.namespace).into()
    }

    fn compiler_context(&self) -> crate::Context {
        crate::Context::from_namespace(self.namespace)
    }

    fn get(&mut self, assignable: &Assignable) -> Result<Variable, Vec<Error>> {
        match &assignable.kind {
            AssignableKind::Read(ident) => {
                // TODO(ed): Fix this
                if let Some(var) = self.stack.iter().rev().find(|var| var.ident.name == ident.name) {
                    return Ok(var.clone());
                }
                dbg!(&self.namespaces[self.namespace]);
                match &self.namespaces[self.namespace][&ident.name] {
                    Name::Global(Some((ty, kind))) => { return Ok(Variable::new(ident.clone(), ty.clone(), *kind)); },
                    x => todo!("X: {:?} - {:?}", assignable.kind, x),
                }
                unreachable!();
            }
            AssignableKind::Call(_, _) => todo!(),
            AssignableKind::ArrowCall(_, _, _) => todo!(),
            AssignableKind::Access(_, _) => todo!(),
            AssignableKind::Index(_, _) => todo!(),
            AssignableKind::Expression(_) => todo!(),
        };
        todo!();
    }

    fn bin_op(
        &mut self,
        span: Span,
        lhs: &Expression,
        rhs: &Expression,
        op: fn(&Type, &Type) -> Type,
        name: &str,
    ) -> Result<Type, Vec<Error>> {
        let lhs = self.expression(lhs)?;
        let rhs = self.expression(rhs)?;
        let res = op(&lhs, &rhs);
        type_error_if_invalid!(
            self,
            res,
            span,
            TypeError::BinOp { lhs, rhs, op: name.into() }
        );
        Ok(res)
    }

    fn uni_op(
        &mut self,
        span: Span,
        val: &Expression,
        op: fn(&Type) -> Type,
        name: &str,
    ) -> Result<Type, Vec<Error>> {
        let val = self.expression(val)?;
        let res = op(&val);
        type_error_if_invalid!(
            self,
            res,
            span,
            TypeError::UniOp { val, op: name.into() }
        );
        Ok(res)
    }

    fn expression_union_or_errors<'a>(&mut self, expressions: impl Iterator<Item = &'a Expression>) -> Result<Type, Vec<Error>> {
        let ty: Vec<Type> = expressions.map(|e| self.expression(e)).collect::<Result<Vec<Type>, Vec<Error>>>()?;
        Ok(Type::maybe_union(ty.iter(), self.compiler.blobs.as_slice()))
    }

    fn expression(&mut self, expression: &Expression) -> Result<Type, Vec<Error>> {
        use ExpressionKind as EK;
        let span = expression.span;
        let res = match &expression.kind {
            EK::Add(a, b) => self.bin_op(span, a, b, op::add, "Addition")?,
            EK::Sub(a, b) => self.bin_op(span, a, b, op::sub, "Subtraction")?,
            EK::Mul(a, b) => self.bin_op(span, a, b, op::mul, "Multiplication")?,
            EK::Div(a, b) => self.bin_op(span, a, b, op::div, "Division")?,
            EK::AssertEq(a, b) | EK::Eq(a, b) | EK::Neq(a, b) => {
                self.bin_op(span, a, b, op::eq, "Equality")?
            }
            EK::Gt(a, b) | EK::Gteq(a, b) | EK::Lt(a, b) | EK::Lteq(a, b) => {
                self.bin_op(span, a, b, op::cmp, "Comparison")?
            }

            EK::Is(a, b) => self.bin_op(span, a, b, |a, b| Type::Ty, "Is")?,
            EK::In(a, b) => {
                let a = self.expression(a)?;
                let b = self.expression(b)?;
                // TODO(ed): Verify the order here
                let ret = match (&a, &b) {
                    (a, Type::List(b))
                    | (a, Type::Set(b))
                    | (a, Type::Dict(b, _)) => b.fits(a, self.compiler.blobs.as_slice()),
                    _ => Err("".into()),
                };
                if let Err(msg) = ret {
                    let err = Error::TypeError {
                        kind: TypeError::BinOp { lhs: a, rhs: b, op: "Containment".into() },
                        file: self.file(),
                        span,
                        message: if msg.is_empty() { None } else { Some(format!("because {}", msg)) },
                    };
                    return Err(vec![err]);
                }
                Type::Bool
            }

            EK::Neg(a) => self.uni_op(span, a, op::neg, "Negation")?,

            EK::And(a, b) => self.bin_op(span, a, b, op::and, "Boolean and")?,
            EK::Or(a, b) => self.bin_op(span, a, b, op::or, "Boolean or")?,
            EK::Not(a) => self.uni_op(span, a, op::not, "Boolean not")?,

            EK::IfExpression {
                condition,
                pass,
                fail,
            } => todo!(),
            EK::Duplicate(expr) => self.expression(expr)?,
            EK::Tuple(values) => {
                let mut types = Vec::new();
                for v in values.iter() {
                    types.push(self.expression(v)?);
                }
                Type::Tuple(types)
            }
            EK::Float(_) => Type::Float,
            EK::Int(_) => Type::Int,
            EK::Str(_) => Type::String,
            EK::Bool(_) => Type::Bool,
            EK::TypeConstant(_) => Type::Ty,
            EK::Nil => Type::Void,

            EK::Set(values) => {
                let ty = self.expression_union_or_errors(values.iter())?;
                Type::Set(Box::new(ty))
            }

            EK::List(values) => {
                let ty = self.expression_union_or_errors(values.iter())?;
                Type::List(Box::new(ty))
            }

            EK::Dict(values) => {
                let key = self.expression_union_or_errors(values.iter().skip(0).step_by(2))?;
                let val = self.expression_union_or_errors(values.iter().skip(1).step_by(2))?;
                Type::Dict(Box::new(key), Box::new(val))
            }

            EK::Function {
                name,
                params,
                ret,
                body,
            } => {
                let ret = self
                    .statement(body)?
                    .expect("A function that doesn't return a value");
                // TODO
                Type::Function(Vec::new(), Box::new(ret))
            }

            _ => todo!(),
        };
        Ok(res)
    }

    fn statement(&mut self, statement: &Statement) -> Result<Option<Type>, Vec<Error>> {
        let span = statement.span;
        let ret = match &statement.kind {
            StatementKind::Use { file, file_alias } => None,
            StatementKind::Blob { name, fields } => todo!(),
            StatementKind::Assignment {
                kind,
                target,
                value,
            } => {
                let value = self.expression(value)?;
                let variable = self.get(target)?;
                if variable.kind.immutable() {
                    // TODO(ed): I want this to point to the equal-sign, the parser is
                    // probably a bit off.
                    // TODO(ed): This should not be a type error - prefereably a compile error?
                    return type_error!(
                        self,
                        span,
                        TypeError::Mutability { ident: variable.ident.name }
                    );
                }
                let target_ty = variable.ty;
                let result = match kind {
                    ParserOp::Nop => value.clone(),
                    ParserOp::Add => op::add(&target_ty, &value),
                    ParserOp::Sub => op::sub(&target_ty, &value),
                    ParserOp::Mul => op::mul(&target_ty, &value),
                    ParserOp::Div => op::div(&target_ty, &value),
                };
                type_error_if_invalid!(
                    self,
                    result,
                    span,
                    TypeError::BinOp {
                        lhs: target_ty.clone(),
                        rhs: value.clone(),
                        op: match kind  {
                            ParserOp::Nop => unreachable!(),
                            ParserOp::Add => "Addition",
                            ParserOp::Sub => "Subtraction",
                            ParserOp::Mul => "Multiplication",
                            ParserOp::Div => "Division",
                        }.to_string()
                    }
                );
                // TODO(ed): Is the fits-order correct?
                if let Err(reason) = target_ty.fits(&result, self.compiler.blobs.as_slice()) {
                    // TODO(ed): I want this to point to the equal-sign, the parser is
                    // probably a bit off.
                    return type_error!(
                        self,
                        span,
                        TypeError::MismatchAssign { got: result, expected: target_ty },
                        "because {}",
                        reason
                    );
                }
                None
            }
            StatementKind::Definition {
                ident,
                kind,
                ty,
                value,
            } => {
                let ty = self.compiler.resolve_type(ty, self.compiler_context());
                let value = self.expression(value)?;
                let fit = ty.fits(&value, self.compiler.blobs.as_slice());
                let ty = match (kind.force(), fit) {
                    (true, Ok(_)) => {
                        return type_error!(
                            self,
                            span,
                            TypeError::ExessiveForce {
                                got: ty,
                                expected: value,
                            }
                        )
                    }
                    (true, Err(_)) => ty,
                    (false, Ok(_)) => value,
                    (false, Err(reason)) => {
                        return type_error!(
                            self,
                            span,
                            TypeError::Missmatch {
                                got: ty,
                                expected: value,
                            },
                            "because {}", reason
                        )
                    }
                };
                self.stack.push(Variable::new(ident.clone(), ty, *kind));
                None
            }
            StatementKind::If {
                condition,
                pass,
                fail,
            } => {
                let ty = self.expression(condition)?;
                if !matches!(ty, Type::Bool) {
                    return type_error!(
                        self,
                        condition.span,
                        TypeError::Missmatch {
                            got: ty,
                            expected: Type::Bool,
                        },
                        "Only boolean expressions are valid if-statement conditions"
                    )
                }
                self.statement(pass)?;
                self.statement(fail)?;
                None
            }
            StatementKind::Loop { condition, body } => {
                let ty = self.expression(condition)?;
                if !matches!(ty, Type::Bool) {
                    return type_error!(
                        self,
                        condition.span,
                        TypeError::Missmatch {
                            got: ty,
                            expected: Type::Bool,
                        },
                        "Only boolean expressions are valid if-statement conditions"
                    )
                }
                self.statement(body)?;
                None
            }
            StatementKind::IsCheck { lhs, rhs } => todo!(),
            StatementKind::Block { statements } => {
                let stack_size = self.stack.len();

                let mut errors = Vec::new();
                let mut rets = Vec::new();
                for stmt in statements {
                    match self.statement(stmt) {
                        Ok(Some(ty)) => {
                            rets.push(ty);
                        }
                        Ok(None) => {}
                        Err(mut errs) => {
                            errors.append(&mut errs);
                        }
                    }
                }

                self.stack.truncate(stack_size);

                if !errors.is_empty() {
                    return Err(errors);
                }
                Some(Type::maybe_union(
                    rets.iter(),
                    self.compiler.blobs.as_slice(),
                ))
            }

            StatementKind::Ret { value } => Some(self.expression(value)?),
            StatementKind::StatementExpression { value } => {
                self.expression(value)?;
                None
            }

            StatementKind::Continue
            | StatementKind::Break
            | StatementKind::Unreachable
            | StatementKind::EmptyStatement => None,
        };
        Ok(ret)
    }

    fn outer_definition(&mut self, namespace: &mut HashMap<String, Name>, stmt: &Statement) -> Result<(), Vec<Error>> {
        let span = stmt.span;
        match &stmt.kind {
            StatementKind::Definition { ident, kind, ty, value } => {
                let name = match &namespace[&ident.name] {
                    Name::Global(None) => {
                        let ty = self.compiler.resolve_type(ty, self.compiler_context());
                        let value = self.expression(value)?;
                        let fit = ty.fits(&value, self.compiler.blobs.as_slice());
                        let ty = match (kind.force(), fit) {
                            (true, Ok(_)) => {
                                return type_error!(
                                    self,
                                    span,
                                    TypeError::ExessiveForce {
                                        got: ty,
                                        expected: value,
                                    }
                                )
                            }
                            (true, Err(_)) => ty,
                            (false, Ok(_)) => value,
                            (false, Err(reason)) => {
                                return type_error!(
                                    self,
                                    span,
                                    TypeError::Missmatch {
                                        got: ty,
                                        expected: value,
                                    },
                                    "because {}", reason
                                )
                            }
                        };
                        (ty, *kind)
                    }
                    // TODO(ed): Throw earlier errors before typechecking -
                    // so we don't have to care about the duplicates.
                    x => unreachable!("X: {:?}", x),
                };
                namespace.insert(ident.name.clone(), Name::Global(Some(name)));
                dbg!(&namespace);
            }
            _ => {},
        }
        Ok(())

    }

    fn solve(
        mut self,
        tree: &mut AST,
        to_namespace: &HashMap<PathBuf, usize>,
    ) -> Result<(), Vec<Error>> {
        let mut errors = Vec::new();

        for (path, module) in &tree.modules {
            self.namespace = to_namespace[path];
            let mut namespace = self.namespaces[self.namespace].clone();
            for stmt in &module.statements {
                if let Err(mut errs) = self.outer_definition(&mut namespace, &stmt) {
                    errors.append(&mut errs);
                }
                // Make sure it's updated all the time! :D
                self.namespaces[self.namespace] = namespace.clone();
            }
        }
        dbg!(&self.namespaces);


        for (path, module) in &tree.modules {
            self.namespace = to_namespace[path];
            for stmt in &module.statements {
                if let Err(mut errs) = self.statement(&stmt) {
                    errors.append(&mut errs);
                }
            }
        }

        if !errors.is_empty() {
            Err(errors)
        } else {
            Ok(())
        }
    }
}

pub(crate) fn solve(
    compiler: &mut Compiler,
    tree: &mut AST,
    to_namespace: &HashMap<PathBuf, usize>,
) -> Result<(), Vec<Error>> {
    TypeChecker::new(compiler).solve(tree, to_namespace)
}

///
/// Module with all the operators that can be applied
/// to values.
///
/// Broken out because they need to be recursive.
mod op {
    use super::Type;
    use std::collections::HashSet;

    fn tuple_bin_op(a: &Vec<Type>, b: &Vec<Type>, f: fn(&Type, &Type) -> Type) -> Type {
        Type::Tuple(a.iter().zip(b.iter()).map(|(a, b)| f(a, b)).collect())
    }

    fn tuple_un_op(a: &Vec<Type>, f: fn(&Type) -> Type) -> Type {
        Type::Tuple(a.iter().map(f).collect())
    }

    fn union_un_op(a: &HashSet<Type>, f: fn(&Type) -> Type) -> Type {
        a.iter()
            .find_map(|x| {
                let x = f(x);
                if x.is_nil() {
                    None
                } else {
                    Some(x)
                }
            })
            .unwrap_or(Type::Invalid)
    }

    fn union_bin_op(a: &HashSet<Type>, b: &Type, f: fn(&Type, &Type) -> Type) -> Type {
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
            Type::Union(v) => union_un_op(&v, neg),
            Type::Unknown => Type::Unknown,
            _ => Type::Invalid,
        }
    }

    pub fn not(value: &Type) -> Type {
        match value {
            Type::Bool => Type::Bool,
            Type::Tuple(a) => tuple_un_op(a, not),
            Type::Union(v) => union_un_op(&v, not),
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
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, add),
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
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, mul),
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
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, div),
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
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, cmp),
            _ => Type::Invalid,
        }
    }

    pub fn and(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, and),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => and(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, and),
            _ => Type::Invalid,
        }
    }

    pub fn or(a: &Type, b: &Type) -> Type {
        match (a, b) {
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, or),
            (Type::Unknown, a) | (a, Type::Unknown) if !matches!(a, Type::Unknown) => or(a, a),
            (Type::Unknown, Type::Unknown) => Type::Unknown,
            (Type::Union(a), b) | (b, Type::Union(a)) => union_bin_op(&a, b, or),
            _ => Type::Invalid,
        }
    }
}
