use std::collections::{hash_map::Entry, HashMap};
use std::path::PathBuf;
use sylt_common::error::{Error, TypeError};
use sylt_common::Type;
use sylt_parser::expression::ComparisonKind;
use sylt_parser::{
    Assignable, AssignableKind, Expression, ExpressionKind, Identifier, Op as ParserOp,
    Span, Statement, StatementKind, VarKind,
};

use crate::{self as compiler, first_ok_or_errs};
use compiler::Compiler;

macro_rules! type_error_if_invalid {
    ($self:expr, $ty:expr, $span:expr, $kind:expr, $( $msg:expr ),+ ) => {
        if matches!($ty, Type::Invalid) {
            return err_type_error!($self, $span, $kind, $( $msg ),*);
        }
    };
    ($self:expr, $ty:expr, $span:expr, $kind:expr) => {
        if matches!($ty, Type::Invalid) {
            return err_type_error!($self, $span, $kind);
        }
    };
}

macro_rules! err_type_error {
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

macro_rules! type_error {
    ($self:expr, $span:expr, $kind:expr, $( $msg:expr ),+ ) => {
        Error::TypeError {
            kind: $kind,
            file: $self.file(),
            span: $span,
            message: Some(format!($( $msg ),*)),
        }
    };
    ($self:expr, $span:expr, $kind:expr) => {
        Error::TypeError {
            kind: $kind,
            file: $self.file(),
            span: $span,
            message: None,
        }
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

#[derive(Debug, Clone)]
enum Lookup {
    Value(Type, VarKind),
    Namespace(usize),
}

impl<'c> TypeChecker<'c> {
    fn new(compiler: &'c mut Compiler) -> Self {
        let namespaces = compiler
            .namespaces
            .iter()
            .map(|n| n
                .iter()
                .map(|(k, v)| (
                    k.clone(),
                    match v {
                        compiler::Name::Global(_) => Name::Global(None),
                        compiler::Name::Blob(b) => Name::Blob(*b),
                        compiler::Name::Namespace(n) => Name::Namespace(*n),
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

    fn compiler_context(&self) -> compiler::Context {
        compiler::Context::from_namespace(self.namespace)
    }

    fn solve_generics_recursively(&self, span: Span, generics: &mut HashMap<String, Type>, par: &Type, arg: &Type) -> Result<Type, Vec<Error>> {
        Ok(match (par, arg) {
            (_, Type::Generic(_)) => {
                return err_type_error!(
                    self,
                    span,
                    TypeError::Violating(arg.clone()),
                    "Generics are not supported as arguments - only parameters"
                );
            }
            (Type::Generic(name), _) => {
                match generics.entry(name.clone()) {
                    Entry::Occupied(known) => {
                        let known = known.get();
                        if let Err(reason) = known.fits(&arg) {
                            // TODO(ed): Point to the argument maybe?
                            return err_type_error!(
                                self,
                                span,
                                TypeError::Mismatch { got: arg.clone(), expected: known.clone() },
                                "because {}. The type was inferred from previous arguments.",
                                reason
                            )
                        }
                        known.clone()
                    }
                    Entry::Vacant(unknown) => {
                        unknown.insert(arg.clone()).clone()
                    }
                }
            }
            (x, y) if x.fits(&y).is_ok() => x.clone(),

            (Type::Tuple(a), Type::Tuple(b)) => Type::Tuple(a.iter().zip(b.iter()).map(|(a, b)| self.solve_generics_recursively(span, generics, a, b)).collect::<Result<Vec<_>, _>>()?),
            (Type::List(a), Type::List(b)) => Type::List(Box::new(self.solve_generics_recursively(span, generics, a, b)?)),
            (Type::Set(a), Type::Set(b)) => Type::Set(Box::new(self.solve_generics_recursively(span, generics, a, b)?)),
            (Type::Dict(ak, av), Type::Dict(bk, bv)) => Type::Dict(
                Box::new(self.solve_generics_recursively(span, generics, ak, bk)?),
                Box::new(self.solve_generics_recursively(span, generics, av, bv)?),
            ),
            (Type::Function(a_args, a_ret), Type::Function(b_args, b_ret)) => {
                let args = a_args.iter().zip(b_args.iter()).map(|(a, b)| self.solve_generics_recursively(span, generics, a, b)).collect::<Result<Vec<_>, _>>()?;
                let ret = Box::new(self.solve_generics_recursively(span, generics, a_ret, b_ret)?);
                Type::Function(args, ret)
            }
            (a, Type::Union(b)) => {
                // This is technically wrong, it fails when guesses don't hold, like
                // `fn #X | #Y, #Y, #X -> void`, if we give in `int, int, float`.
                // We would assume:
                //   #X = int,
                //   #Y = int,
                // and fail on the third argument. Even though:
                //   #X = float,
                //   #Y = int,
                // would work.
                //
                // This complexity requires a lot more code and was therefore skipped.
                for t in b {
                    let mut new_generics = generics.clone();
                    self.solve_generics_recursively(span, &mut new_generics, a, t)?;
                    *generics = new_generics;
                }
                a.clone()
            }
            (Type::Union(a), b) => {
                first_ok_or_errs(a.iter()
                    .map(|ty| {
                        let mut new_generics = generics.clone();
                        let ret = self.solve_generics_recursively(span, &mut new_generics, ty, b);
                        if ret.is_ok() {
                            *generics = new_generics;
                        }
                        ret
                    })
                )
                .map_err(|errs| errs.into_iter().flatten().collect::<Vec<_>>())?
            }
            _ => {
                // TODO(ed): Point to the argument maybe?
                return err_type_error!(
                    self,
                    span,
                    TypeError::Mismatch { got: arg.clone(), expected: par.clone() }
                );
            }
        })
    }

    fn resolve_functions_from_args(&self, span: Span, args: Vec<Type>, ty: Type) -> Result<(Vec<Type>, Type), Vec<Error>> {
        let (params, ret) = match ty {
            Type::Function(params, ret) => (params, ret),
            Type::Unknown => {
                return Ok((args.clone(), Type::Unknown));
            },
            ty => {
                return err_type_error!(
                    self,
                    span,
                    TypeError::Violating(ty.clone()),
                    "{:?} cannot be called as a function",
                    ty
                );
            }
        };

        if args.len() != params.len() {
            return err_type_error!(
                self,
                span,
                TypeError::WrongArity { got: args.len(), expected: params.len() }
            )
        }

        let mut generics: HashMap<_, Type> = HashMap::new();
        for (par, arg) in params.iter().zip(args.iter()) {
            if matches!(arg, Type::Generic(_)) {
                return err_type_error!(
                    self,
                    span,
                    TypeError::Violating(arg.clone()),
                    "Generics are not supported as arguments - only parameters"
                );
            }
            self.solve_generics_recursively(span, &mut generics, par, arg)?;
        }
        let ret = if let Type::Generic(ret) = *ret {
            match generics.get(&ret) {
                Some(ty) => ty.clone(),
                None => {
                    return err_type_error!(
                        self,
                        span,
                        TypeError::Mutability, // TODO(ed): Wrong error
                        "Generics are only allowed if they can be deduced from the function signature, but '#{}' is not mentioned in the parameters",
                        ret
                    )
                }
            }
        } else {
            Type::clone(&ret)
        };
        Ok((args, ret))
    }

    fn assignable(&mut self, assignable: &Assignable, namespace: usize) -> Result<Lookup, Vec<Error>> {
        use AssignableKind as AK;
        use Lookup::*;
        let span = assignable.span;
        match &assignable.kind {
            AK::Read(ident) => {
                if let Some(var) = self.stack.iter().rfind(|var| var.ident.name == ident.name) {
                    return Ok(Value(var.ty.clone(), var.kind));
                }
                match &self.namespaces[namespace].get(&ident.name) {
                    Some(Name::Global(Some((ty, kind)))) => {
                        return Ok(Value(ty.clone(), *kind));
                    }
                    Some(Name::Global(None)) => {
                        // TODO(ed): This error should be caught earlier in the compiler - no point
                        // doing it twice.
                        return err_type_error!(
                            self,
                            span,
                            TypeError::UnresolvedName(ident.name.clone()),
                            "Read before being defined"
                        );
                    }
                    Some(Name::Blob(blob)) => {
                        if let crate::Value::Ty(b) = &self.compiler.constants[*blob] {
                            return Ok(Value(b.clone(), VarKind::Const));
                        }
                    }
                    Some(Name::Namespace(id)) => {
                        return Ok(Namespace(*id))
                    }
                    None => {}
                }
                if let Some((_, _, ty)) = self.compiler.functions.get(&ident.name) {
                    return Ok(Value(ty.clone(), VarKind::Const));
                } else {
                    return err_type_error!(
                        self,
                        span,
                        TypeError::UnresolvedName(ident.name.clone())
                    );
                }
            }
            AK::Call(fun, args) => {
                // TODO(ed): External functions need a different lookup.
                let ty = match self.assignable(fun, namespace)? {
                    Value(ty, _) => ty,
                    Namespace(_) => {
                        return err_type_error!(
                            self,
                            span,
                            TypeError::NamespaceNotExpression,
                            "Namespace cannot be called like a function"
                        );
                    }
                };
                let args = args.iter().map(|e| self.expression(e)).collect::<Result<Vec<_>, Vec<_>>>()?;
                let (_params, ret) = self.resolve_functions_from_args(span, args, ty.clone())?;
                return Ok(Value(Type::clone(&ret), VarKind::Const));
            }
            AK::ArrowCall(extra, fun, args) => {
                // DRY
                let mut args = args.clone();
                args.insert(0, Expression::clone(extra));
                return self.assignable(&Assignable {
                    span,
                    kind: AK::Call(Box::clone(fun), args),
                }, namespace);
            }
            AK::Access(thing, field) => {
                match self.assignable(thing, namespace)? {
                    Value(ty, _kind) => {
                        match &ty {
                            Type::Unknown => { Ok(Value(Type::Unknown, VarKind::Mutable)) }
                            Type::Blob(name, fields) => {
                                match fields.get(&field.name) {
                                    Some(ty) => Ok(Value(ty.clone(), VarKind::Mutable)),
                                    None => match field.name.as_str() {
                                        // TODO(ed): These result in poor error messages
                                        "_id" => Ok(Value(Type::Int, VarKind::Const)),
                                        "_name" => Ok(Value(Type::String, VarKind::Const)),
                                        _ => err_type_error!(
                                            self,
                                            field.span,
                                            TypeError::UnknownField { blob: name.clone(), field: field.name.clone() }
                                        ),
                                    }
                                }
                            }
                            ty => err_type_error!(
                                self,
                                span,
                                TypeError::Violating(ty.clone()),
                                "Only namespaces and blobs support '.'-access"
                            ),
                        }
                    }
                    Namespace(namespace) => {
                        return self.assignable(&Assignable {
                            span: field.span,
                            kind: AK::Read(field.clone()),
                        }, namespace);
                    }
                }
            }
            AK::Index(thing, index_expr) => {
                // TODO(ed): We could disallow mutating via reference here - not sure we want to thought.
                let thing = if let Value(val, _) = self.assignable(thing, namespace)? {
                    val
                } else {
                    return err_type_error!(
                        self,
                        span,
                        TypeError::NamespaceNotExpression
                    );
                };
                let index = self.expression(index_expr)?;
                let ret = match (thing, index) {
                    (Type::List(ret), index) => {
                        if let Err(reason) = index.fits(&Type::Int) {
                            return err_type_error!(
                                self,
                                span,
                                TypeError::Mismatch {
                                    got: index,
                                    expected: Type::Int,
                                },
                                "List indexing requires '{:?}' and {}",
                                Type::Int,
                                reason
                            )
                        }
                        Value(Type::clone(&ret), VarKind::Mutable)
                    }
                    (Type::Tuple(kinds), index) => {
                        if let Err(reason) = index.fits(&Type::Int) {
                            return err_type_error!(
                                self,
                                span,
                                TypeError::Mismatch {
                                    got: index,
                                    expected: Type::Int,
                                },
                                "Tuple indexing requires '{:?}' and {}",
                                Type::Int,
                                reason
                            )
                        }
                        // TODO(ed): Clean this up a bit
                        let val = if let ExpressionKind::Int(index) = index_expr.kind {
                            if let Some(val) = kinds.get(index as usize) {
                                val.clone()
                            } else {
                                return err_type_error!(
                                    self,
                                    span,
                                    TypeError::TupleIndexOutOfRange {
                                        length: kinds.len(),
                                        got: index,
                                    }
                                );
                            }
                        } else {
                            Type::maybe_union(kinds.iter())
                        };
                        Value(val, VarKind::Const)
                    }
                    (Type::Dict(key, val), index) => {
                        if let Err(reason) = key.fits(&index) {
                            return err_type_error!(
                                self,
                                span,
                                TypeError::Mismatch {
                                    got: index,
                                    expected: Type::clone(&key),
                                },
                                "Dict key-type is '{:?}' and {}",
                                key,
                                reason
                            )
                        }
                        Value(Type::clone(&val), VarKind::Mutable)
                    }
                    (ty, _) => {
                        return err_type_error!(
                            self,
                            span,
                            TypeError::Violating(ty.clone()),
                            "'{:?}' cannot be indexed, only List, Tuple and Dict can be",
                            ty
                        );
                    }
                };
                return Ok(ret);
            }
            AK::Expression(expr) => {
                return Ok(Value(self.expression(&expr)?, VarKind::Const));
            }
        }
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
        Ok(Type::maybe_union(ty.iter()))
    }

    fn expression(&mut self, expression: &Expression) -> Result<Type, Vec<Error>> {
        use ExpressionKind as EK;
        let span = expression.span;
        let res = match &expression.kind {
            EK::Get(assignable) => match self.assignable(assignable, self.namespace)? {
                Lookup::Value(value, _) => {
                    value
                }
                Lookup::Namespace(_) => {
                    return err_type_error!(
                        self,
                        span,
                        TypeError::NamespaceNotExpression
                    );
                }
            },

            EK::Add(a, b) => self.bin_op(span, a, b, op::add, "Addition")?,
            EK::Sub(a, b) => self.bin_op(span, a, b, op::sub, "Subtraction")?,
            EK::Mul(a, b) => self.bin_op(span, a, b, op::mul, "Multiplication")?,
            EK::Div(a, b) => self.bin_op(span, a, b, op::div, "Division")?,
            EK::AssertEq(a, b) => self.bin_op(span, a, b, op::eq, "Equality")?,

            EK::Comparison(a, cmp, b) => match cmp {
                ComparisonKind::Equals | ComparisonKind::NotEquals => {
                    self.bin_op(span, a, b, op::eq, "Equality")?
                }
                ComparisonKind::Greater | ComparisonKind::GreaterEqual | ComparisonKind::Less | ComparisonKind::LessEqual => {
                    self.bin_op(span, a, b, op::cmp, "Comparison")?
                }
                ComparisonKind::Is => self.bin_op(span, a, b, |_ ,_| Type::Bool, "Is")?,
                ComparisonKind::In => {
                    let a = self.expression(a)?;
                    let b = self.expression(b)?;
                    // TODO(ed): Verify the order here
                    let ret = match (&a, &b) {
                        (a, Type::List(b))
                        | (a, Type::Set(b))
                        | (a, Type::Dict(b, _)) => b.fits(a),
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
            }

            EK::Neg(a) => self.uni_op(span, a, op::neg, "Negation")?,

            EK::And(a, b) => self.bin_op(span, a, b, op::and, "Boolean and")?,
            EK::Or(a, b) => self.bin_op(span, a, b, op::or, "Boolean or")?,
            EK::Not(a) => self.uni_op(span, a, op::not, "Boolean not")?,

            EK::Parenthesis(expr) => self.expression(expr)?,

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
                name: _,
                params,
                ret,
                body,
            } => {
                let stack_size = self.stack.len();
                let mut param_types = Vec::new();
                for (ident, ty) in params {
                    let ty = self.compiler.resolve_type(ty, self.compiler_context());
                    param_types.push(ty.clone());
                    self.stack.push(Variable::new(ident.clone(), ty, VarKind::Const));
                }

                let ret = self.compiler.resolve_type(ret, self.compiler_context());
                let actual_ret = self
                    .statement(body)?
                    .expect("A function that doesn't return a value");

                // TODO(ed): We can catch types being too lenient here
                if let Err(reason) = ret.fits(&actual_ret) {
                    return err_type_error!(
                        self,
                        span,
                        TypeError::Mismatch { got: actual_ret, expected: ret },
                        "Return type doesn't match, {}",
                        reason
                    );
                }

                self.stack.truncate(stack_size);

                Type::Function(param_types, Box::new(ret))
            }

            EK::IfExpression {
                condition,
                pass,
                fail,
            } => {
                let condition_ty = self.expression(condition)?;
                if !matches!(condition_ty, Type::Bool) {
                    return err_type_error!(
                        self,
                        condition.span,
                        TypeError::Mismatch {
                            got: condition_ty,
                            expected: Type::Bool,
                        },
                        "Only boolean expressions are valid if-expression conditions"
                    )
                }

                // TODO(ed) check nullables and the actual condition
                Type::maybe_union(
                    [self.expression(pass)?, self.expression(fail)?].iter(),
                )
            }

            EK::IfShort { lhs, condition, fail } => {
                let condition_ty = self.expression(condition)?;
                if !matches!(condition_ty, Type::Bool) {
                    return err_type_error!(
                        self,
                        condition.span,
                        TypeError::Mismatch {
                            got: condition_ty,
                            expected: Type::Bool,
                        },
                        "Only boolean expressions are valid if-expression conditions"
                    )
                }

                // TODO(ed) check nullables and the actual condition
                Type::maybe_union(
                    [self.expression(lhs)?, self.expression(fail)?].iter(),
                )
            }

            EK::Blob { blob, fields } => {
                let (blob_name, blob_fields) = match self.assignable(blob, self.namespace)? {
                    Lookup::Value(ty, _) => {
                        match ty {
                            Type::Blob(name, fields) => (name, fields),
                            _ => return err_type_error!(
                                self,
                                span,
                                TypeError::Violating(ty),
                                "A blob was expected when instancing"
                            ),
                        }
                    }
                    Lookup::Namespace(_) => {
                        return err_type_error!(
                            self,
                            span,
                            TypeError::NamespaceNotExpression
                        );
                    }
                };
                let mut errors = Vec::new();
                let mut initalizer = HashMap::new();
                for (name, expr) in fields {
                    let ty = match self.expression(&expr) {
                        Ok(ty) => (ty, expr.span),
                        Err(mut errs) => {
                            errors.append(&mut errs);
                            continue;
                        }
                    };
                    initalizer.insert(name.clone(), ty);
                }
                for (name, (rhs, span)) in initalizer.iter() {
                    match blob_fields.get(name) {
                        Some(lhs) => match lhs.fits(rhs) {
                            Ok(_) => {}
                            Err(reason) => {
                                // TODO(ed): Not super sold on this error message - it can be better.
                                errors.push(type_error!(
                                    self,
                                    *span,
                                    TypeError::Mismatch { expected: lhs.clone(), got: rhs.clone() },
                                    "because {}.{} is a '{:?}' and {}",
                                    blob_name,
                                    name,
                                    lhs,
                                    reason
                                ));
                            }
                        }
                        None => {
                            errors.push(type_error!(
                                self,
                                *span,
                                TypeError::UnknownField { blob: blob_name.clone(), field: name.clone() },
                                "{}.{} does not exist on the original blob type",
                                blob_name,
                                name
                            ));
                        }
                    }
                }
                // No point checking that all fields are there if they're the wrong type,
                // we'll get duplicate errors.
                if !errors.is_empty() {
                    return Err(errors);
                }
                for (name, ty) in blob_fields.iter() {
                    if initalizer.contains_key(name) {
                        continue;
                    }
                    if let Err(_) = ty.fits(&Type::Void) {
                        // TODO(ed): Not super sold on this error message - it can be better.
                        errors.push(type_error!(
                            self,
                            span,
                            TypeError::Mismatch { got: Type::Void, expected: ty.clone() },
                            "Only nullable fields can be omitted, {}.{} is not nullable",
                            blob_name,
                            name
                        ));
                    }
                }
                if !errors.is_empty() {
                    return Err(errors);
                }
                Type::Blob(blob_name, blob_fields)
            }
        };
        Ok(res)
    }

    fn statement(&mut self, statement: &Statement) -> Result<Option<Type>, Vec<Error>> {
        use StatementKind as SK;
        let span = statement.span;
        let ret = match &statement.kind {
            SK::Assignment {
                kind,
                target,
                value,
            } => {
                let value = self.expression(value)?;
                let target_ty = match self.assignable(target, self.namespace)? {
                    Lookup::Value(_, kind) if kind.immutable() => {
                        // TODO(ed): I want this to point to the equal-sign, the parser is
                        // probably a bit off.
                        // TODO(ed): This should not be a type error - prefereably a compile error?
                        return err_type_error!(
                            self,
                            span,
                            TypeError::Mutability
                        );
                    }
                    Lookup::Namespace(_) => {
                        return err_type_error!(
                            self,
                            span,
                            TypeError::NamespaceNotExpression
                        );
                    }
                    Lookup::Value(ty, _) => {
                        ty
                    }
                };
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
                if let Err(reason) = target_ty.fits(&result) {
                    // TODO(ed): I want this to point to the equal-sign, the parser is
                    // probably a bit off.
                    return err_type_error!(
                        self,
                        span,
                        TypeError::MismatchAssign { got: result, expected: target_ty },
                        "because {}",
                        reason
                    );
                }
                None
            }
            SK::Definition {
                ident,
                kind,
                ty,
                value,
            } => {
                let slot = self.stack.len();
                let ty = self.compiler.resolve_type(ty, self.compiler_context());
                let ty = if matches!(ty, Type::Unknown) {
                    // Special case if it's a function
                    if let ExpressionKind::Function { params, ret, .. } = &value.kind {
                        let params = params.iter().map(|(_, ty)| self.compiler.resolve_type(ty, self.compiler_context())).collect();
                        let ret = self.compiler.resolve_type(ret, self.compiler_context());
                        Type::Function(params, Box::new(ret))
                    } else {
                        Type::Unknown
                    }
                } else {
                    ty
                };

                let value = self.expression(value);
                self.stack.push(Variable::new(ident.clone(), ty.clone(), *kind));
                let value = value?;

                let fit = ty.fits(&value);
                let ty = match (kind.force(), fit) {
                    (true, Ok(_)) => {
                        return err_type_error!(
                            self,
                            span,
                            TypeError::ExcessiveForce {
                                got: ty,
                                expected: value,
                            }
                        )
                    }
                    (true, Err(_)) => ty,
                    (false, Ok(_)) => if matches!(ty, Type::Unknown) { value } else { ty },
                    (false, Err(reason)) => {
                        return err_type_error!(
                            self,
                            span,
                            TypeError::Mismatch {
                                got: ty,
                                expected: value,
                            },
                            "because {}", reason
                        )
                    }
                };
                self.stack[slot].ty = ty;
                None
            }
            SK::If {
                condition,
                pass,
                fail,
            } => {
                let ty = self.expression(condition)?;
                if !matches!(ty, Type::Bool) {
                    return err_type_error!(
                        self,
                        condition.span,
                        TypeError::Mismatch {
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
            SK::Loop { condition, body } => {
                let ty = self.expression(condition)?;
                if !matches!(ty, Type::Bool) {
                    return err_type_error!(
                        self,
                        condition.span,
                        TypeError::Mismatch {
                            got: ty,
                            expected: Type::Bool,
                        },
                        "Only boolean expressions are valid if-statement conditions"
                    )
                }
                self.statement(body)?;
                None
            }
            SK::IsCheck { .. } => {
                // Checked in the compiler
                None
            }
            SK::Block { statements } => {
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
                Some(Type::maybe_union(rets.iter()))
            }

            SK::Ret { value } => Some(self.expression(value)?),
            SK::StatementExpression { value } => {
                self.expression(value)?;
                None
            }

            SK::Use { .. }
            | SK::Blob { .. }
            | SK::Continue
            | SK::Break
            | SK::Unreachable
            | SK::EmptyStatement => None,
        };
        Ok(ret)
    }

    fn outer_definition(&mut self, namespace: usize, stmt: &Statement) -> Result<(), Vec<Error>> {
        let span = stmt.span;
        match &stmt.kind {
            StatementKind::Definition { ident, kind, ty, value } => {
                let name = match &self.namespaces[namespace][&ident.name] {
                    Name::Global(None) => {
                        let ty = self.compiler.resolve_type(ty, self.compiler_context());
                        let ty = if matches!(ty, Type::Unknown) {
                            // Special case if it's a function
                            if let ExpressionKind::Function { params, ret, .. } = &value.kind {
                                let params = params.iter().map(|(_, ty)| self.compiler.resolve_type(ty, self.compiler_context())).collect();
                                let ret = self.compiler.resolve_type(ret, self.compiler_context());
                                Type::Function(params, Box::new(ret))
                            } else {
                                Type::Unknown
                            }
                        } else {
                            ty
                        };
                        let name = Name::Global(Some((ty.clone(), *kind)));
                        self.namespaces[namespace].insert(ident.name.clone(), name);
                        let value = self.expression(value)?;
                        let fit = ty.fits(&value);
                        let ty = match (kind.force(), fit) {
                            (true, Ok(_)) => {
                                return err_type_error!(
                                    self,
                                    span,
                                    TypeError::ExcessiveForce {
                                        got: ty,
                                        expected: value,
                                    }
                                )
                            }
                            (true, Err(_)) => ty,
                            (false, Ok(_)) => value,
                            (false, Err(reason)) => {
                                return err_type_error!(
                                    self,
                                    span,
                                    TypeError::Mismatch {
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
                self.namespaces[namespace].insert(ident.name.clone(), Name::Global(Some(name)));
            }
            _ => {},
        }
        Ok(())

    }

    fn solve(
        mut self,
        statements: &Vec<(&Statement, usize)>,
    ) -> Result<(), Vec<Error>> {

        for (statement, namespace) in statements.iter() {
            // Ignore errors since they'll be caught later and
            // there are false positives.
            self.stack.clear();
            let _ = self.outer_definition(*namespace, &statement);
        }

        let mut errors = Vec::new();
        for (statement, namespace) in statements.iter() {
            self.namespace = *namespace;
            self.stack.clear();
            if let Err(mut errs) = self.statement(&statement) {
                errors.append(&mut errs);
            }
        }
        let span = statements
            .iter()
            .find_map(|(stmt, _)| {
                if let StatementKind::Definition{ ident, .. } = &stmt.kind {
                    if ident.name == "start" {
                        return Some(ident.span);
                    }
                }
                None
            })
            .unwrap_or_else(|| Span { col_start: 0, col_end: 0, line: 0 });

        let call_start = &Assignable {
            span,
            kind: AssignableKind::Call(
                Box::new(Assignable {
                    span,
                    kind: AssignableKind::Read(Identifier {
                        span: Span::zero(),
                        name: "start".to_string()
                    }),
                }),
                Vec::new(),
            )
        };
        if let Err(mut errs) = self.assignable(call_start, 0) {
            for mut err in errs.iter_mut() {
                if let Error::TypeError { message, kind, .. } = &mut err {
                    let _ = message.insert("the program entry point".to_string());
                    match kind {
                        TypeError::WrongArity { got, expected } => {
                            std::mem::swap(got, expected);
                        }
                        _ => { }
                    }
                }
            }
            errors.append(&mut errs);
        }

        // Typecheck the implied syntax of calling start.
        if !errors.is_empty() {
            Err(errors)
        } else {
            Ok(())
        }
    }
}

pub(crate) fn solve(
    compiler: &mut Compiler,
    statements: &Vec<(&Statement, usize)>,
) -> Result<(), Vec<Error>> {
    TypeChecker::new(compiler).solve(statements)
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
