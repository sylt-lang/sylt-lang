use std::collections::HashMap;
use std::path::PathBuf;
use sylt_common::error::{Error, Helper, TypeError};
use sylt_common::{RustFunction, Type as RuntimeType};
use sylt_parser::statement::NameIdentifier;
use sylt_parser::{
    expression::ComparisonKind, Assignable, AssignableKind, Expression, ExpressionKind, Identifier,
    Op as ParserOp, Span, Statement, StatementKind, Type as ParserType, TypeAssignable,
    TypeAssignableKind, TypeConstraint, TypeKind, VarKind,
};

use crate::ty::Type;
use std::collections::{BTreeMap, BTreeSet};

type TypeResult<T> = Result<T, Vec<Error>>;

trait Help {
    fn help(self, typechecker: &TypeChecker, span: Span, message: String) -> Self;
}

impl<T> Help for TypeResult<T> {
    fn help(mut self, typechecker: &TypeChecker, span: Span, message: String) -> Self {
        match &mut self {
            Ok(_) => {}
            Err(errs) => match &mut errs.last_mut() {
                Some(Error::TypeError { helpers, .. }) => {
                    helpers.push(Helper { file: typechecker.span_file(&span), span, message });
                }
                _ => panic!("Cannot help on this error"),
            },
        }
        self
    }
}

macro_rules! err_type_error {
    ($self:expr, $span:expr, $kind:expr, $( $msg:expr ),+ ) => {
        Err(vec![type_error!($self, $span, $kind, $($msg),*)])
    };
    ($self:expr, $span:expr, $kind:expr) => {
        Err(vec![type_error!($self, $span, $kind)])
    };
}

macro_rules! type_error {
    ($self:expr, $span:expr, $kind:expr, $( $msg:expr ),+ ) => {
        Error::TypeError {
            kind: $kind,
            file: $self.span_file(&$span),
            span: $span,
            message: Some(format!($( $msg ),*)),
            helpers: Vec::new(),
        }
    };
    ($self:expr, $span:expr, $kind:expr) => {
        Error::TypeError {
            kind: $kind,
            file: $self.span_file(&$span),
            span: $span,
            message: None,
            helpers: Vec::new(),
        }
    };
}

macro_rules! bin_op {
    ($self:expr, $span:expr, $ctx:expr, $a:expr, $b:expr, $con:expr) => {{
        let a = $self.expression(&$a, $ctx)?;
        let b = $self.expression(&$b, $ctx)?;
        $self.add_constraint(a, $span, $con(b));
        $self.add_constraint(b, $span, $con(a));
        $self.check_constraints($span, $ctx, a)?;
        $self.check_constraints($span, $ctx, b)?;
        Ok(a) as TypeResult<usize>
    }};
}

#[derive(Clone, Debug)]
struct Variable {
    ident: Identifier,
    ty: usize,
    kind: VarKind,
    span: Span,
}

#[derive(Clone, Debug)]
struct TypeNode {
    ty: Type,
    parent: Option<usize>,
    size: usize,
    constraints: BTreeMap<Constraint, Span>,
}

/// # Constraints for type variables
///
/// Most constraints force `Unknown` types into becoming a certain type and causes a `TypeError`
/// otherwise. Constraints applied to two or more type variables need to make sure all variables
/// have the constraint in some way. For example, if some type has the `Contains` constraint, the
/// contained type must have the `IsContainedIn` constraint. If this is not the case, the
/// typechecker may miss some constraints when unifying.
///
/// In theory, `Unknown` is the only type that can have a constraint. In practice, concrete types
/// may have constraints since they need to be checked at least once.
#[derive(Clone, Debug, Hash, PartialOrd, Ord, PartialEq, Eq)]
enum Constraint {
    Add(usize),
    Sub(usize),
    Mul(usize),
    Div(usize),
    Equ(usize),
    Cmp(usize),
    CmpEqu(usize),

    Neg,

    Indexes(usize),
    IndexedBy(usize),
    IndexingGives(usize),
    GivenByIndex(usize),
    ConstantIndex(i64, usize),

    Field(String, usize),

    Num,
    Container,
    SameContainer(usize),
    Contains(usize),
    IsContainedIn(usize),
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
    Enum(Type),
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
                    res.resolve_type(Span::zero(0), TypeCtx { namespace: 0 }, ty)
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
            constraints: BTreeMap::new(),
        });
        ty_id
    }

    fn namespace_chain(&self, assignable: &Assignable, ctx: TypeCtx) -> Option<TypeCtx> {
        match &assignable.kind {
            AssignableKind::Read(ident) => {
                if let Some(_) = self.stack.iter().rfind(|v| v.ident.name == ident.name) {
                    None
                } else {
                    match self
                        .globals
                        .get(&(ctx.namespace, ident.name.clone()))
                        .cloned()
                    {
                        Some(Name::Namespace(namespace)) => Some(TypeCtx { namespace, ..ctx }),
                        _ => None,
                    }
                }
            }

            AssignableKind::Access(ass, ident) => {
                let ctx = self.namespace_chain(ass, ctx)?;
                match self
                    .globals
                    .get(&(ctx.namespace, ident.name.clone()))
                    .cloned()
                {
                    Some(Name::Namespace(namespace)) => Some(TypeCtx { namespace, ..ctx }),
                    _ => None,
                }
            }

            AssignableKind::Variant { .. }
            | AssignableKind::Call(..)
            | AssignableKind::ArrowCall(..)
            | AssignableKind::Index(..)
            | AssignableKind::Expression(..) => None,
        }
    }

    fn type_namespace_chain(
        &self,
        assignable: &TypeAssignable,
        ctx: TypeCtx,
    ) -> TypeResult<TypeCtx> {
        match &assignable.kind {
            TypeAssignableKind::Read(ident) => {
                if let Some(_) = self.stack.iter().rfind(|v| v.ident.name == ident.name) {
                    err_type_error! {
                        self,
                        ident.span,
                        TypeError::Exotic,
                        "'{}' is a local variable, not a namespace",
                        ident.name
                    }
                } else {
                    match self
                        .globals
                        .get(&(ctx.namespace, ident.name.clone()))
                        .cloned()
                    {
                        Some(Name::Namespace(namespace)) => Ok(TypeCtx { namespace, ..ctx }),
                        _ => err_type_error! {
                            self,
                            ident.span,
                            TypeError::UnresolvedName(ident.name.clone()),
                            "Did you forget an import?"
                        },
                    }
                }
            }

            TypeAssignableKind::Access(ass, ident) => {
                let ctx = self.type_namespace_chain(ass, ctx)?;
                match self
                    .globals
                    .get(&(ctx.namespace, ident.name.clone()))
                    .cloned()
                {
                    Some(Name::Namespace(namespace)) => Ok(TypeCtx { namespace, ..ctx }),
                    None => {
                        err_type_error!(
                            self,
                            ident.span,
                            TypeError::UnresolvedName(ident.name.clone()),
                            "Did you forget an import?"
                        )
                    }
                    _ => err_type_error! {
                        self,
                        ident.span,
                        TypeError::Exotic,
                        "'{}' should be a namespace or a blob but it's a global",
                        ident.name
                    },
                }
            }
        }
    }

    fn type_assignable(&mut self, ctx: TypeCtx, assignable: &TypeAssignable) -> TypeResult<usize> {
        match &assignable.kind {
            TypeAssignableKind::Read(ident) => match self
                .globals
                .get(&(ctx.namespace, ident.name.clone()))
                .cloned()
            {
                Some(Name::Blob(ty)) | Some(Name::Enum(ty)) => Ok(self.push_type(ty.clone())),
                None => {
                    err_type_error!(
                        self,
                        ident.span,
                        TypeError::UnresolvedName(ident.name.clone()),
                        "Expected a blob or an enum"
                    )
                }
                _ => {
                    err_type_error!(
                        self,
                        ident.span,
                        TypeError::Exotic,
                        "Expected a blob but got '{}'",
                        ident.name
                    )
                }
            },

            TypeAssignableKind::Access(ass, ident) => {
                let ctx = self.type_namespace_chain(ass, ctx)?;
                match self
                    .globals
                    .get(&(ctx.namespace, ident.name.clone()))
                    .cloned()
                {
                    Some(Name::Blob(ty)) | Some(Name::Enum(ty)) => Ok(self.push_type(ty.clone())),
                    None => {
                        err_type_error!(
                            self,
                            ident.span,
                            TypeError::UnresolvedName(ident.name.clone()),
                            "Expected a blob"
                        )
                    }
                    _ => {
                        err_type_error!(
                            self,
                            ident.span,
                            TypeError::Exotic,
                            "Expected a blob but got '{}'",
                            ident.name
                        )
                    }
                }
            }
        }
    }

    fn resolve_type(&mut self, span: Span, ctx: TypeCtx, ty: &ParserType) -> TypeResult<usize> {
        self.inner_resolve_type(span, ctx, ty, &mut HashMap::new())
    }

    fn resolve_constraint(
        &mut self,
        span: Span,
        var: usize,
        constraint: &TypeConstraint,
        seen: &HashMap<String, usize>,
    ) -> TypeResult<()> {
        fn check_constraint_arity(
            typechecker: &TypeChecker,
            span: Span,
            name: &str,
            got: usize,
            expected: usize,
        ) -> TypeResult<()> {
            if got != expected {
                err_type_error!(
                    typechecker,
                    span,
                    TypeError::WrongConstraintArity { name: name.into(), got, expected }
                )
            } else {
                Ok(())
            }
        }

        fn parse_constraint_arg(
            typechecker: &TypeChecker,
            span: Span,
            name: &str,
            seen: &HashMap<String, usize>,
        ) -> TypeResult<usize> {
            match seen.get(name) {
                Some(x) => Ok(*x),
                _ => {
                    err_type_error!(
                        typechecker,
                        span,
                        TypeError::UnknownConstraintArgument(name.into())
                    )
                }
            }
        }

        let num_args = constraint.args.len();
        match constraint.name.name.as_str() {
            "Num" => {
                check_constraint_arity(self, span, "Num", num_args, 0)?;
                self.add_constraint(var, span, Constraint::Num);
            }
            "Container" => {
                check_constraint_arity(self, span, "Container", num_args, 0)?;
                self.add_constraint(var, span, Constraint::Container);
            }
            "SameContainer" => {
                check_constraint_arity(self, span, "SameContainer", num_args, 1)?;
                let a = parse_constraint_arg(self, span, &constraint.args[0].name, seen)?;
                self.add_constraint(var, span, Constraint::SameContainer(a));
                self.add_constraint(a, span, Constraint::SameContainer(var));
            }
            "Contains" => {
                check_constraint_arity(self, span, "Contains", num_args, 1)?;
                let a = parse_constraint_arg(self, span, &constraint.args[0].name, seen)?;
                self.add_constraint(var, span, Constraint::Contains(a));
                self.add_constraint(a, span, Constraint::IsContainedIn(var));
            }
            x => return err_type_error!(self, span, TypeError::UnknownConstraint(x.into())),
        }
        Ok(())
    }

    fn inner_resolve_type(
        &mut self,
        span: Span,
        ctx: TypeCtx,
        ty: &ParserType,
        seen: &mut HashMap<String, usize>,
    ) -> TypeResult<usize> {
        use TypeKind::*;
        let ty = match &ty.kind {
            Implied => Type::Unknown,

            Resolved(ty) => match ty {
                RuntimeType::Void => Type::Void,
                RuntimeType::Unknown => Type::Unknown,
                RuntimeType::Int => Type::Int,
                RuntimeType::Float => Type::Float,
                RuntimeType::Bool => Type::Bool,
                RuntimeType::String => Type::Str,
                x => unreachable!("Got an unexpected resolved type '{:?}'", x),
            },

            UserDefined(assignable) => {
                return self.type_assignable(ctx, assignable);
            }

            Fn { constraints, params, ret } => {
                let params = params
                    .iter()
                    .map(|t| self.inner_resolve_type(span, ctx, t, seen))
                    .collect::<TypeResult<Vec<_>>>()?;
                let ret = self.inner_resolve_type(span, ctx, ret, seen)?;
                for (var, constraints) in constraints.iter() {
                    let var = match seen.get(var) {
                        Some(var) => *var,
                        // NOTE(ed): This disallowes type-variables that are only used for
                        // constraints.
                        None => {
                            return err_type_error!(
                                self,
                                span,
                                TypeError::UnresolvedName(var.clone()),
                                "Unused type-variable. (Only usages in the function signature are counted)"
                            )
                        }
                    };

                    for constraint in constraints.iter() {
                        self.resolve_constraint(span, var, constraint, seen)?;
                    }
                }
                Type::Function(params, ret)
            }

            Tuple(fields) => Type::Tuple(
                fields
                    .iter()
                    .map(|t| self.inner_resolve_type(span, ctx, t, seen))
                    .collect::<TypeResult<Vec<_>>>()?,
            ),

            List(kind) => Type::List(self.inner_resolve_type(span, ctx, kind, seen)?),

            Set(kind) => Type::Set(self.inner_resolve_type(span, ctx, kind, seen)?),

            Dict(key, value) => Type::Dict(
                self.inner_resolve_type(span, ctx, key, seen)?,
                self.inner_resolve_type(span, ctx, value, seen)?,
            ),

            Grouping(ty) => {
                return self.inner_resolve_type(span, ctx, ty, seen);
            }

            Generic(name) => {
                return Ok(*seen
                    .entry(name.clone())
                    .or_insert_with(|| self.push_type(Type::Unknown)))
            }
        };
        Ok(self.push_type(ty))
    }

    fn statement(&mut self, statement: &Statement, ctx: TypeCtx) -> TypeResult<Option<usize>> {
        let span = statement.span;
        match &statement.kind {
            StatementKind::Block { statements } => {
                // Left this for Gustav

                let ss = self.stack.len();
                let rets = self.push_type(Type::Unknown);
                let mut any_return = false;
                for stmt in statements.iter() {
                    if let Some(ret) = self.statement(stmt, ctx)? {
                        self.unify(span, ctx, rets, ret)?;
                        any_return = true;
                    }
                }
                self.stack.truncate(ss);
                if any_return {
                    Ok(Some(rets))
                } else {
                    Ok(None)
                }
            }

            StatementKind::Ret { value } => Ok(Some(self.expression(value, ctx)?)),

            StatementKind::StatementExpression { value } => {
                self.expression(value, ctx)?;
                Ok(None)
            }

            StatementKind::If { condition, pass, fail } => {
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

            StatementKind::Assignment { kind, target, value } => {
                self.can_assign(span, ctx, target)?;
                let expression_ty = self.expression(value, ctx)?;
                let target_ty = self.assignable(target, ctx)?;
                match kind {
                    ParserOp::Nop => {}
                    ParserOp::Add => {
                        self.add_constraint(expression_ty, span, Constraint::Add(target_ty));
                        self.add_constraint(target_ty, span, Constraint::Add(expression_ty));
                    }
                    ParserOp::Sub => {
                        self.add_constraint(expression_ty, span, Constraint::Sub(target_ty));
                        self.add_constraint(target_ty, span, Constraint::Sub(expression_ty));
                    }
                    ParserOp::Mul => {
                        self.add_constraint(expression_ty, span, Constraint::Mul(target_ty));
                        self.add_constraint(target_ty, span, Constraint::Mul(expression_ty));
                    }
                    ParserOp::Div => {
                        self.add_constraint(expression_ty, span, Constraint::Mul(target_ty));
                        self.add_constraint(target_ty, span, Constraint::Mul(expression_ty));
                    }
                };
                self.unify(span, ctx, expression_ty, target_ty)?;
                Ok(None)
            }

            StatementKind::Definition { .. } => {
                self.definition(statement, false, ctx)?;
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
            | StatementKind::Enum { .. }
            | StatementKind::IsCheck { .. }
            | StatementKind::ExternalDefinition { .. } => {
                unreachable!(
                    "Illegal inner statement at {:?}! Parser should have caught this.",
                    span
                )
            }
        }
    }

    fn outer_statement(&mut self, statement: &Statement, ctx: TypeCtx) -> TypeResult<()> {
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

            StatementKind::Enum { name, variants } => {
                let mut resolved_variants = BTreeMap::new();
                let mut seen = HashMap::new();
                for (k, t) in variants.iter() {
                    resolved_variants
                        .insert(k.clone(), self.inner_resolve_type(span, ctx, t, &mut seen)?);
                }
                let ty = Type::Enum(name.clone(), resolved_variants);
                self.globals
                    .insert((ctx.namespace, name.clone()), Name::Enum(ty));
            }

            StatementKind::Blob { name, fields } => {
                let mut resolved_fields = BTreeMap::new();
                let mut seen = HashMap::new();
                for (k, t) in fields.iter() {
                    resolved_fields
                        .insert(k.clone(), self.inner_resolve_type(span, ctx, t, &mut seen)?);
                }
                let ty = Type::Blob(name.clone(), resolved_fields);
                self.globals
                    .insert((ctx.namespace, name.clone()), Name::Blob(ty));
            }

            StatementKind::Definition { .. } => {
                self.definition(statement, true, ctx)?;
            }

            StatementKind::ExternalDefinition { ident, kind, ty } => {
                let ty = self.resolve_type(span, ctx, ty)?;
                let var = Variable { ident: ident.clone(), ty, kind: *kind, span };
                self.globals
                    .insert((ctx.namespace, ident.name.clone()), Name::Global(var));
            }

            StatementKind::IsCheck { lhs, rhs } => {
                let lhs = self.resolve_type(span, ctx, lhs)?;
                let rhs = self.resolve_type(span, ctx, rhs)?;
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
                unreachable!(
                    "Illegal outer statement between lines {} and {} in '{}'! Parser should have caught this",
                    span.line_start,
                    span.line_end,
                    self.span_file(&span).display()
                )
            }
        }
        Ok(())
    }

    fn assignable(&mut self, assignable: &Assignable, ctx: TypeCtx) -> TypeResult<usize> {
        let span = assignable.span;
        match &assignable.kind {
            AssignableKind::Variant { enum_ass, variant, value } => {
                let (ctx, enum_name) = match &enum_ass.kind {
                    AssignableKind::Read(enum_name) => (ctx, enum_name),
                    AssignableKind::Access(chain, enum_name) => match self.namespace_chain(chain, ctx) {
                        Some(ctx) => (ctx, enum_name),
                        None => return err_type_error!(
                            self,
                            span,
                            TypeError::Exotic,
                            "Not all accesses are namespace accesses\nsince enums cannot be stored anywhere"
                        ),
                    }

                    AssignableKind::Call(_, _)
                    | AssignableKind::Variant { .. }
                    | AssignableKind::ArrowCall(_, _, _)
                    | AssignableKind::Index(_, _)
                    | AssignableKind::Expression(_) => unreachable!(),
                };
                match self.stack.iter().rfind(|v| v.ident.name == enum_name.name) {
                    Some(var) => {
                        return err_type_error!(
                            self,
                            span,
                            TypeError::Exotic,
                            "Expected an enum - but the local variable '{}'",
                            var.ident.name
                        )
                        .help(
                            self,
                            var.span,
                            format!("'{}' was declared here", var.ident.name),
                        )?
                    }
                    None => {}
                };
                let ty = match self.globals.get(&(ctx.namespace, enum_name.name.clone())) {
                    Some(Name::Enum(ty)) => {
                        // NOTE(ed): This allows enumerations to be generic, which is always fun!
                        let ty = ty.clone();
                        let ty = self.push_type(ty);
                        self.copy(ty)
                    }
                    _ => {
                        return err_type_error!(
                            self,
                            span,
                            TypeError::UnresolvedName(enum_name.name.clone())
                        )
                    }
                };

                let (enum_name, variants) = match self.find_type(ty) {
                    Type::Enum(name, variants) => (name, variants),
                    Type::Unknown => todo!("Should this ever happen?"),
                    _ => {
                        return err_type_error!(
                            self,
                            variant.span,
                            TypeError::Violating(self.bake_type(ty)),
                            "Is not an enum-variant"
                        )
                    }
                };
                // Only unify this variant with the expression
                let expr_ty = self.expression(value, ctx)?;
                match variants.get(&variant.name) {
                    Some(field_ty) => self.unify(variant.span, ctx, *field_ty, expr_ty)?,
                    None => {
                        return err_type_error!(
                            self,
                            variant.span,
                            TypeError::UnknownVariant(enum_name, variant.name.clone())
                        )
                    }
                };
                Ok(ty)
            }

            // FIXME: Functions are copied since they may be specialized
            // several times, this does not work properly when functions are
            // passed to an unknown function parameter.
            AssignableKind::Read(ident) => {
                if let Some(var) = self
                    .stack
                    .iter()
                    .rfind(|v| v.ident.name == ident.name)
                    .cloned()
                {
                    match self.find_type(var.ty) {
                        Type::Function(..) => Ok(self.copy(var.ty)),
                        _ => Ok(var.ty),
                    }
                } else {
                    match self
                        .globals
                        .get(&(ctx.namespace, ident.name.clone()))
                        .cloned()
                    {
                        Some(Name::Global(var)) => match self.find_type(var.ty) {
                            Type::Function(..) => Ok(self.copy(var.ty)),
                            _ => Ok(var.ty),
                        },
                        None => match self.functions.get(&ident.name).cloned() {
                            Some(f) => Ok(self.copy(f)),
                            None => err_type_error!(
                                self,
                                span,
                                TypeError::UnresolvedName(ident.name.clone())
                            ),
                        },
                        _ => err_type_error!(
                            self,
                            span,
                            TypeError::UnresolvedName(ident.name.clone())
                        ),
                    }
                }
            }

            AssignableKind::Call(f, args) => {
                let f = self.assignable(f, ctx)?;
                match self.find_type(f) {
                    Type::Function(params, ret) => {
                        if args.len() != params.len() {
                            return err_type_error!(
                                self,
                                span,
                                TypeError::WrongArity { got: args.len(), expected: params.len() }
                            );
                        }
                        // TODO(ed): Annotate the errors?
                        for (a, p) in args.iter().zip(params.iter()) {
                            let a = self.expression(a, ctx)?;
                            self.unify(span, ctx, *p, a)?;
                        }

                        Ok(ret)
                    }
                    Type::Unknown => err_type_error!(
                        self,
                        span,
                        TypeError::Violating(self.bake_type(f)),
                        "Unknown types cannot be called"
                    ),
                    _ => err_type_error!(
                        self,
                        span,
                        TypeError::Violating(self.bake_type(f)),
                        "Not callable"
                    ),
                }
            }

            AssignableKind::ArrowCall(pre_arg, f, args) => {
                let mut args = args.clone();
                args.insert(0, Expression::clone(pre_arg));
                let mapped_assignable =
                    Assignable { span, kind: AssignableKind::Call(f.clone(), args) };
                self.assignable(&mapped_assignable, ctx)
            }

            AssignableKind::Access(outer, ident) => match self.namespace_chain(outer, ctx) {
                Some(ctx) => self.assignable(
                    &Assignable { span, kind: AssignableKind::Read(ident.clone()) },
                    ctx,
                ),
                None => {
                    let outer = self.assignable(outer, ctx)?;
                    let ret = self.push_type(Type::Unknown);
                    self.add_constraint(outer, span, Constraint::Field(ident.name.clone(), ret));
                    self.check_constraints(span, ctx, outer)?;
                    Ok(ret)
                }
            },

            AssignableKind::Index(outer, syn_index) => {
                let outer = self.assignable(outer, ctx)?;
                let index = self.expression(syn_index, ctx)?;
                let ret = self.push_type(Type::Unknown);
                match syn_index.kind {
                    ExpressionKind::Int(index) => {
                        self.add_constraint(outer, span, Constraint::ConstantIndex(index, ret));
                    }
                    _ => {
                        self.add_constraint(index, span, Constraint::Indexes(outer));
                        self.add_constraint(outer, span, Constraint::IndexedBy(index));
                        self.add_constraint(outer, span, Constraint::IndexingGives(ret));
                        self.add_constraint(ret, span, Constraint::GivenByIndex(outer));
                    }
                }

                self.check_constraints(span, ctx, outer)?;
                self.check_constraints(span, ctx, index)?;
                Ok(ret)
            }

            AssignableKind::Expression(expression) => self.expression(expression, ctx),
        }
    }

    fn expression(&mut self, expression: &Expression, ctx: TypeCtx) -> TypeResult<usize> {
        let span = expression.span;
        let res = match &expression.kind {
            ExpressionKind::Get(ass) => self.assignable(ass, ctx),

            ExpressionKind::Add(a, b) => bin_op!(self, span, ctx, a, b, Constraint::Add),
            ExpressionKind::Sub(a, b) => bin_op!(self, span, ctx, a, b, Constraint::Sub),
            ExpressionKind::Mul(a, b) => bin_op!(self, span, ctx, a, b, Constraint::Mul),
            ExpressionKind::Div(a, b) => bin_op!(self, span, ctx, a, b, Constraint::Div),

            ExpressionKind::Comparison(a, comp, b) => match comp {
                ComparisonKind::NotEquals | ComparisonKind::Equals => {
                    bin_op!(self, span, ctx, a, b, Constraint::Equ)?;
                    Ok(self.push_type(Type::Bool))
                }
                ComparisonKind::Less | ComparisonKind::Greater => {
                    bin_op!(self, span, ctx, a, b, Constraint::Cmp)?;
                    Ok(self.push_type(Type::Bool))
                }
                ComparisonKind::LessEqual | ComparisonKind::GreaterEqual => {
                    bin_op!(self, span, ctx, a, b, Constraint::CmpEqu)?;
                    Ok(self.push_type(Type::Bool))
                }

                ComparisonKind::In => {
                    let a = self.expression(&a, ctx)?;
                    let b = self.expression(&b, ctx)?;
                    self.add_constraint(a, span, Constraint::IsContainedIn(b));
                    self.add_constraint(b, span, Constraint::Contains(a));
                    self.check_constraints(span, ctx, a)?;
                    self.check_constraints(span, ctx, b)?;
                    Ok(self.push_type(Type::Bool))
                }
            },

            ExpressionKind::AssertEq(a, b) => {
                bin_op!(self, span, ctx, a, b, Constraint::Equ)?;
                Ok(self.push_type(Type::Bool))
            }

            ExpressionKind::Or(a, b) | ExpressionKind::And(a, b) => {
                let a = self.expression(a, ctx)?;
                let b = self.expression(b, ctx)?;
                let boolean = self.push_type(Type::Bool);
                self.unify(span, ctx, a, boolean)?;
                self.unify(span, ctx, b, boolean)
            }

            ExpressionKind::Neg(a) => {
                let a = self.expression(a, ctx)?;
                self.add_constraint(a, span, Constraint::Neg);
                Ok(a)
            }

            ExpressionKind::Not(a) => {
                let a = self.expression(a, ctx)?;
                let boolean = self.push_type(Type::Bool);
                self.unify(span, ctx, a, boolean)
            }

            ExpressionKind::Parenthesis(expr) => self.expression(expr, ctx),

            ExpressionKind::IfExpression { condition, pass, fail } => {
                let boolean = self.push_type(Type::Bool);
                let condition = self.expression(condition, ctx)?;
                self.unify(span, ctx, condition, boolean)?;
                let pass = self.expression(pass, ctx)?;
                let fail = self.expression(fail, ctx)?;
                self.unify(span, ctx, pass, fail)
            }

            ExpressionKind::Function { name: _, params, ret, body } => {
                let ss = self.stack.len();
                let mut args = Vec::new();
                let mut seen = HashMap::new();
                for (ident, ty) in params.iter() {
                    let ty = self.inner_resolve_type(span, ctx, ty, &mut seen)?;
                    args.push(ty);

                    let var = Variable {
                        ident: ident.clone(),
                        ty,
                        kind: VarKind::Const,
                        span,
                    };
                    self.stack.push(var);
                }

                let ret = self.inner_resolve_type(span, ctx, ret, &mut seen)?;
                if let Some(actual_ret) = self.statement(body, ctx)? {
                    self.unify(span, ctx, ret, actual_ret)?;
                } else {
                    let void = self.push_type(Type::Void);
                    self.unify(span, ctx, ret, void)?;
                }

                self.stack.truncate(ss);

                Ok(self.push_type(Type::Function(args, ret)))
            }

            ExpressionKind::Blob { blob, fields } => {
                let blob_ty = self.type_assignable(ctx, blob)?;
                let (blob_name, blob_fields) = match self.find_type(blob_ty) {
                    Type::Blob(name, fields) => (name, fields),
                    _ => unreachable!(),
                };

                let given_fields: BTreeMap<_, _> = fields
                    .iter()
                    .map(|(key, _)| Ok((key.clone(), self.push_type(Type::Unknown))))
                    .collect::<TypeResult<_>>()?;

                let mut errors = Vec::new();
                for (field, _) in blob_fields.iter() {
                    if !given_fields.contains_key(field) {
                        errors.push(type_error!(
                            self,
                            span,
                            TypeError::MissingField {
                                blob: blob_name.clone(),
                                field: field.clone(),
                            }
                        ));
                    }
                }

                for (field, _) in given_fields.iter() {
                    if !blob_fields.contains_key(field) {
                        errors.push(type_error!(
                            self,
                            span,
                            TypeError::UnknownField {
                                blob: blob_name.clone(),
                                field: field.clone(),
                            }
                        ));
                    }
                }

                if !errors.is_empty() {
                    return Err(errors);
                }

                let given_blob =
                    self.push_type(Type::Blob(blob_name.clone(), given_fields.clone()));

                // Unify the fields with their real types
                let ss = self.stack.len();
                for (key, expr) in fields {
                    if matches!(expr.kind, ExpressionKind::Function { .. }) {
                        self.stack.push(Variable {
                            ident: Identifier { name: "self".to_string(), span },
                            kind: VarKind::Const,
                            ty: given_blob,
                            span,
                        });
                    }
                    let expr_ty = self.expression(expr, ctx)?;
                    self.unify(span, ctx, expr_ty, given_fields[key])?;
                    self.stack.truncate(ss);
                }

                self.unify(span, ctx, given_blob, blob_ty)
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

            ExpressionKind::Set(exprs) => {
                let inner_ty = self.push_type(Type::Unknown);
                for expr in exprs.iter() {
                    let e = self.expression(expr, ctx)?;
                    self.unify(span, ctx, inner_ty, e)?;
                }
                Ok(self.push_type(Type::Set(inner_ty)))
            }

            ExpressionKind::Dict(exprs) => {
                let key_ty = self.push_type(Type::Unknown);
                let value_ty = self.push_type(Type::Unknown);
                for (key, value) in exprs.iter().zip(exprs.iter().skip(1)).step_by(2) {
                    let e = self.expression(key, ctx)?;
                    self.unify(span, ctx, key_ty, e)?;
                    let e = self.expression(value, ctx)?;
                    self.unify(span, ctx, value_ty, e)?;
                }
                Ok(self.push_type(Type::Dict(key_ty, value_ty)))
            }

            ExpressionKind::Int(_) => Ok(self.push_type(Type::Int)),
            ExpressionKind::Float(_) => Ok(self.push_type(Type::Float)),
            ExpressionKind::Str(_) => Ok(self.push_type(Type::Str)),
            ExpressionKind::Bool(_) => Ok(self.push_type(Type::Bool)),
            ExpressionKind::Nil => Ok(self.push_type(Type::Void)),
        }?;
        let res_ty = self.find_type(res);
        match res_ty {
            // Type::Blob(_, _) => Ok(self.push_type(res_ty)),
            _ => Ok(res),
        }
    }

    fn definition(&mut self, statement: &Statement, global: bool, ctx: TypeCtx) -> TypeResult<()> {
        let span = statement.span;
        match &statement.kind {
            StatementKind::Definition { ident, kind, ty, value } => {
                let defined_ty = self.resolve_type(span, ctx, &ty)?;

                let is_function = match &value.kind {
                    ExpressionKind::Function { params, .. } => {
                        let args = params
                            .iter()
                            .map(|_| self.push_type(Type::Unknown))
                            .collect();
                        let ret = self.push_type(Type::Unknown);
                        let fn_ty = self.push_type(Type::Function(args, ret));
                        self.unify(span, ctx, defined_ty, fn_ty)?;
                        let var = Variable { ident: ident.clone(), ty: fn_ty, kind: *kind, span };
                        if global {
                            self.globals
                                .insert((ctx.namespace, ident.name.clone()), Name::Global(var));
                        } else {
                            self.stack.push(var);
                        }
                        true
                    }
                    _ => false,
                };

                let expression_ty = self.expression(value, ctx)?;
                self.unify(span, ctx, expression_ty, defined_ty)?;

                if !is_function {
                    let var = Variable {
                        ident: ident.clone(),
                        ty: defined_ty,
                        kind: *kind,
                        span,
                    };
                    if global {
                        self.globals.insert(
                            (ctx.namespace, ident.name.clone()),
                            Name::Global(var.clone()),
                        );
                    } else {
                        self.stack.push(var);
                    }
                }
            }
            _ => unreachable!(),
        }
        Ok(())
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

    fn find_node(&mut self, a: usize) -> &TypeNode {
        let ta = self.find(a);
        &self.types[ta]
    }

    fn find_node_mut(&mut self, a: usize) -> &mut TypeNode {
        let ta = self.find(a);
        &mut self.types[ta]
    }

    fn find_type(&mut self, a: usize) -> Type {
        self.find_node(a).ty.clone()
    }

    fn inner_bake_type(&mut self, a: usize, seen: &mut HashMap<usize, RuntimeType>) -> RuntimeType {
        let a = self.find(a);
        if seen.contains_key(&a) {
            return seen[&a].clone();
        }

        seen.insert(a, RuntimeType::Unknown);

        let res = match self.find_type(a) {
            Type::Unknown => RuntimeType::Unknown,
            Type::Ty => RuntimeType::Ty,
            Type::Void => RuntimeType::Void,
            Type::Int => RuntimeType::Int,
            Type::Float => RuntimeType::Float,
            Type::Bool => RuntimeType::Bool,
            Type::Str => RuntimeType::String,
            Type::Tuple(tys) => RuntimeType::Tuple(
                tys.iter()
                    .map(|ty| self.inner_bake_type(*ty, seen))
                    .collect(),
            ),
            Type::List(ty) => RuntimeType::List(Box::new(self.inner_bake_type(ty, seen))),
            Type::Set(ty) => RuntimeType::Set(Box::new(self.inner_bake_type(ty, seen))),
            Type::Dict(ty_k, ty_v) => RuntimeType::Dict(
                Box::new(self.inner_bake_type(ty_k, seen)),
                Box::new(self.inner_bake_type(ty_v, seen)),
            ),
            Type::Function(args, ret) => RuntimeType::Function(
                args.iter()
                    .map(|ty| self.inner_bake_type(*ty, seen))
                    .collect(),
                Box::new(self.inner_bake_type(ret, seen)),
            ),
            Type::Blob(name, fields) => RuntimeType::Blob(
                name.clone(),
                fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.inner_bake_type(*ty, seen)))
                    .collect(),
            ),
            Type::Enum(name, variants) => RuntimeType::Enum(
                name.clone(),
                variants
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.inner_bake_type(*ty, seen)))
                    .collect(),
            ),

            Type::Invalid => RuntimeType::Invalid,
        };

        seen.insert(a, res.clone());
        res
    }

    fn bake_type(&mut self, a: usize) -> RuntimeType {
        self.inner_bake_type(a, &mut HashMap::new())
    }

    // This span is wierd - is it weird?
    fn check_constraints(&mut self, span: Span, ctx: TypeCtx, a: usize) -> TypeResult<()> {
        for (constraint, original_span) in self.find_node(a).constraints.clone().iter() {
            match constraint {
                // It would be nice to know from where this came from
                Constraint::Add(b) => self.add(span, ctx, a, *b),
                Constraint::Sub(b) => self.sub(span, ctx, a, *b),
                Constraint::Mul(b) => self.mul(span, ctx, a, *b),
                Constraint::Div(b) => self.div(span, ctx, a, *b),
                Constraint::Equ(b) => self.equ(span, ctx, a, *b),
                Constraint::Cmp(b) => self.cmp(span, ctx, a, *b),
                Constraint::CmpEqu(b) => self.equ(span, ctx, a, *b).and(self.cmp(span, ctx, a, *b)),

                Constraint::Neg => match self.find_type(a) {
                    Type::Unknown | Type::Int | Type::Float => Ok(()),
                    _ => err_type_error!(
                        self,
                        span,
                        TypeError::UniOp { val: self.bake_type(a), op: "-".to_string() }
                    ),
                },

                Constraint::IndexedBy(b) => self.is_indexed_by(span, ctx, a, *b),
                Constraint::Indexes(b) => self.is_indexed_by(span, ctx, *b, a),

                Constraint::IndexingGives(b) => self.is_given_by_indexing(span, ctx, a, *b),
                Constraint::GivenByIndex(b) => self.is_given_by_indexing(span, ctx, *b, a),

                Constraint::ConstantIndex(index, ret) => {
                    self.constant_index(span, ctx, a, *index, *ret)
                }

                Constraint::Field(name, expected_ty) => match self.find_type(a).clone() {
                    Type::Unknown => Ok(()),
                    Type::Blob(blob_name, fields) => match fields.get(name) {
                        Some(actual_ty) => {
                            self.unify(span, ctx, *expected_ty, *actual_ty).map(|_| ())
                        }
                        None => err_type_error!(
                            self,
                            span,
                            TypeError::MissingField {
                                blob: blob_name.clone(),
                                field: name.clone(),
                            }
                        ),
                    },
                    _ => err_type_error!(
                        self,
                        span,
                        TypeError::Exotic,
                        "The type \"{}\" is not a blob, so it cannot have a field \"{}\"",
                        self.bake_type(a),
                        name
                    ),
                },

                Constraint::Num => match self.find_type(a) {
                    Type::Unknown | Type::Float | Type::Int => Ok(()),
                    _ => err_type_error!(
                        self,
                        span,
                        TypeError::Violating(self.bake_type(a)),
                        "The Num constraint forces int or float"
                    ),
                },

                Constraint::Container => match self.find_type(a) {
                    Type::Unknown | Type::Set(..) | Type::List(..) | Type::Dict(..) => Ok(()),
                    _ => err_type_error!(
                        self,
                        span,
                        TypeError::Violating(self.bake_type(a)),
                        "The Container constraint forces set, list or dict"
                    ),
                },

                Constraint::SameContainer(b) => match (self.find_type(a), self.find_type(*b)) {
                    (Type::Unknown, _)
                    | (_, Type::Unknown)
                    | (Type::Set(..), Type::Set(..))
                    | (Type::List(..), Type::List(..))
                    | (Type::Dict(..), Type::Dict(..)) => Ok(()),

                    _ => err_type_error!(
                        self,
                        span,
                        TypeError::Mismatch {
                            got: self.bake_type(a),
                            expected: self.bake_type(*b)
                        },
                        "The SameContainer constraint forces the outer containers to match"
                    ),
                },

                Constraint::Contains(b) => self.contains(span, ctx, a, *b),
                Constraint::IsContainedIn(b) => self.contains(span, ctx, *b, a),
            }
            .help(self, *original_span, "Requirement came from".to_string())?
        }
        Ok(())
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

        // TODO(ed): Which span should we keep? The one closest to the top? Should we combine them?
        for (con, span) in self.types[b].constraints.clone().iter() {
            self.types[a].constraints.insert(con.clone(), *span);
        }
    }

    fn unify(&mut self, span: Span, ctx: TypeCtx, a: usize, b: usize) -> TypeResult<usize> {
        let a = self.find(a);
        let b = self.find(b);

        if a == b {
            return Ok(a);
        }

        match (self.find_type(a), self.find_type(b)) {
            (_, Type::Unknown) => self.find_node_mut(b).ty = self.find_type(a),

            (Type::Unknown, _) => self.find_node_mut(a).ty = self.find_type(b),

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
                    // TODO: Make sure there is one place this is checked.
                    if a_args.len() != b_args.len() {
                        return err_type_error!(
                            self,
                            span,
                            TypeError::WrongArity { got: a_args.len(), expected: b_args.len() }
                        );
                    }
                    for (a, b) in a_args.iter().zip(b_args.iter()) {
                        self.unify(span, ctx, *a, *b)?;
                    }
                    self.unify(span, ctx, a_ret, b_ret)?;
                }

                (Type::Blob(_a_blob, a_fields), Type::Blob(b_blob, b_fields)) => {
                    // TODO(ed): This should give information about the violating fields.
                    if a_fields.len() != b_fields.len() {
                        return err_type_error!(
                            self,
                            span,
                            TypeError::Mismatch {
                                got: self.bake_type(a),
                                expected: self.bake_type(b)
                            },
                            "Blobs have different number of fields"
                        );
                    }

                    for (a_field, a_ty) in a_fields.iter() {
                        let b_ty = match b_fields.get(a_field) {
                            Some(b_ty) => *b_ty,
                            None => {
                                return err_type_error!(
                                    self,
                                    span,
                                    TypeError::MissingField {
                                        blob: b_blob.clone(),
                                        field: a_field.clone()
                                    }
                                )
                            }
                        };
                        self.unify(span, ctx, *a_ty, b_ty)?;
                    }
                }

                (Type::Enum(a_name, a_variants), Type::Enum(b_name, b_variants)) => {
                    for (a_var, _) in a_variants.iter() {
                        if !b_variants.contains_key(a_var) {
                            return err_type_error!(
                                self,
                                span,
                                TypeError::UnknownVariant(b_name.clone(), a_var.clone())
                            );
                        }
                    }
                    for (b_var, b_ty) in b_variants.iter() {
                        let a_ty = match a_variants.get(b_var) {
                            Some(a_ty) => *a_ty,
                            None => {
                                return err_type_error!(
                                    self,
                                    span,
                                    TypeError::UnknownVariant(a_name.clone(), b_var.clone())
                                )
                            }
                        };
                        self.unify(span, ctx, a_ty, *b_ty)?;
                    }
                }

                _ => {
                    return err_type_error!(
                        self,
                        span,
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
            self.find_node(ty).constraints,
            same
        );
    }

    fn inner_copy(&mut self, old_ty: usize, seen: &mut HashMap<usize, usize>) -> usize {
        let old_ty = self.find(old_ty);

        if let Some(res) = seen.get(&old_ty) {
            return *res;
        }
        let new_ty = self.push_type(Type::Unknown);
        seen.insert(old_ty, new_ty);

        self.find_node_mut(new_ty).constraints = self
            .find_node(old_ty)
            .constraints
            .clone()
            .iter()
            .map(|(con, span)| {
                (
                    match &con {
                        Constraint::Add(x) => Constraint::Add(self.inner_copy(*x, seen)),
                        Constraint::Sub(x) => Constraint::Sub(self.inner_copy(*x, seen)),
                        Constraint::Mul(x) => Constraint::Mul(self.inner_copy(*x, seen)),
                        Constraint::Div(x) => Constraint::Div(self.inner_copy(*x, seen)),
                        Constraint::Equ(x) => Constraint::Equ(self.inner_copy(*x, seen)),
                        Constraint::Cmp(x) => Constraint::Cmp(self.inner_copy(*x, seen)),
                        Constraint::CmpEqu(x) => Constraint::CmpEqu(self.inner_copy(*x, seen)),
                        Constraint::Neg => Constraint::Neg,
                        Constraint::Indexes(x) => Constraint::Indexes(self.inner_copy(*x, seen)),
                        Constraint::IndexedBy(x) => {
                            Constraint::IndexedBy(self.inner_copy(*x, seen))
                        }
                        Constraint::IndexingGives(x) => {
                            Constraint::IndexingGives(self.inner_copy(*x, seen))
                        }
                        Constraint::GivenByIndex(x) => {
                            Constraint::GivenByIndex(self.inner_copy(*x, seen))
                        }
                        Constraint::ConstantIndex(i, x) => {
                            Constraint::ConstantIndex(*i, self.inner_copy(*x, seen))
                        }
                        Constraint::Field(f, x) => {
                            Constraint::Field(f.clone(), self.inner_copy(*x, seen))
                        }
                        Constraint::Num => Constraint::Num,
                        Constraint::Container => Constraint::Container,
                        Constraint::SameContainer(x) => {
                            Constraint::SameContainer(self.inner_copy(*x, seen))
                        }
                        Constraint::Contains(x) => Constraint::Contains(self.inner_copy(*x, seen)),
                        Constraint::IsContainedIn(x) => {
                            Constraint::IsContainedIn(self.inner_copy(*x, seen))
                        }
                    },
                    *span,
                )
            })
            .collect();

        let ty = self.find_type(old_ty);
        self.find_node_mut(new_ty).ty = match ty {
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

            Type::Enum(name, variants) => Type::Enum(
                name.clone(),
                variants
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

    fn can_assign(&mut self, span: Span, ctx: TypeCtx, assignable: &Assignable) -> TypeResult<()> {
        match &assignable.kind {
            AssignableKind::Variant { .. } => {
                err_type_error!(
                    self,
                    span,
                    TypeError::Assignability,
                    "Cannot assign to enum-variant"
                )
            }
            AssignableKind::Read(ident) => {
                match self.stack.iter().rfind(|v| v.ident.name == ident.name) {
                    Some(var) if !var.kind.immutable() => Ok(()),
                    Some(var) => err_type_error!(
                        self,
                        span,
                        TypeError::Assignability,
                        "Cannot assign to constants"
                    )
                    .help(self, var.span, "Originally defined here".into()),
                    // Not a local variable. Is it a global?
                    _ => match self.globals.get(&(ctx.namespace, ident.name.clone())) {
                        Some(Name::Global(var)) => {
                            if !var.kind.immutable() {
                                Ok(())
                            } else {
                                err_type_error!(
                                    self,
                                    span,
                                    TypeError::Assignability,
                                    "Cannot assign to constants"
                                )
                                .help(
                                    self,
                                    var.span,
                                    "Originally defined here".into(),
                                )
                            }
                        }
                        Some(_) => err_type_error!(
                            self,
                            span,
                            TypeError::Assignability,
                            "\"{}\" is not a variable",
                            ident.name.clone()
                        ),
                        _ => err_type_error!(
                            self,
                            span,
                            TypeError::Assignability,
                            "Variable \"{}\" not found. If declaring, use :=",
                            ident.name.clone()
                        ),
                    },
                }
            }
            AssignableKind::ArrowCall(_, _, _) | AssignableKind::Call(_, _) => err_type_error!(
                self,
                span,
                TypeError::Assignability,
                "Cannot assign to function calls"
            ),
            AssignableKind::Access(outer, ident) => match self.namespace_chain(&outer, ctx) {
                Some(ctx) => self.can_assign(
                    span,
                    ctx,
                    &Assignable { span, kind: AssignableKind::Read(ident.clone()) },
                ),
                None => Ok(()),
            },
            AssignableKind::Index(_, _) => Ok(()),
            AssignableKind::Expression(_) => err_type_error!(
                self,
                span,
                TypeError::Assignability,
                "Cannot assign to expressions"
            ),
        }
    }

    fn add_constraint(&mut self, a: usize, span: Span, constraint: Constraint) {
        self.find_node_mut(a)
            .constraints
            .entry(constraint)
            .or_insert_with(|| span);
    }

    fn add(&mut self, span: Span, ctx: TypeCtx, a: usize, b: usize) -> TypeResult<()> {
        match (self.find_type(a), self.find_type(b)) {
            (Type::Unknown, _) | (_, Type::Unknown) => Ok(()),

            (Type::Float, Type::Float) | (Type::Int, Type::Int) | (Type::Str, Type::Str) => Ok(()),

            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b.iter()) {
                    self.add(span, ctx, *a, *b)?;
                }
                Ok(())
            }

            _ => err_type_error!(
                self,
                span,
                TypeError::BinOp {
                    lhs: self.bake_type(a),
                    rhs: self.bake_type(b),
                    op: "+".to_string(),
                }
            ),
        }
    }

    fn sub(&mut self, span: Span, ctx: TypeCtx, a: usize, b: usize) -> TypeResult<()> {
        match (self.find_type(a), self.find_type(b)) {
            (Type::Unknown, _) | (_, Type::Unknown) => Ok(()),

            (Type::Float, Type::Float) | (Type::Int, Type::Int) => Ok(()),

            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b.iter()) {
                    self.sub(span, ctx, *a, *b)?;
                }
                Ok(())
            }

            _ => err_type_error!(
                self,
                span,
                TypeError::BinOp {
                    lhs: self.bake_type(a),
                    rhs: self.bake_type(b),
                    op: "-".to_string(),
                }
            ),
        }
    }

    fn mul(&mut self, span: Span, ctx: TypeCtx, a: usize, b: usize) -> TypeResult<()> {
        match (self.find_type(a), self.find_type(b)) {
            (Type::Unknown, _) | (_, Type::Unknown) => Ok(()),

            (Type::Float, Type::Float) | (Type::Int, Type::Int) => Ok(()),

            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b.iter()) {
                    self.mul(span, ctx, *a, *b)?;
                }
                Ok(())
            }

            // TODO(ed): This isn't actually implemented in the runtime.
            (Type::Tuple(a), Type::Float) | (Type::Tuple(a), Type::Int) => {
                for a in a.iter() {
                    self.mul(span, ctx, *a, b)?;
                }
                Ok(())
            }
            (Type::Float, Type::Tuple(b)) | (Type::Int, Type::Tuple(b)) => {
                for b in b.iter() {
                    self.mul(span, ctx, a, *b)?;
                }
                Ok(())
            }

            _ => err_type_error!(
                self,
                span,
                TypeError::BinOp {
                    lhs: self.bake_type(a),
                    rhs: self.bake_type(b),
                    op: "*".to_string(),
                }
            ),
        }
    }

    fn div(&mut self, span: Span, ctx: TypeCtx, a: usize, b: usize) -> TypeResult<()> {
        match (self.find_type(a), self.find_type(b)) {
            (Type::Unknown, _) => Ok(()),
            (_, Type::Unknown) => Ok(()),

            (Type::Float, Type::Float) => Ok(()),
            (Type::Int, Type::Int) => Ok(()),

            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b.iter()) {
                    self.div(span, ctx, *a, *b)?;
                }
                Ok(())
            }

            // TODO(ed): This isn't actually implemented in the runtime.
            (Type::Tuple(a), Type::Float) | (Type::Tuple(a), Type::Int) => {
                for a in a.iter() {
                    self.div(span, ctx, *a, b)?;
                }
                Ok(())
            }
            (Type::Float, Type::Tuple(b)) | (Type::Int, Type::Tuple(b)) => {
                for b in b.iter() {
                    self.div(span, ctx, a, *b)?;
                }
                Ok(())
            }

            _ => err_type_error!(
                self,
                span,
                TypeError::BinOp {
                    lhs: self.bake_type(a),
                    rhs: self.bake_type(b),
                    op: "/".to_string(),
                }
            ),
        }
    }

    fn equ(&mut self, span: Span, ctx: TypeCtx, a: usize, b: usize) -> TypeResult<()> {
        // Equal types all support equality!
        self.unify(span, ctx, a, b).map(|_| ())
    }

    fn cmp(&mut self, span: Span, ctx: TypeCtx, a: usize, b: usize) -> TypeResult<()> {
        match (self.find_type(a), self.find_type(b)) {
            (Type::Unknown, _) | (_, Type::Unknown) => Ok(()),

            (Type::Float, Type::Float)
            | (Type::Int, Type::Int)
            | (Type::Int, Type::Float)
            | (Type::Float, Type::Int) => Ok(()),

            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b.iter()) {
                    self.cmp(span, ctx, *a, *b)?;
                }
                Ok(())
            }

            // TODO(ed): Maybe sets?
            _ => err_type_error!(
                self,
                span,
                TypeError::BinOp {
                    lhs: self.bake_type(a),
                    rhs: self.bake_type(b),
                    op: "<".to_string(),
                }
            ),
        }
    }

    fn is_indexed_by(&mut self, span: Span, ctx: TypeCtx, a: usize, b: usize) -> TypeResult<()> {
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

            _ => err_type_error!(
                self,
                span,
                TypeError::BinOp {
                    lhs: self.bake_type(a),
                    rhs: self.bake_type(b),
                    op: "Indexing".to_string(),
                }
            ),
        }
    }

    fn is_given_by_indexing(
        &mut self,
        span: Span,
        ctx: TypeCtx,
        a: usize,
        b: usize,
    ) -> TypeResult<()> {
        match self.find_type(a) {
            Type::Unknown => Ok(()),

            Type::Tuple(_) => {
                // NOTE(ed): If we get here - it means we're checking the constraint, but the
                // constraint shouldn't be added because we only ever check constants.
                return err_type_error!(
                    self,
                    span,
                    TypeError::Exotic,
                    "Tuples can only be indexed by positive integer constants"
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

            _ => err_type_error!(
                self,
                span,
                TypeError::BinOp {
                    lhs: self.bake_type(a),
                    rhs: self.bake_type(b),
                    op: "Indexing".to_string(),
                }
            ),
        }
    }

    fn constant_index(
        &mut self,
        span: Span,
        ctx: TypeCtx,
        a: usize,
        index: i64,
        ret: usize,
    ) -> TypeResult<()> {
        match self.find_type(a) {
            Type::Tuple(tys) => match tys.get(index as usize) {
                Some(ty) => self.unify(span, ctx, *ty, ret).map(|_| ()),
                None => err_type_error!(
                    self,
                    span,
                    TypeError::TupleIndexOutOfRange { got: index, length: tys.len() }
                ),
            },
            Type::List(ty) => self.unify(span, ctx, ty, ret).map(|_| ()),
            Type::Dict(key_ty, value_ty) => {
                let int_ty = self.push_type(Type::Int);
                self.unify(span, ctx, key_ty, int_ty)?;
                self.unify(span, ctx, value_ty, ret)?;
                Ok(())
            }
            _ => err_type_error!(
                self,
                span,
                TypeError::Violating(self.bake_type(a)),
                "This type cannot be indexed"
            ),
        }
    }

    fn contains(&mut self, span: Span, ctx: TypeCtx, a: usize, b: usize) -> TypeResult<()> {
        match (self.find_type(a), self.find_type(b)) {
            (Type::Unknown, _) | (_, Type::Unknown) => Ok(()),

            (Type::Set(x), _) | (Type::List(x), _) => self.unify(span, ctx, x, b).map(|_| ()),

            (Type::Dict(kx, vx), Type::Tuple(ys)) => {
                if ys.len() == 2 {
                    self.unify(span, ctx, kx, ys[0])?;
                    self.unify(span, ctx, vx, ys[1]).map(|_| ())
                } else {
                    err_type_error!(
                        self,
                        span,
                        TypeError::Violating(self.bake_type(b)),
                        "Expected length of tuple to be 2 but it was {}",
                        ys.len()
                    )
                }
            }

            _ => err_type_error!(
                self,
                span,
                TypeError::Mismatch {
                    got: self.bake_type(a),
                    expected: self.bake_type(b)
                },
                "The Contains constraint forces a container"
            ),
        }
    }

    fn solve(&mut self, statements: &Vec<(&Statement, usize)>) -> TypeResult<()> {
        // Initialize the namespaces first.
        for (statement, namespace) in statements.iter() {
            if matches!(statement.kind, StatementKind::Use { .. }) {
                self.outer_statement(statement, TypeCtx { namespace: *namespace })?;
            }
        }

        // Then the rest.
        for (statement, namespace) in statements.iter() {
            if !matches!(statement.kind, StatementKind::Use { .. }) {
                self.outer_statement(statement, TypeCtx { namespace: *namespace })?;
            }
        }

        let ctx = TypeCtx { namespace: 0 };
        match self.globals.get(&(0, "start".to_string())).cloned() {
            Some(Name::Global(var)) => {
                let void = self.push_type(Type::Void);
                let start = self.push_type(Type::Function(Vec::new(), void));
                self.unify(var.ident.span, ctx, var.ty, start)
                    .map(|_| ())
                    .or_else(|_| {
                        err_type_error!(
                            self,
                            var.ident.span,
                            TypeError::Mismatch {
                                got: self.bake_type(var.ty),
                                expected: self.bake_type(start),
                            },
                            "The start function has the wrong type"
                        )
                    })
            }
            Some(_) => {
                err_type_error!(
                    self,
                    Span::zero(ctx.namespace),
                    TypeError::Exotic,
                    "Expected a start function in the main module - but it was something else"
                )
            }
            None => {
                err_type_error!(
                    self,
                    Span::zero(ctx.namespace),
                    TypeError::Exotic,
                    "Expected a start function in the main module - but couldn't find it"
                )
            }
        }
    }

    fn span_file(&self, span: &Span) -> PathBuf {
        self.namespace_to_file[&span.file_id].clone()
    }
}

pub(crate) fn solve(
    statements: &Vec<(&Statement, usize)>,
    namespace_to_file: &HashMap<usize, PathBuf>,
    functions: &HashMap<String, (usize, RustFunction, ParserType)>,
) -> TypeResult<()> {
    TypeChecker::new(namespace_to_file, functions).solve(statements)
}
