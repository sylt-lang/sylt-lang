use std::collections::HashMap;
use sylt_common::error::{Error, Helper, TypeError};
use sylt_common::{FileOrLib, TyID, Type as RuntimeType};
use sylt_parser::{
    expression::ComparisonKind, Assignable, AssignableKind, Expression, ExpressionKind, Identifier,
    Op as ParserOp, Span, Statement, StatementKind, Type as ParserType, TypeAssignable,
    TypeAssignableKind, TypeConstraint, TypeKind, VarKind,
};

use crate::ty::Purity;
use crate::{ty::Type, NamespaceID};
use std::collections::{BTreeMap, BTreeSet};

type TypeResult<T> = Result<T, Vec<Error>>;

type RetNValue = (Option<TyID>, TyID);

fn no_ret(value: TyID) -> TypeResult<RetNValue> {
    Ok((None, value))
}

fn with_ret(ret: Option<TyID>, value: TyID) -> TypeResult<RetNValue> {
    Ok((ret, value))
}

trait Help {
    fn help(self, typechecker: &TypeChecker, span: Span, message: String) -> Self;
    fn help_no_span(self, message: String) -> Self;
}

impl<T> Help for TypeResult<T> {
    fn help(mut self, typechecker: &TypeChecker, span: Span, message: String) -> Self {
        match &mut self {
            Ok(_) => {}
            Err(errs) => match &mut errs.last_mut() {
                Some(Error::TypeError { helpers, .. }) => {
                    helpers.push(Helper {
                        at: Some((typechecker.span_file(&span), span)),
                        message,
                    });
                }
                _ => panic!("Cannot help on this error since the error is empty"),
            },
        }
        self
    }

    fn help_no_span(mut self, message: String) -> Self {
        match &mut self {
            Ok(_) => {}
            Err(errs) => match &mut errs.last_mut() {
                Some(Error::TypeError { helpers, .. }) => {
                    helpers.push(Helper { at: None, message });
                }
                _ => panic!("Cannot help on this error since the error is empty"),
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
        let (a_ret, a) = $self.expression($a, $ctx)?;
        let (b_ret, b) = $self.expression($b, $ctx)?;
        $self.add_constraint(a, $span, $con(b));
        $self.add_constraint(b, $span, $con(a));
        $self.check_constraints($span, $ctx, a)?;
        $self.check_constraints($span, $ctx, b)?;
        with_ret($self.unify_option($span, $ctx, a_ret, b_ret)?, a)
    }};
}

#[derive(Clone, Debug)]
struct Variable {
    ident: Identifier,
    ty: TyID,
    kind: VarKind,
    span: Span,
}

#[derive(Clone, Debug)]
struct TypeNode {
    ty: Type,
    parent: Option<TyID>,
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
    Add(TyID),
    Sub(TyID),
    Mul(TyID),
    Div(TyID),
    Equ(TyID),
    Cmp(TyID),
    CmpEqu(TyID),

    Neg,

    Indexes(TyID),
    IndexedBy(TyID),
    IndexingGives(TyID),
    GivenByIndex(TyID),
    ConstantIndex(i64, TyID),

    Field(String, TyID),

    Num,
    Container,
    SameContainer(TyID),
    Contains(TyID),
    IsContainedIn(TyID),

    Enum,
    Variant(String, Option<TyID>),
    TotalEnum(BTreeSet<String>),

    Variable,
}

pub struct TypeChecker {
    globals: HashMap<(NamespaceID, String), Name>,
    stack: Vec<Variable>,
    types: Vec<TypeNode>,
    namespace_to_file: HashMap<NamespaceID, FileOrLib>,
    // TODO(ed): This can probably be removed via some trickery
    pub file_to_namespace: HashMap<FileOrLib, NamespaceID>,
}

#[derive(Clone, Debug, Copy)]
struct TypeCtx {
    inside_loop: bool,
    inside_pure: bool,
    namespace: NamespaceID,
}

impl TypeCtx {
    fn namespace(namespace: NamespaceID) -> Self {
        Self { inside_loop: false, inside_pure: false, namespace }
    }

    fn enter_loop(self) -> Self {
        Self { inside_loop: true, ..self }
    }

    fn enter_pure(self) -> Self {
        Self { inside_pure: true, ..self }
    }
}

#[derive(Debug, Clone)]
enum Name {
    Type(TyID),
    Global(Variable),
    Namespace(NamespaceID),
}

impl TypeChecker {
    fn new(namespace_to_file: &HashMap<NamespaceID, FileOrLib>) -> Self {
        Self {
            globals: HashMap::new(),
            stack: Vec::new(),
            types: Vec::new(),
            namespace_to_file: namespace_to_file.clone(),
            file_to_namespace: namespace_to_file
                .iter()
                .map(|(a, b)| (b.clone(), a.clone()))
                .collect(),
        }
    }

    fn push_type(&mut self, ty: Type) -> TyID {
        let ty_id = TyID(self.types.len());
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

    fn type_assignable(&mut self, ctx: TypeCtx, assignable: &TypeAssignable) -> TypeResult<TyID> {
        match &assignable.kind {
            TypeAssignableKind::Read(ident) => match self
                .globals
                .get(&(ctx.namespace, ident.name.clone()))
                .cloned()
            {
                Some(Name::Type(ty)) if matches!(self.find_type(ty), Type::Unknown) => Ok(ty),
                Some(Name::Type(ty)) => Ok(self.copy(ty)),
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
                    Some(Name::Type(ty)) if matches!(self.find_type(ty), Type::Unknown) => Ok(ty),
                    Some(Name::Type(ty)) => Ok(self.copy(ty)),
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

    fn resolve_type(&mut self, span: Span, ctx: TypeCtx, ty: &ParserType) -> TypeResult<TyID> {
        self.inner_resolve_type(span, ctx, ty, &mut HashMap::new())
    }

    fn resolve_constraint(
        &mut self,
        span: Span,
        var: TyID,
        constraint: &TypeConstraint,
        seen: &HashMap<String, TyID>,
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
            seen: &HashMap<String, TyID>,
        ) -> TypeResult<TyID> {
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
        seen: &mut HashMap<String, TyID>,
    ) -> TypeResult<TyID> {
        use TypeKind::*;
        let ty = match &ty.kind {
            Implied => Type::Unknown,

            Resolved(ty) => match ty {
                RuntimeType::Void => Type::Void,
                RuntimeType::Nil => Type::Nil,
                RuntimeType::Unknown => Type::Unknown,
                RuntimeType::Int => Type::Int,
                RuntimeType::Float => Type::Float,
                RuntimeType::Bool => Type::Bool,
                RuntimeType::String => Type::Str,
                x => unreachable!("Got an unexpected resolved type '{:?}'", x),
            },

            UserDefined(assignable, vars) => {
                let ty = self.type_assignable(ctx, assignable)?;
                self.print_type(ty);
                match self.find_type(ty) {
                    Type::Blob(name, _, sub) | Type::Enum(name, _, sub) => {
                        for (i, var) in vars.iter().enumerate() {
                            if sub.len() == i {
                                return err_type_error!(
                                    self,
                                    var.span,
                                    TypeError::Exotic,
                                    "The type {} takes at most {} type arguments",
                                    name.name,
                                    sub.len()
                                ).help(self, name.span, "Defined here".into());
                            }
                            let var_ty = self.inner_resolve_type(var.span, ctx, var, seen)?;
                            self.unify(span, ctx, var_ty, sub[i])?;
                        }
                    }

                    // NOTE(ed): Is this going to hant me later?
                    // Gives better errors for recursive types - which are illegal.
                    Type::Unknown => { }

                    _ => {
                        return err_type_error!(
                            self,
                            span,
                            TypeError::Violating(self.bake_type(ty)),
                            "Only enums and blobs can take type-arguments"
                        );
                    }
                }
                return Ok(ty);
            }

            Fn { constraints, params, ret, is_pure } => {
                let params = params
                    .iter()
                    .map(|t| self.inner_resolve_type(span, ctx, t, seen))
                    .collect::<TypeResult<Vec<_>>>()?;
                let ret = self.inner_resolve_type(span, ctx, ret, seen)?;
                for (var, constraints) in constraints.iter() {
                    match seen.get(var) {
                        Some(var) => {
                            // NOTE(ed): This disallowes type-variables that are only used for
                            // constraints.
                            for constraint in constraints.iter() {
                                self.resolve_constraint(span, *var, constraint, seen)?;
                            }
                        }
                        None => {
                            return err_type_error!(
                                self,
                                span,
                                TypeError::UnresolvedName(var.clone()),
                                "Unused type-variable. (Only usages in the function signature are counted)"
                            );
                        }
                    }
                }
                let purity = is_pure.then(|| Purity::Pure).unwrap_or(Purity::Undefined);
                Type::Function(params, ret, purity)
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

    fn statement(&mut self, statement: &mut Statement, ctx: TypeCtx) -> TypeResult<Option<TyID>> {
        let span = statement.span;
        match &mut statement.kind {
            StatementKind::Ret { value: Some(value) } => Ok(Some({
                let (ret, value) = self.expression(value, ctx)?;
                match ret {
                    Some(ret) => self.unify(span, ctx, value, ret)?,
                    None => value,
                }
            })),
            StatementKind::Ret { value: None } => Ok(Some(self.push_type(Type::Void))),

            StatementKind::Block { statements } => {
                let (ret, _expr) = self.expression_block(span, statements, ctx)?;
                Ok(ret)
            }

            StatementKind::StatementExpression { value } => {
                let (ret, _) = self.expression(value, ctx)?;
                Ok(ret)
            }

            StatementKind::Assignment { kind, target, value } => {
                self.can_assign(span, ctx, target)?;

                if ctx.inside_pure {
                    return err_type_error!(
                        self,
                        span,
                        TypeError::Exotic,
                        "Cannot make assignments in pure functions"
                    );
                }

                let (expression_ret, expression_ty) = self.expression(value, ctx)?;
                let (target_ret, target_ty) = self.assignable(target, ctx)?;
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
                        let float_ty = self.push_type(Type::Float);
                        self.unify(span, ctx, target_ty, float_ty)?;
                        self.add_constraint(expression_ty, span, Constraint::Div(target_ty));
                        self.add_constraint(target_ty, span, Constraint::Div(expression_ty));
                    }
                };
                self.unify(span, ctx, expression_ty, target_ty)?;
                self.unify_option(span, ctx, expression_ret, target_ret)
            }

            StatementKind::Definition { .. } => self.definition(statement, false, ctx),

            StatementKind::Loop { condition, body } => {
                let (ret, condition) = self.expression(condition, ctx)?;
                let boolean = self.push_type(Type::Bool);
                self.unify(span, ctx, boolean, condition)?;

                let body_ret = self.statement(body, ctx.enter_loop())?;
                self.unify_option(span, ctx, ret, body_ret)
            }

            StatementKind::Break => {
                if !ctx.inside_loop {
                    err_type_error!(self, span, TypeError::Exotic, "`break` only works in loops")
                } else {
                    Ok(None)
                }
            }
            StatementKind::Continue => {
                if !ctx.inside_loop {
                    err_type_error!(
                        self,
                        span,
                        TypeError::Exotic,
                        "`continue` only works in loops"
                    )
                } else {
                    Ok(None)
                }
            }

            StatementKind::Unreachable => Ok(None),
            StatementKind::EmptyStatement => Ok(None),

            StatementKind::Use { .. }
            | StatementKind::FromUse { .. }
            | StatementKind::Blob { .. }
            | StatementKind::Enum { .. }
            | StatementKind::ExternalDefinition { .. } => {
                unreachable!(
                    "Illegal inner statement at {:?}! Parser should have caught this",
                    span
                )
            }
        }
    }

    fn outer_statement(&mut self, statement: &mut Statement, ctx: TypeCtx) -> TypeResult<()> {
        let span = statement.span;
        match &statement.kind {
            StatementKind::Use { name, file, .. } => {
                let ident = name.ident();
                let other = self.file_to_namespace[file];
                self.globals
                    .insert((ctx.namespace, ident.name.clone()), Name::Namespace(other));
            }

            StatementKind::FromUse { imports, file, .. } => {
                // TODO(ed): This shouldn't be nessecary since the namespace
                // should be set up correctly already.
                let other = self.file_to_namespace[file];
                for (ident, alias) in imports.iter() {
                    let name = self.globals[&(other, ident.name.clone())].clone();
                    let ident_name = &alias.as_ref().unwrap_or(ident).name;

                    match name {
                        Name::Global(other_var) => {
                            let var = Variable {
                                ident: alias.as_ref().unwrap_or(ident).clone(),
                                ty: self.push_type(Type::Unknown),
                                kind: VarKind::Const,
                                span,
                            };
                            self.unify(span, ctx, var.ty, other_var.ty)?;
                            self.globals
                                .insert((ctx.namespace, ident_name.clone()), Name::Global(var));
                        }

                        Name::Type(_) => {
                            self.globals
                                .insert((ctx.namespace, ident_name.clone()), name.clone());
                        }

                        Name::Namespace(_) => {
                            return err_type_error!(
                                self,
                                span,
                                TypeError::Exotic,
                                "From import of namespaces is not implemented"
                            );
                        }
                    }
                }
            }
            StatementKind::Enum { name, variants, variables } => {
                let enum_ty = self.push_type(Type::Unknown);
                self.globals
                    .insert((ctx.namespace, name.name.clone()), Name::Type(enum_ty));
                let mut resolved_variants = BTreeMap::new();
                let mut type_params = Vec::new();
                let mut seen = HashMap::new();
                for v in variables.iter() {
                    let ty = self.push_type(Type::Unknown);
                    type_params.push(ty);
                    seen.insert(v.name.clone(), ty);
                }
                let num_vars = seen.len();
                for (k, t) in variants.iter() {
                    resolved_variants.insert(
                        k.name.clone(),
                        (k.span, self.inner_resolve_type(span, ctx, t, &mut seen)?),
                    );

                    if num_vars != seen.len() {
                        return err_type_error!(
                            self,
                            k.span,
                            TypeError::Exotic,
                            "Unknown generic {}",
                            t
                        )
                        .help(self, span, "While defining".to_string())
                        .help_no_span(format!(
                            "Generics have the be defined before use, like this: `{} :: enum({})`",
                            name.name, t
                        ));
                    }
                }
                let ty = self.push_type(Type::Enum(name.clone(), resolved_variants, type_params));
                self.unify(span, ctx, ty, enum_ty)?;
            }

            StatementKind::Blob { name, fields, variables } => {
                let blob_ty = self.push_type(Type::Unknown);
                self.globals
                    .insert((ctx.namespace, name.name.clone()), Name::Type(blob_ty));
                let mut resolved_fields = BTreeMap::new();
                let mut type_params = Vec::new();
                let mut seen = HashMap::new();
                for v in variables.iter() {
                    let ty = self.push_type(Type::Unknown);
                    type_params.push(ty);
                    seen.insert(v.name.clone(), ty);
                }
                let num_vars = seen.len();
                for (k, t) in fields.iter() {
                    resolved_fields.insert(
                        k.name.clone(),
                        (k.span, self.inner_resolve_type(span, ctx, t, &mut seen)?),
                    );

                    if num_vars != seen.len() {
                        return err_type_error!(
                            self,
                            k.span,
                            TypeError::Exotic,
                            "Unknown generic {}",
                            t
                        )
                        .help(self, span, "While defining".to_string())
                        .help_no_span(format!(
                            "Generics have the be defined before use, like this: `{} :: blob({})`",
                            name.name, t
                        ));
                    }
                }
                let ty = self.push_type(Type::Blob(name.clone(), resolved_fields, type_params));
                self.unify(span, ctx, ty, blob_ty)?;
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

            StatementKind::Assignment { .. }
            | StatementKind::Loop { .. }
            | StatementKind::Break
            | StatementKind::Continue
            | StatementKind::Ret { .. }
            | StatementKind::Block { .. }
            | StatementKind::StatementExpression { .. }
            | StatementKind::Unreachable
            | StatementKind::EmptyStatement => {
                unreachable!(
                    "Illegal outer statement between lines {} and {} in '{:?}'! Parser should have caught this",
                    span.line_start,
                    span.line_end,
                    self.span_file(&span)
                )
            }
        }
        Ok(())
    }

    fn assignable(&mut self, assignable: &mut Assignable, ctx: TypeCtx) -> TypeResult<RetNValue> {
        let span = assignable.span;
        // FIXME: Functions are copied since they may be specialized
        // several times, this does not work properly when functions are
        // passed to an unknown function parameter.
        let ty = match &mut assignable.kind {
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
                    Some(Name::Type(ty)) => {
                        // NOTE(ed): This allows generics, which is always fun!
                        let ty = *ty;
                        let ty = self.copy(ty);
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
                    Type::Enum(name, variants, _) => (name, variants),
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
                let (ret, expr_ty) = self.expression(value, ctx)?;
                match variants.get(&variant.name) {
                    Some((span, field_ty)) => self.unify(*span, ctx, *field_ty, expr_ty)?,
                    None => {
                        return err_type_error!(
                            self,
                            variant.span,
                            TypeError::UnknownVariant(enum_name.name.clone(), variant.name.clone())
                        )
                        .help(
                            self,
                            enum_name.span,
                            "Defined here".to_string(),
                        )
                    }
                };
                with_ret(ret, ty)
            }

            AssignableKind::Read(ident) => {
                if let Some(var) = self
                    .stack
                    .iter()
                    .rfind(|v| v.ident.name == ident.name)
                    .cloned()
                {
                    no_ret(var.ty)
                } else {
                    match self
                        .globals
                        .get(&(ctx.namespace, ident.name.clone()))
                        .cloned()
                    {
                        Some(Name::Global(var)) => {
                            if ctx.inside_pure && matches!(var.kind, VarKind::Mutable) {
                                err_type_error!(
                                    self,
                                    span,
                                    TypeError::Impurity,
                                    "Cannot access mutable variables from pure functions"
                                )
                            } else {
                                no_ret(var.ty)
                            }
                        }
                        _ => err_type_error!(
                            self,
                            span,
                            TypeError::UnresolvedName(ident.name.clone())
                        ),
                    }
                }
            }

            AssignableKind::Call(f, args) => {
                let (ret, f) = self.assignable(f, ctx)?;
                match self.find_type(f) {
                    Type::Function(params, ret_ty, purity) => {
                        if args.len() != params.len() {
                            return err_type_error!(
                                self,
                                span,
                                TypeError::WrongArity { got: args.len(), expected: params.len() }
                            );
                        }

                        if ctx.inside_pure && !matches!(purity, Purity::Pure) {
                            return err_type_error!(
                                self,
                                span,
                                TypeError::Impurity,
                                "Cannot call impure functions from pure functions"
                            );
                        }

                        // TODO(ed): Annotate the errors?
                        let mut ret = ret;
                        for (a, p) in args.iter_mut().zip(params.iter()) {
                            let span = a.span;
                            let (a_ret, a) = self.expression(a, ctx)?;
                            self.unify(span, ctx, *p, a)?;
                            ret = self.unify_option(span, ctx, ret, a_ret)?;
                        }

                        with_ret(ret, ret_ty)
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
                let mut mapped_assignable =
                    Assignable { span, kind: AssignableKind::Call(f.clone(), args) };
                self.assignable(&mut mapped_assignable, ctx)
            }

            AssignableKind::Access(outer, ident) => match self.namespace_chain(outer, ctx) {
                Some(ctx) => self.assignable(
                    &mut Assignable { span, kind: AssignableKind::Read(ident.clone()) },
                    ctx,
                ),
                None => {
                    let (outer_ret, outer) = self.assignable(outer, ctx)?;
                    let field = self.push_type(Type::Unknown);
                    self.add_constraint(outer, span, Constraint::Field(ident.name.clone(), field));
                    self.check_constraints(span, ctx, outer)?;
                    // TODO(ed): Don't we do this further down? Do we need this code?
                    // We copy functions
                    let field = match self.find_type(outer) {
                        Type::Function(_, _, _) => self.copy(field),
                        _ => field,
                    };
                    with_ret(outer_ret, field)
                }
            },

            AssignableKind::Index(outer, syn_index) => {
                let (outer_ret, outer) = self.assignable(outer, ctx)?;
                let (index_ret, index) = self.expression(syn_index, ctx)?;
                let expr = self.push_type(Type::Unknown);
                match syn_index.kind {
                    ExpressionKind::Int(index) => {
                        self.add_constraint(outer, span, Constraint::ConstantIndex(index, expr));
                    }
                    _ => {
                        self.add_constraint(index, span, Constraint::Indexes(outer));
                        self.add_constraint(outer, span, Constraint::IndexedBy(index));
                        self.add_constraint(outer, span, Constraint::IndexingGives(expr));
                        self.add_constraint(expr, span, Constraint::GivenByIndex(outer));
                    }
                }

                self.check_constraints(span, ctx, outer)?;
                self.check_constraints(span, ctx, index)?;
                let ret = self.unify_option(span, ctx, outer_ret, index_ret)?;
                with_ret(ret, expr)
            }

            AssignableKind::Expression(expression) => self.expression(expression, ctx),
        };
        let (ret, ty) = ty?;
        let ty = match self.find_type(ty) {
            Type::Function(..) => self.copy(ty),
            _ => ty,
        };
        with_ret(ret, ty)
    }

    fn expression_block(
        &mut self,
        span: Span,
        statements: &mut Vec<Statement>,
        ctx: TypeCtx,
    ) -> TypeResult<(Option<TyID>, Option<TyID>)> {
        // Left this for Gustav
        let ss = self.stack.len();
        let mut ret = None;
        for stmt in statements.iter_mut() {
            let stmt_ret = self.statement(stmt, ctx)?;
            ret = self.unify_option(span, ctx, ret, stmt_ret)?;
        }
        // We typecheck the last statement twice sometimes, doesn't matter though.
        let value = if let Some(Statement {
            kind: StatementKind::StatementExpression { value },
            ..
        }) = statements.last_mut()
        {
            let (value_ret, value) = self.expression(value, ctx)?;
            ret = self.unify_option(span, ctx, ret, value_ret)?;
            Some(value)
        } else {
            None
        };
        self.stack.truncate(ss);
        Ok((ret, value))
    }

    fn expression(&mut self, expression: &mut Expression, ctx: TypeCtx) -> TypeResult<RetNValue> {
        let span = expression.span;
        let res = match &mut expression.kind {
            ExpressionKind::Get(ass) => self.assignable(ass, ctx),

            ExpressionKind::Add(a, b) => bin_op!(self, span, ctx, a, b, Constraint::Add),
            ExpressionKind::Sub(a, b) => bin_op!(self, span, ctx, a, b, Constraint::Sub),
            ExpressionKind::Mul(a, b) => bin_op!(self, span, ctx, a, b, Constraint::Mul),
            ExpressionKind::Div(a, b) => {
                let (ret, _) = bin_op!(self, span, ctx, a, b, Constraint::Div)?;
                with_ret(ret, self.push_type(Type::Float))
            }

            ExpressionKind::Comparison(a, comp, b) => match comp {
                ComparisonKind::NotEquals | ComparisonKind::Equals => {
                    let (ret, _) = bin_op!(self, span, ctx, a, b, Constraint::Equ)?;
                    with_ret(ret, self.push_type(Type::Bool))
                }
                ComparisonKind::Less | ComparisonKind::Greater => {
                    let (ret, _) = bin_op!(self, span, ctx, a, b, Constraint::Cmp)?;
                    with_ret(ret, self.push_type(Type::Bool))
                }
                ComparisonKind::LessEqual | ComparisonKind::GreaterEqual => {
                    let (ret, _) = bin_op!(self, span, ctx, a, b, Constraint::CmpEqu)?;
                    with_ret(ret, self.push_type(Type::Bool))
                }

                ComparisonKind::In => {
                    let (a_ret, a) = self.expression(a, ctx)?;
                    let (b_ret, b) = self.expression(b, ctx)?;
                    self.add_constraint(a, span, Constraint::IsContainedIn(b));
                    self.add_constraint(b, span, Constraint::Contains(a));
                    self.check_constraints(span, ctx, a)?;
                    self.check_constraints(span, ctx, b)?;
                    with_ret(
                        self.unify_option(span, ctx, a_ret, b_ret)?,
                        self.push_type(Type::Bool),
                    )
                }
            },

            ExpressionKind::AssertEq(a, b) => {
                let (ret, _) = bin_op!(self, span, ctx, a, b, Constraint::Equ)?;
                with_ret(ret, self.push_type(Type::Bool))
            }

            ExpressionKind::Or(a, b) | ExpressionKind::And(a, b) => {
                let (a_ret, a) = self.expression(a, ctx)?;
                let (b_ret, b) = self.expression(b, ctx)?;
                let boolean = self.push_type(Type::Bool);
                self.unify(span, ctx, a, boolean)?;
                self.unify(span, ctx, b, boolean)?;
                with_ret(self.unify_option(span, ctx, a_ret, b_ret)?, a)
            }

            ExpressionKind::Neg(a) => {
                let (a_ret, a) = self.expression(a, ctx)?;
                self.add_constraint(a, span, Constraint::Neg);
                with_ret(a_ret, a)
            }

            ExpressionKind::Not(a) => {
                let (a_ret, a) = self.expression(a, ctx)?;
                let boolean = self.push_type(Type::Bool);
                with_ret(a_ret, self.unify(span, ctx, a, boolean)?)
            }

            ExpressionKind::Parenthesis(expr) => self.expression(expr, ctx),

            ExpressionKind::Case { to_match, branches, fall_through } => {
                let (ret, to_match) = self.expression(to_match, ctx)?;
                self.add_constraint(to_match, span, Constraint::Enum);

                let mut ret = ret;
                let mut value = None;
                let mut branch_names = BTreeSet::new();
                let ss = self.stack.len();
                for branch in branches.iter_mut() {
                    let name = branch.pattern.name.clone();
                    let constraint = if let Some(var) = &branch.variable {
                        let var = Variable {
                            ident: var.clone(),
                            ty: self.push_type(Type::Unknown),
                            kind: VarKind::Const,
                            span,
                        };
                        let constraint = Some(var.ty);
                        self.stack.push(var);
                        constraint
                    } else {
                        None
                    };
                    self.add_constraint(
                        to_match,
                        span,
                        Constraint::Variant(name.clone(), constraint),
                    );
                    // NOTE(ed): This unifies the variable with the enum, so it injects a function
                    // - for example - this makes it more permissive than if you place it after the
                    // `self.expression_block`.
                    self.check_constraints(span, ctx, to_match)?;
                    let (branch_ret, branch) =
                        self.expression_block(span, &mut branch.body, ctx)?;
                    value = self.unify_option(span, ctx, value, branch)?;
                    ret = self.unify_option(span, ctx, ret, branch_ret)?;
                    self.stack.truncate(ss);
                    branch_names.insert(name.clone());
                }

                if let Some(fall_through) = fall_through {
                    let (fall_ret, fall) = self.expression_block(span, fall_through, ctx)?;
                    ret = self.unify_option(span, ctx, fall_ret, ret)?;
                    value = self.unify_option(span, ctx, fall, value)?;
                } else {
                    self.add_constraint(to_match, span, Constraint::TotalEnum(branch_names));
                    self.check_constraints(span, ctx, to_match)?;
                }
                with_ret(ret, value.unwrap_or_else(|| self.push_type(Type::Void)))
            }

            ExpressionKind::If(branches) => {
                let tys = branches
                    .iter_mut()
                    .map(|branch| {
                        let condition_ret = if let Some(condition) = &mut branch.condition {
                            let span = condition.span;
                            let (ret, condition) = self.expression(condition, ctx)?;
                            let boolean = self.push_type(Type::Bool);
                            self.unify(span, ctx, boolean, condition)?;
                            ret
                        } else {
                            None
                        };
                        let (block_ret, block_value) =
                            self.expression_block(span, &mut branch.body, ctx)?;
                        Ok((
                            span,
                            self.unify_option(span, ctx, condition_ret, block_ret)?,
                            block_value,
                        ))
                    })
                    .collect::<TypeResult<Vec<_>>>()?;

                let mut ret = None;
                let value = if branches
                    .last()
                    .map(|branch| branch.condition.is_some())
                    .unwrap()
                {
                    // There isn't an else branch - so we can fall through.
                    let void = self.push_type(Type::Void);
                    Some(void)
                } else {
                    let mut value = None;
                    for (span, branch_ret, branch_value) in tys.iter() {
                        // TODO(ed): These are bad errors, they're easy to confuse. A better
                        // formulation?
                        ret = self
                            .unify_option(*span, ctx, *branch_ret, ret)
                            .help_no_span(
                                "The return from this block doesn't match the earlier branches"
                                    .into(),
                            )?;
                        value = self
                            .unify_option(*span, ctx, *branch_value, value)
                            .help_no_span(
                                "The value from this block doesn't match the earlier branches"
                                    .into(),
                            )?;
                    }
                    value
                };
                with_ret(ret, value.unwrap_or_else(|| self.push_type(Type::Void)))
            }

            ExpressionKind::Function { name: _, params, ret, body, pure } => {
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

                let returns_something = ret.kind != TypeKind::Resolved(RuntimeType::Void);
                let ret_ty = self.inner_resolve_type(span, ctx, ret, &mut seen)?;

                let ctx = if *pure { ctx.enter_pure() } else { ctx };

                let (actual_ret, implicit_ret) = self.expression_block(span, body, ctx)?;

                let actual_ret = if returns_something {
                    self.unify_option(span, ctx, actual_ret, implicit_ret)
                        .help_no_span("The implicit and explicit return types differ".into())?
                } else {
                    let void = Some(self.push_type(Type::Void));
                    self.unify_option(span, ctx, actual_ret, void)?
                };
                self.unify_option(span, ctx, Some(ret_ty), actual_ret)
                    .help_no_span(
                        "The actual return type and the specified return type differ!".into(),
                    )?;

                if actual_ret.map(|x| self.is_void(x)).unwrap_or(true) && returns_something {
                    return err_type_error!(
                        self,
                        ret.span,
                        TypeError::Exotic,
                        "The return type isn't explicitly set to `void`, but the function doesn't return anything"
                    );
                }

                self.unify_option(span, ctx, Some(ret_ty), actual_ret)
                    .help(
                        self,
                        ret.span,
                        "The actual return type differs from the specified return type".into(),
                    )?;

                self.stack.truncate(ss);

                // Functions are the only expressions that we cannot return out of when evaluating.
                let purity = if *pure { Purity::Pure } else { Purity::Impure };
                let f = self.push_type(Type::Function(args, ret_ty, purity));
                no_ret(f)
            }

            ExpressionKind::Blob { blob, fields } => {
                let blob_ty = self.type_assignable(ctx, blob)?;
                let (blob_name, blob_fields, blob_args) = match self.find_type(blob_ty) {
                    Type::Blob(name, fields, args) => (name, fields, args),
                    _ => {
                        return err_type_error!(
                            self,
                            span,
                            TypeError::Violating(self.bake_type(blob_ty)),
                            "A blob type was expected, but the given type isn't a blob"
                        )
                    }
                };

                let given_fields: BTreeMap<_, _> = fields
                    .iter()
                    .map(|(key, expr)| {
                        Ok((key.clone(), (expr.span, self.push_type(Type::Unknown))))
                    })
                    .collect::<TypeResult<_>>()?;

                let mut errors = Vec::new();
                for (field, _) in blob_fields.iter() {
                    if !given_fields.contains_key(field) {
                        errors.push(type_error!(
                            self,
                            span,
                            TypeError::MissingField {
                                blob: blob_name.name.clone(),
                                field: field.clone(),
                            }
                        ));
                    }
                }

                for (field, (span, _)) in given_fields.iter() {
                    if !blob_fields.contains_key(field) {
                        errors.push(type_error!(
                            self,
                            *span,
                            TypeError::UnknownField {
                                blob: blob_name.name.clone(),
                                field: field.clone(),
                            }
                        ));
                    }
                }

                if !errors.is_empty() {
                    return Err(errors);
                }

                let fields_and_types = given_fields
                    .iter()
                    .map(|(a, (s, x))| (a.clone(), (s.clone(), x.clone())))
                    .collect::<BTreeMap<_, _>>();
                let given_blob = self.push_type(Type::Blob(
                    blob_name.clone(),
                    fields_and_types.clone(),
                    blob_args.clone(),
                ));

                // Unify the fields with their real types
                let ss = self.stack.len();
                let ret = Some(self.push_type(Type::Unknown));
                for (key, expr) in fields {
                    if matches!(expr.kind, ExpressionKind::Function { .. }) {
                        self.stack.push(Variable {
                            ident: Identifier { name: "self".to_string(), span },
                            kind: VarKind::Const,
                            ty: given_blob,
                            span,
                        });
                    }
                    let (inner_ret, expr_ty) = self.expression(expr, ctx)?;
                    self.unify_option(span, ctx, ret, inner_ret)?;
                    self.unify(expr.span, ctx, expr_ty, fields_and_types[key].1)?;
                    self.stack.truncate(ss);
                }

                with_ret(ret, self.unify(span, ctx, given_blob, blob_ty)?)
            }

            ExpressionKind::Tuple(exprs) => {
                let mut tys = Vec::new();
                let ret = Some(self.push_type(Type::Unknown));
                for expr in exprs.iter_mut() {
                    let (inner_ret, ty) = self.expression(expr, ctx)?;
                    tys.push(ty);
                    self.unify_option(span, ctx, ret, inner_ret)?;
                }
                with_ret(ret, self.push_type(Type::Tuple(tys)))
            }

            ExpressionKind::List(exprs) => {
                let inner_ty = self.push_type(Type::Unknown);
                let ret = Some(self.push_type(Type::Unknown));
                for expr in exprs.iter_mut() {
                    let (e_ret, e) = self.expression(expr, ctx)?;
                    self.unify(span, ctx, inner_ty, e)?;
                    self.unify_option(span, ctx, ret, e_ret)?;
                }
                with_ret(ret, self.push_type(Type::List(inner_ty)))
            }

            ExpressionKind::Set(exprs) => {
                let inner_ty = self.push_type(Type::Unknown);
                let ret = Some(self.push_type(Type::Unknown));
                for expr in exprs.iter_mut() {
                    let (e_ret, e) = self.expression(expr, ctx)?;
                    self.unify(span, ctx, inner_ty, e)?;
                    self.unify_option(span, ctx, ret, e_ret)?;
                }
                with_ret(ret, self.push_type(Type::Set(inner_ty)))
            }

            ExpressionKind::Dict(exprs) => {
                let key_ty = self.push_type(Type::Unknown);
                let value_ty = self.push_type(Type::Unknown);
                let ret = Some(self.push_type(Type::Unknown));
                for (i, x) in exprs.iter_mut().enumerate() {
                    let (e_ret, e) = self.expression(x, ctx)?;
                    // Even indexes are keys, odd are the values.
                    let ty = if i % 2 == 0 { key_ty } else { value_ty };
                    self.unify(span, ctx, ty, e)?;
                    self.unify_option(span, ctx, e_ret, ret)?;
                }
                with_ret(ret, self.push_type(Type::Dict(key_ty, value_ty)))
            }

            ExpressionKind::Int(_) => no_ret(self.push_type(Type::Int)),
            ExpressionKind::Float(_) => no_ret(self.push_type(Type::Float)),
            ExpressionKind::Str(_) => no_ret(self.push_type(Type::Str)),
            ExpressionKind::Bool(_) => no_ret(self.push_type(Type::Bool)),
            ExpressionKind::Nil => no_ret(self.push_type(Type::Nil)),
        }?;
        expression.ty = Some(res.1);
        Ok(res)
    }

    fn definition(
        &mut self,
        statement: &mut Statement,
        global: bool,
        ctx: TypeCtx,
    ) -> TypeResult<Option<TyID>> {
        let span = statement.span;
        let (ident, kind, ty, value) = match &mut statement.kind {
            StatementKind::Definition { ident, kind, ty, value } => {
                if ctx.inside_pure && !kind.immutable() {
                    return err_type_error!(
                        self,
                        span,
                        TypeError::Impurity,
                        "Cannot make mutable declarations in pure functions"
                    );
                }
                (ident.clone(), *kind, ty, value)
            }
            _ => unreachable!(),
        };
        let global_name = (ctx.namespace, ident.name.clone());
        let defined_ty = self.resolve_type(span, ctx, &ty)?;
        self.add_constraint(defined_ty, span, Constraint::Variable);

        match &value.kind {
            ExpressionKind::Function { params, pure, .. } => {
                // Special case for functions
                let args = params
                    .iter()
                    .map(|_| self.push_type(Type::Unknown))
                    .collect();
                let ret = self.push_type(Type::Unknown);
                let purity = pure.then(|| Purity::Pure).unwrap_or(Purity::Impure);
                let fn_ty = self.push_type(Type::Function(args, ret, purity));
                self.unify(span, ctx, defined_ty, fn_ty)?;
                let var = Variable { ident, ty: fn_ty, kind, span };
                if global {
                    self.globals.insert(global_name, Name::Global(var));
                } else {
                    self.stack.push(var);
                }

                let (ret_expression, expression_ty) = self.expression(value, ctx)?;
                self.unify(span, ctx, defined_ty, expression_ty)?;
                // Re-check the function body, this catches type-errors from recursion.
                self.expression(value, ctx)?;

                Ok(ret_expression)
            }

            _ => {
                // 'Normal' variables
                let (ret_expression, expression_ty) = self.expression(value, ctx)?;
                self.unify(span, ctx, defined_ty, expression_ty)?;

                let var = Variable { ident, ty: defined_ty, kind, span };
                if global {
                    self.globals.insert(global_name, Name::Global(var));
                } else {
                    self.stack.push(var);
                }

                Ok(ret_expression)
            }
        }
    }

    fn find(&mut self, TyID(a): TyID) -> TyID {
        let mut root = a;
        while let Some(TyID(next)) = self.types[root].parent {
            root = next;
        }

        let mut node = a;
        while let Some(TyID(next)) = self.types[node].parent {
            self.types[node].parent = Some(TyID(root));
            node = next;
        }

        TyID(root)
    }

    fn find_node(&mut self, a: TyID) -> &TypeNode {
        let TyID(ta) = self.find(a);
        &self.types[ta]
    }

    fn find_node_mut(&mut self, a: TyID) -> &mut TypeNode {
        let TyID(ta) = self.find(a);
        &mut self.types[ta]
    }

    fn find_type(&mut self, a: TyID) -> Type {
        self.find_node(a).ty.clone()
    }

    fn is_void(&mut self, a: TyID) -> bool {
        matches!(self.find_type(a), Type::Void)
    }

    fn inner_bake_type(&mut self, a: TyID, seen: &mut HashMap<TyID, RuntimeType>) -> RuntimeType {
        let a = self.find(a);
        if seen.contains_key(&a) {
            return seen[&a].clone();
        }

        seen.insert(a, RuntimeType::Unknown);

        let res = match self.find_type(a) {
            Type::Unknown => RuntimeType::Unknown,
            Type::Ty => RuntimeType::Ty,
            Type::Void => RuntimeType::Void,
            Type::Nil => RuntimeType::Nil,
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
            Type::Function(args, ret, _) => RuntimeType::Function(
                args.iter()
                    .map(|ty| self.inner_bake_type(*ty, seen))
                    .collect(),
                Box::new(self.inner_bake_type(ret, seen)),
            ),
            // TODO(ed): Should we print out the arguments to the blob instead?
            Type::Blob(name, fields, _) => RuntimeType::Blob(
                name.name.clone(),
                fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.inner_bake_type(ty.1, seen)))
                    .collect(),
            ),
            // TODO(ed): Should we print out the arguments to the enum instead?
            Type::Enum(name, variants, _) => RuntimeType::Enum(
                name.name.clone(),
                variants
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.inner_bake_type(ty.1, seen)))
                    .collect(),
            ),

            Type::Invalid => RuntimeType::Invalid,
        };

        seen.insert(a, res.clone());
        res
    }

    fn bake_type(&mut self, a: TyID) -> RuntimeType {
        self.inner_bake_type(a, &mut HashMap::new())
    }

    // This span is wierd - is it weird?
    fn check_constraints(&mut self, span: Span, ctx: TypeCtx, a: TyID) -> TypeResult<()> {
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
                    Type::Blob(blob_name, fields, _) => match fields.get(name) {
                        Some((span, actual_ty)) => {
                            self.unify(*span, ctx, *expected_ty, *actual_ty).map(|_| ())
                        }
                        None => err_type_error!(
                            self,
                            span,
                            TypeError::MissingField {
                                blob: blob_name.name.clone(),
                                field: name.clone(),
                            }
                        ).help(self, blob_name.span, "Defined here".to_string()),
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

                Constraint::Enum => match self.find_type(a) {
                    Type::Unknown | Type::Enum(..) => Ok(()),

                    _ => err_type_error!(
                        self,
                        span,
                        TypeError::Violating(self.bake_type(a)),
                        "Expected this to be an enum"
                    ),
                },

                Constraint::Variant(var, maybe_v_b) => match self.find_type(a) {
                    Type::Unknown => Ok(()),

                    Type::Enum(enum_name, variants, _) => match (variants.get(var), maybe_v_b) {
                        (Some(_), None) => Ok(()),
                        (Some((_, v_a)), Some(v_b)) => self.unify(span, ctx, *v_a, *v_b).map(|_| ()),
                        (None, _) => {
                            err_type_error!(
                                self,
                                span,
                                TypeError::UnknownVariant(enum_name.name, var.clone())
                            ).help(self, enum_name.span, "Defined here".to_string())
                        }
                    },

                    _ => err_type_error!(
                        self,
                        span,
                        TypeError::Violating(self.bake_type(a)),
                        "Expected this to be an enum with a variant '{}'",
                        var
                    ),
                },

                Constraint::TotalEnum(vars) => match self.find_type(a) {
                    Type::Unknown => Ok(()),

                    Type::Enum(enum_name, enum_vars, _) => {
                        let missing = vars
                            .iter()
                            .cloned()
                            .filter(|var| !enum_vars.contains_key(var))
                            .collect::<Vec<_>>();
                        if !missing.is_empty() {
                            err_type_error!(
                                self,
                                span,
                                TypeError::MissingVariants(enum_name.name.clone(), missing)
                            ).help(self, enum_name.span, "Defined here".to_string())
                        } else {
                            let extra = enum_vars
                                .iter()
                                .map(|(var, _)| var.clone())
                                .filter(|var| !vars.contains(var))
                                .collect::<Vec<_>>();
                            if !extra.is_empty() {
                                err_type_error!(
                                    self,
                                    span,
                                    TypeError::ExtraVariants(enum_name.name.clone(), extra)
                                ).help(self, enum_name.span, "Defined here".to_string())
                            } else {
                                Ok(())
                            }
                        }
                    }

                    _ => err_type_error!(
                        self,
                        span,
                        TypeError::Violating(self.bake_type(a)),
                        "Expected this to be an enum with the variants '{:?}'",
                        vars
                    ),
                },

                Constraint::Variable => match self.find_type(a) {
                    Type::Void => err_type_error!(
                        self,
                        span,
                        TypeError::Exotic,
                        "The `void` has no values and cannot be put in a variable"
                    ),

                    _ => Ok(()),
                },
            }
            .help(self, *original_span, "Requirement came from".to_string())?
        }
        Ok(())
    }

    fn union(&mut self, a: TyID, b: TyID) {
        let TyID(a) = self.find(a);
        let TyID(b) = self.find(b);

        if a == b {
            return;
        }

        let (a, b) = if self.types[a].size < self.types[b].size {
            (b, a)
        } else {
            (a, b)
        };

        self.types[b].parent = Some(TyID(a));
        self.types[a].size += self.types[b].size;

        // TODO(ed): Which span should we keep? The one closest to the top? Should we combine them?
        for (con, span) in self.types[b].constraints.clone().iter() {
            self.types[a].constraints.insert(con.clone(), *span);
        }
    }

    fn unify_option(
        &mut self,
        span: Span,
        ctx: TypeCtx,
        a: Option<TyID>,
        b: Option<TyID>,
    ) -> TypeResult<Option<TyID>> {
        Ok(match (a, b) {
            (Some(a), Some(b)) => Some(self.unify(span, ctx, a, b)?),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        })
    }

    fn unify(&mut self, span: Span, ctx: TypeCtx, a: TyID, b: TyID) -> TypeResult<TyID> {
        // TODO(ed): Is this worth doing? Or can we eagerly union types?
        // I tried some and it didn't work great, but I might have missed something.
        let mut seen = BTreeSet::new();
        self.sub_unify(span, ctx, a, b, &mut seen)
    }

    fn sub_unify(
        &mut self,
        span: Span,
        ctx: TypeCtx,
        a: TyID,
        b: TyID,
        seen: &mut BTreeSet<(TyID, TyID)>,
    ) -> TypeResult<TyID> {
        let a = self.find(a);
        let b = self.find(b);

        if a == b || seen.contains(&(a, b)) {
            return Ok(a);
        }

        // Equivalence is symetrical!
        seen.insert((a, b));
        seen.insert((b, a));

        match (self.find_type(a), self.find_type(b)) {
            (_, Type::Unknown) => self.find_node_mut(b).ty = self.find_type(a),
            (Type::Unknown, _) => self.find_node_mut(a).ty = self.find_type(b),

            _ => match (self.find_type(a), self.find_type(b)) {
                (Type::Ty, Type::Ty) => {}
                (Type::Void, Type::Void) => {}
                (Type::Nil, Type::Nil) => {}
                (Type::Int, Type::Int) => {}
                (Type::Float, Type::Float) => {}
                (Type::Bool, Type::Bool) => {}
                (Type::Str, Type::Str) => {}

                (Type::List(a), Type::List(b)) => {
                    self.sub_unify(span, ctx, a, b, seen)
                        .help_no_span("While checking list".into())?;
                }
                (Type::Set(a), Type::Set(b)) => {
                    self.sub_unify(span, ctx, a, b, seen)
                        .help_no_span("While checking set".into())?;
                }
                (Type::Dict(a_k, a_v), Type::Dict(b_k, b_v)) => {
                    self.sub_unify(span, ctx, a_k, b_k, seen)
                        .help_no_span("While checking dictionary key".into())?;
                    self.sub_unify(span, ctx, a_v, b_v, seen)
                        .help_no_span("While checking dictionary value".into())?;
                }

                (Type::Tuple(a), Type::Tuple(b)) => {
                    if a.len() != b.len() {
                        return err_type_error!(
                            self,
                            span,
                            TypeError::TupleLengthMismatch { lhs: a.len(), rhs: b.len() }
                        );
                    }
                    for (i, (a, b)) in a.iter().zip(b.iter()).enumerate() {
                        self.sub_unify(span, ctx, *a, *b, seen)
                            .help_no_span(format!("While checking index #{}", i))?;
                    }
                }

                (
                    Type::Function(a_args, a_ret, a_purity),
                    Type::Function(b_args, b_ret, b_purity),
                ) => {
                    // TODO: Make sure there is one place this is checked.
                    match (a_purity, b_purity) {
                            (Purity::Undefined, _) |
                            (_, Purity::Undefined) |
                            (Purity::Pure, Purity::Pure) |
                            (Purity::Impure, Purity::Impure) => (),
                            (_, _) => return err_type_error!(
                                self,
                                span,
                                TypeError::Impurity,
                                "Cannot use impure function implementations for pure function declarations"
                            ),
                        }
                    if a_args.len() != b_args.len() {
                        return err_type_error!(
                            self,
                            span,
                            TypeError::WrongArity { got: a_args.len(), expected: b_args.len() }
                        );
                    }
                    for (i, (a, b)) in a_args.iter().zip(b_args.iter()).enumerate() {
                        self.sub_unify(span, ctx, *a, *b, seen)
                            .help_no_span(format!("While checking argument #{}", i))?;
                    }
                    self.sub_unify(span, ctx, a_ret, b_ret, seen)
                        .help_no_span("While checking return type".into())?;
                }

                (Type::Blob(a_blob, a_fields, _), Type::Blob(b_blob, b_fields, _)) => {
                    for (a_field, _) in a_fields.iter() {
                        if !b_fields.contains_key(a_field) {
                            return err_type_error!(
                                self,
                                span,
                                TypeError::MissingField {
                                    blob: b_blob.name.clone(),
                                    field: a_field.clone()
                                }
                            ).help(self, b_blob.span, "Defined here".to_string());
                        };
                    }

                    for (b_field, (b_span, b_ty)) in b_fields.iter() {
                        let (_a_span, a_ty) = match a_fields.get(b_field) {
                            Some(b_ty) => *b_ty,
                            None => {
                                return err_type_error!(
                                    self,
                                    span,
                                    TypeError::MissingField {
                                        blob: a_blob.name.clone(),
                                        field: b_field.clone()
                                    }
                                ).help(self, a_blob.span, "Defined here".to_string());
                            }
                        };
                        self.sub_unify(span, ctx, a_ty, *b_ty, seen)
                            .help(self, *b_span, format!("While checking field .{}", b_field))?;
                    }
                }

                (Type::Enum(a_name, a_variants, _), Type::Enum(b_name, b_variants, _)) => {
                    for (a_var, _) in a_variants.iter() {
                        if !b_variants.contains_key(a_var) {
                            return err_type_error!(
                                self,
                                span,
                                TypeError::UnknownVariant(b_name.name.clone(), a_var.clone())
                            ).help(self, b_name.span, "Defined here".to_string());
                        }
                    }
                    for (b_var, (_b_span, b_ty)) in b_variants.iter() {
                        let (a_span, a_ty) = match a_variants.get(b_var) {
                            Some(a_ty) => *a_ty,
                            None => {
                                return err_type_error!(
                                    self,
                                    span,
                                    TypeError::UnknownVariant(a_name.name.clone(), b_var.clone())
                                ).help(self, a_name.span, "Defined here".to_string());
                            }
                        };
                        self.sub_unify(span, ctx, a_ty, *b_ty, seen)
                            .help(self, a_span, format!("While checking variant {}", b_var))?;
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
    fn print_type(&mut self, ty: TyID) {
        let ty = self.find(ty);
        let mut same = BTreeSet::new();
        for i in 0..self.types.len() {
            if self.find(TyID(i)) == ty {
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

    fn inner_copy(&mut self, old_ty: TyID, seen: &mut HashMap<TyID, TyID>) -> TyID {
        let old_ty = self.find(old_ty);

        if let Some(res) = seen.get(&old_ty) {
            return *res;
        }
        let new_ty = self.push_type(Type::Unknown);
        seen.insert(old_ty, new_ty);

        use Constraint as C;
        self.find_node_mut(new_ty).constraints = self
            .find_node(old_ty)
            .constraints
            .clone()
            .iter()
            .map(|(con, span)| {
                (
                    match &con {
                        C::Add(x) => C::Add(self.inner_copy(*x, seen)),
                        C::Sub(x) => C::Sub(self.inner_copy(*x, seen)),
                        C::Mul(x) => C::Mul(self.inner_copy(*x, seen)),
                        C::Div(x) => C::Div(self.inner_copy(*x, seen)),
                        C::Equ(x) => C::Equ(self.inner_copy(*x, seen)),
                        C::Cmp(x) => C::Cmp(self.inner_copy(*x, seen)),
                        C::CmpEqu(x) => C::CmpEqu(self.inner_copy(*x, seen)),
                        C::Neg => C::Neg,
                        C::Indexes(x) => C::Indexes(self.inner_copy(*x, seen)),
                        C::IndexedBy(x) => C::IndexedBy(self.inner_copy(*x, seen)),
                        C::IndexingGives(x) => C::IndexingGives(self.inner_copy(*x, seen)),
                        C::GivenByIndex(x) => C::GivenByIndex(self.inner_copy(*x, seen)),
                        C::ConstantIndex(i, x) => C::ConstantIndex(*i, self.inner_copy(*x, seen)),
                        C::Field(f, x) => C::Field(f.clone(), self.inner_copy(*x, seen)),
                        C::Num => C::Num,
                        C::Container => C::Container,
                        C::SameContainer(x) => C::SameContainer(self.inner_copy(*x, seen)),
                        C::Contains(x) => C::Contains(self.inner_copy(*x, seen)),
                        C::IsContainedIn(x) => C::IsContainedIn(self.inner_copy(*x, seen)),
                        C::Enum => C::Enum,
                        C::Variant(v, x) => {
                            C::Variant(v.clone(), x.map(|y| self.inner_copy(y, seen)))
                        }
                        C::TotalEnum(x) => C::TotalEnum(x.clone()),
                        C::Variable => C::Variable,
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
            | Type::Nil
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

            Type::Function(args, ret, purity) => Type::Function(
                args.iter().map(|ty| self.inner_copy(*ty, seen)).collect(),
                self.inner_copy(ret, seen),
                purity,
            ),

            // TODO(ed): We can cheat here and just copy the table directly.
            Type::Blob(name, fields, args) => Type::Blob(
                name.clone(),
                fields
                    .iter()
                    .map(|(name, (span, ty))| (name.clone(), (*span, self.inner_copy(*ty, seen))))
                    .collect(),
                args.iter().map(|ty| self.inner_copy(*ty, seen)).collect(),
            ),

            Type::Enum(name, variants, args) => Type::Enum(
                name.clone(),
                variants
                    .iter()
                    .map(|(name, (span, ty))| (name.clone(), (*span, self.inner_copy(*ty, seen))))
                    .collect(),
                args.iter().map(|ty| self.inner_copy(*ty, seen)).collect(),
            ),
        };
        new_ty
    }

    fn copy(&mut self, ty: TyID) -> TyID {
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

    fn add_constraint(&mut self, a: TyID, span: Span, constraint: Constraint) {
        self.find_node_mut(a)
            .constraints
            .entry(constraint)
            .or_insert_with(|| span);
    }

    fn add(&mut self, span: Span, ctx: TypeCtx, a: TyID, b: TyID) -> TypeResult<()> {
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

    fn sub(&mut self, span: Span, ctx: TypeCtx, a: TyID, b: TyID) -> TypeResult<()> {
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

    fn mul(&mut self, span: Span, ctx: TypeCtx, a: TyID, b: TyID) -> TypeResult<()> {
        match (self.find_type(a), self.find_type(b)) {
            (Type::Unknown, _) | (_, Type::Unknown) => Ok(()),

            (Type::Float, Type::Float) | (Type::Int, Type::Int) => Ok(()),

            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b.iter()) {
                    self.mul(span, ctx, *a, *b)?;
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

    fn div(&mut self, span: Span, ctx: TypeCtx, a: TyID, b: TyID) -> TypeResult<()> {
        match (self.find_type(a), self.find_type(b)) {
            (Type::Unknown, _) => Ok(()),
            (_, Type::Unknown) => Ok(()),

            (Type::Float | Type::Int, Type::Float | Type::Int) => Ok(()),

            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b.iter()) {
                    self.div(span, ctx, *a, *b)?;
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

    fn equ(&mut self, span: Span, ctx: TypeCtx, a: TyID, b: TyID) -> TypeResult<()> {
        // Equal types all support equality!
        self.unify(span, ctx, a, b).map(|_| ())
    }

    fn cmp(&mut self, span: Span, ctx: TypeCtx, a: TyID, b: TyID) -> TypeResult<()> {
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

    fn is_indexed_by(&mut self, span: Span, ctx: TypeCtx, a: TyID, b: TyID) -> TypeResult<()> {
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
        a: TyID,
        b: TyID,
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
        a: TyID,
        index: i64,
        ret: TyID,
    ) -> TypeResult<()> {
        match self.find_type(a) {
            Type::Unknown => Ok(()),
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
                "This type cannot be indexed with the constant index {}",
                index
            ),
        }
    }

    fn contains(&mut self, span: Span, ctx: TypeCtx, a: TyID, b: TyID) -> TypeResult<()> {
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

    fn solve(&mut self, statements: &mut Vec<(Statement, NamespaceID)>) -> TypeResult<()> {
        // Initialize the namespaces first.
        for (statement, namespace) in statements.iter_mut() {
            if matches!(statement.kind, StatementKind::Use { .. }) {
                self.outer_statement(statement, TypeCtx::namespace(*namespace))?;
            }
        }

        // Then the rest.
        for (statement, namespace) in statements.iter_mut() {
            if !matches!(statement.kind, StatementKind::Use { .. }) {
                self.outer_statement(statement, TypeCtx::namespace(*namespace))?;
            }
        }

        let ctx = TypeCtx::namespace(0);
        match self.globals.get(&(0, "start".to_string())).cloned() {
            Some(Name::Global(var)) => {
                let void = self.push_type(Type::Void);
                let start = self.push_type(Type::Function(Vec::new(), void, Purity::Undefined));
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

    fn span_file(&self, span: &Span) -> FileOrLib {
        self.namespace_to_file[&span.file_id].clone()
    }
}

#[cfg_attr(timed, sylt_macro::timed("typechecker::solve"))]
pub(crate) fn solve(
    statements: &mut Vec<(Statement, NamespaceID)>,
    namespace_to_file: &HashMap<NamespaceID, FileOrLib>,
) -> TypeResult<TypeChecker> {
    let mut tc = TypeChecker::new(namespace_to_file);
    tc.solve(statements)?;
    Ok(tc)
}
