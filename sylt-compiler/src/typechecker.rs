use std::collections::HashMap;
use sylt_common::error::{Error, Helper, TypeError};
use sylt_common::{FileOrLib, TyID, Type as RuntimeType};
use sylt_parser::{Span, TypeConstraint, VarKind};

use crate::name_resolution::{Type as ResolverType, *};
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
    ($self:expr, $span:expr, $ctx:expr, $a:expr, $b:expr, $con:expr, $ret:expr) => {{
        let (ret, _) = bin_op!($self, $span, $ctx, $a, $b, $con)?;
        with_ret(ret, $self.push_type($ret))
    }};
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

pub struct TypeVariable {
    #[allow(unused)]
    pub name: String,
    #[allow(unused)]
    pub id: usize,
    #[allow(unused)]
    pub definition: Span,
    pub is_global: bool,
    pub kind: VarKind,
    pub ty: TyID,
}

pub struct TypeChecker {
    types: Vec<TypeNode>,
    pub variables: Vec<TypeVariable>,
    namespace_to_file: HashMap<NamespaceID, FileOrLib>,
    // TODO(ed): This can probably be removed via some trickery
    pub file_to_namespace: HashMap<FileOrLib, NamespaceID>,
}

#[derive(Clone, Debug, Copy)]
struct TypeCtx {
    inside_loop: bool,
    inside_pure: bool,
}

impl TypeCtx {
    fn new() -> Self {
        Self { inside_loop: false, inside_pure: false }
    }

    fn enter_loop(self) -> Self {
        Self { inside_loop: true, ..self }
    }

    fn enter_pure(self) -> Self {
        Self { inside_pure: true, ..self }
    }
}

impl TypeChecker {
    fn new(variables: &[Var], namespace_to_file: &HashMap<NamespaceID, FileOrLib>) -> Self {
        let mut res = Self {
            types: Vec::new(),
            variables: Vec::new(),
            namespace_to_file: namespace_to_file.clone(),
            file_to_namespace: namespace_to_file
                .iter()
                .map(|(a, b)| (b.clone(), a.clone()))
                .collect(),
        };
        for var in variables {
            let ty = res.push_type(Type::Unknown);
            res.variables.push(TypeVariable {
                name: var.name.clone(),
                id: var.id,
                is_global: var.is_global,
                definition: var.definition,
                kind: var.kind,
                ty,
            })
        }
        res
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

    fn resolve_type(&mut self, ctx: TypeCtx, ty: &ResolverType) -> TypeResult<TyID> {
        self.inner_resolve_type(ctx, ty, &mut HashMap::new())
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
        ctx: TypeCtx,
        ty: &ResolverType,
        seen: &mut HashMap<String, TyID>,
    ) -> TypeResult<TyID> {
        use ResolverType as T;
        let ty = match ty {
            T::Implied(_) => Type::Unknown,

            T::Resolved(ty, _) => match ty {
                RuntimeType::Void => Type::Void,
                RuntimeType::Nil => Type::Nil,
                RuntimeType::Unknown => Type::Unknown,
                RuntimeType::Int => Type::Int,
                RuntimeType::Float => Type::Float,
                RuntimeType::Bool => Type::Bool,
                RuntimeType::String => Type::Str,
                x => unreachable!("Got an unexpected resolved type '{:?}'", x),
            },

            T::UserType(var, vars, span) => {
                let ty = self.variables[*var].ty;
                match self.find_type(ty) {
                    Type::Blob(name, span, _, sub)
                    | Type::ExternBlob(name, span, _, sub, _)
                    | Type::Enum(name, span, _, sub) => {
                        for (i, var) in vars.iter().enumerate() {
                            if sub.len() == i {
                                return err_type_error!(
                                    self,
                                    var.span(),
                                    TypeError::Exotic,
                                    "The type {} takes at most {} type arguments",
                                    name,
                                    sub.len()
                                )
                                .help(
                                    self,
                                    span,
                                    "Defined here".into(),
                                );
                            }
                            let var_ty = self.inner_resolve_type(ctx, var, seen)?;
                            self.unify(span, ctx, var_ty, sub[i])?;
                        }
                    }

                    // NOTE(ed): Is this going to hant me later?
                    // Gives better errors for recursive types - which are illegal.
                    Type::Unknown => {}

                    _ => {
                        return err_type_error!(
                            self,
                            *span,
                            TypeError::Violating(self.bake_type(ty)),
                            "Only enums and blobs can take type-arguments"
                        );
                    }
                }
                return Ok(ty);
            }

            T::Fn { constraints, params, ret, is_pure, span } => {
                let params = params
                    .iter()
                    .map(|t| self.inner_resolve_type(ctx, t, seen))
                    .collect::<TypeResult<Vec<_>>>()?;
                let ret = self.inner_resolve_type(ctx, ret, seen)?;
                for (var, constraints) in constraints.iter() {
                    match seen.get(var) {
                        Some(var) => {
                            // NOTE(ed): This disallowes type-variables that are only used for
                            // constraints.
                            for constraint in constraints.iter() {
                                self.resolve_constraint(*span, *var, constraint, seen)?;
                            }
                        }
                        None => {
                            return err_type_error!(
                                self,
                                *span,
                                TypeError::UnresolvedName(var.clone()),
                                "Unused type-variable. (Only usages in the function signature are counted)"
                            );
                        }
                    }
                }
                let purity = is_pure.then(|| Purity::Pure).unwrap_or(Purity::Undefined);
                Type::Function(params, ret, purity)
            }

            T::Tuple(fields, _) => Type::Tuple(
                fields
                    .iter()
                    .map(|t| self.inner_resolve_type(ctx, t, seen))
                    .collect::<TypeResult<Vec<_>>>()?,
            ),

            T::List(kind, _) => Type::List(self.inner_resolve_type(ctx, kind, seen)?),

            T::Set(kind, _) => Type::Set(self.inner_resolve_type(ctx, kind, seen)?),

            T::Dict(key, value, _) => Type::Dict(
                self.inner_resolve_type(ctx, key, seen)?,
                self.inner_resolve_type(ctx, value, seen)?,
            ),

            T::Generic(name, _) => {
                return Ok(*seen
                    .entry(name.clone())
                    .or_insert_with(|| self.push_type(Type::Unknown)))
            }
        };
        Ok(self.push_type(ty))
    }

    fn statement(&mut self, statement: &Statement, ctx: TypeCtx) -> TypeResult<Option<TyID>> {
        use Statement as S;
        let span = statement.span();
        match &statement {
            S::Ret { value: Some(value), span } => Ok(Some({
                let (ret, value) = self.expression(value, ctx)?;
                match ret {
                    Some(ret) => self.unify(*span, ctx, value, ret)?,
                    None => value,
                }
            })),
            S::Ret { value: None, .. } => Ok(Some(self.push_type(Type::Void))),

            S::Block { statements, span } => {
                let (ret, _expr) = self.expression_block(*span, statements, ctx)?;
                Ok(ret)
            }

            S::StatementExpression { value, .. } => Ok(self.expression(&value, ctx)?.0),

            S::Assignment { op, target, value, span } => {
                self.can_assign(*span, target)?;

                if ctx.inside_pure {
                    return err_type_error!(
                        self,
                        *span,
                        TypeError::Exotic,
                        "Cannot make assignments in pure functions"
                    );
                }

                let (expression_ret, expression_ty) = self.expression(&value, ctx)?;
                let (target_ret, target_ty) = self.expression(&target, ctx)?;
                match op {
                    BinOp::And
                    | BinOp::AssertEq
                    | BinOp::Equals
                    | BinOp::Greater
                    | BinOp::GreaterEqual
                    | BinOp::In
                    | BinOp::Less
                    | BinOp::LessEqual
                    | BinOp::NotEquals
                    | BinOp::Or => {}

                    BinOp::Nop => {}
                    BinOp::Add => {
                        self.add_constraint(expression_ty, *span, Constraint::Add(target_ty));
                        self.add_constraint(target_ty, *span, Constraint::Add(expression_ty));
                    }
                    BinOp::Sub => {
                        self.add_constraint(expression_ty, *span, Constraint::Sub(target_ty));
                        self.add_constraint(target_ty, *span, Constraint::Sub(expression_ty));
                    }
                    BinOp::Mul => {
                        self.add_constraint(expression_ty, *span, Constraint::Mul(target_ty));
                        self.add_constraint(target_ty, *span, Constraint::Mul(expression_ty));
                    }
                    BinOp::Div => {
                        let float_ty = self.push_type(Type::Float);
                        self.unify(*span, ctx, target_ty, float_ty)?;
                        self.add_constraint(expression_ty, *span, Constraint::Div(target_ty));
                        self.add_constraint(target_ty, *span, Constraint::Div(expression_ty));
                    }
                };
                self.unify(*span, ctx, expression_ty, target_ty)?;
                self.unify_option(*span, ctx, expression_ret, target_ret)
            }

            S::Definition { var, ty, span, value, .. } => {
                let ty = self.resolve_type(ctx, ty)?;
                let (value_ret, value) = self.expression(&value, ctx)?;
                self.unify(*span, ctx, self.variables[*var].ty, ty)?;
                self.unify(*span, ctx, self.variables[*var].ty, value)?;
                Ok(value_ret)
            }

            S::Loop { condition, body, span } => {
                let (ret, condition) = self.expression(&condition, ctx)?;
                let boolean = self.push_type(Type::Bool);
                self.unify(*span, ctx, boolean, condition)?;

                let (body_ret, _) = self.expression_block(*span, &body, ctx.enter_loop())?;
                self.unify_option(*span, ctx, ret, body_ret)
            }

            S::Break(span) => {
                if !ctx.inside_loop {
                    err_type_error!(
                        self,
                        *span,
                        TypeError::Exotic,
                        "`break` only works in loops"
                    )
                } else {
                    Ok(None)
                }
            }
            S::Continue(span) => {
                if !ctx.inside_loop {
                    err_type_error!(
                        self,
                        *span,
                        TypeError::Exotic,
                        "`continue` only works in loops"
                    )
                } else {
                    Ok(None)
                }
            }

            S::Unreachable(_) => Ok(None),

            S::Blob { .. } | S::Enum { .. } | S::ExternalDefinition { .. } => {
                unreachable!(
                    "Illegal inner statement at {:?}! Parser should have caught this",
                    span
                )
            }
        }
    }

    fn outer_statement(&mut self, statement: &Statement, ctx: TypeCtx) -> TypeResult<()> {
        use Statement as S;
        match &statement {
            S::Enum { name, var, span, variants, variables } => {
                let enum_ty = self.variables[*var].ty;
                let mut resolved_variants = BTreeMap::new();
                let mut type_params = Vec::new();
                let mut seen = HashMap::new();
                for v in variables.iter() {
                    let ty = self.push_type(Type::Unknown);
                    type_params.push(ty);
                    seen.insert(v.clone(), ty);
                }
                let num_vars = seen.len();
                for (k, (k_span, t)) in variants.iter() {
                    resolved_variants.insert(
                        k.clone(),
                        (*k_span, self.inner_resolve_type(ctx, t, &mut seen)?),
                    );

                    if num_vars != seen.len() {
                        return err_type_error!(
                            self,
                            *k_span,
                            TypeError::Exotic,
                            "Unknown generic {:?}",
                            t
                        )
                        .help(self, *span, "While defining".to_string())
                        .help_no_span(format!(
                            "Generics have the be defined before use, like this: `{} :: enum({:?})`",
                            name, t
                        ));
                    }
                }
                let ty = self.push_type(Type::Enum(
                    name.clone(),
                    *span,
                    resolved_variants,
                    type_params,
                ));
                self.unify(*span, ctx, ty, enum_ty)?;
            }

            S::Blob { name, var, fields, variables, external, span } => {
                let blob_ty = self.variables[*var].ty;
                let mut resolved_fields = BTreeMap::new();
                let mut type_params = Vec::new();
                let mut seen = HashMap::new();
                for v in variables.iter() {
                    let ty = self.push_type(Type::Unknown);
                    type_params.push(ty);
                    seen.insert(v.clone(), ty);
                }
                let num_vars = seen.len();
                for (k, (k_span, t)) in fields.iter() {
                    resolved_fields.insert(
                        k.clone(),
                        (*k_span, self.inner_resolve_type(ctx, t, &mut seen)?),
                    );

                    if num_vars != seen.len() {
                        return err_type_error!(
                            self,
                            *k_span,
                            TypeError::Exotic,
                            "Unknown generic {:?}",
                            t
                        )
                        .help(self, *span, "While defining".to_string())
                        .help_no_span(format!(
                            "Generics have the be defined before use, like this: `{} :: blob({:?})`",
                            name, t
                        ));
                    }
                }
                let ty = self.push_type(match external {
                    true => Type::ExternBlob(
                        name.clone(),
                        *span,
                        resolved_fields,
                        type_params,
                        *var,
                    ),
                    false => Type::Blob(name.clone(), *span, resolved_fields, type_params),
                });
                self.unify(*span, ctx, ty, blob_ty)?;
            }

            S::Definition { var, ty, span, value, .. } => {
                let ty = self.resolve_type(ctx, ty)?;
                // TODO(ed): Make sure the option is void or none - you cannot return otherwise.
                // But this might be caught somewhere else?
                let (_, value) = self.expression(value, ctx)?;
                self.unify(*span, ctx, self.variables[*var].ty, ty)?;
                self.unify(*span, ctx, self.variables[*var].ty, value)?;
            }

            S::ExternalDefinition { var, ty, span, .. } => {
                let ty = self.resolve_type(ctx, ty)?;
                self.unify(*span, ctx, self.variables[*var].ty, ty)?;
            }

            S::Assignment { .. }
            | S::Loop { .. }
            | S::Break(..)
            | S::Continue(..)
            | S::Ret { .. }
            | S::Block { .. }
            | S::StatementExpression { .. }
            | S::Unreachable(..) => {
                let span = statement.span();
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

    fn expression_block(
        &mut self,
        span: Span,
        statements: &Vec<Statement>,
        ctx: TypeCtx,
    ) -> TypeResult<(Option<TyID>, Option<TyID>)> {
        // Left this for Gustav
        let mut ret = None;
        for stmt in statements.iter() {
            let stmt_ret = self.statement(stmt, ctx)?;
            ret = self.unify_option(span, ctx, ret, stmt_ret)?;
        }
        // We typecheck the last statement twice sometimes, doesn't matter though.
        let value =
            if let Some(Statement::StatementExpression { value, .. }) = statements.last() {
                let (value_ret, value) = self.expression(value, ctx)?;
                ret = self.unify_option(span, ctx, ret, value_ret)?;
                Some(value)
            } else {
                None
            };
        Ok((ret, value))
    }

    fn expression(&mut self, expression: &Expression, ctx: TypeCtx) -> TypeResult<RetNValue> {
        use Expression as E;
        let (expr_ret, expr) = match expression {
            E::Read { var, .. } => no_ret(self.variables[*var].ty),
            E::Variant { ty, variant, value, span } => {
                let (value_ret, value) = self.expression(value, ctx)?;
                // TODO[ed]: We should be able to do without this!
                let enum_ty = self.copy(self.variables[*ty].ty);
                self.add_constraint(
                    enum_ty,
                    *span,
                    Constraint::Variant(variant.clone(), Some(value)),
                );
                self.check_constraints(*span, ctx, enum_ty)?;
                with_ret(value_ret, enum_ty)
            }
            E::Call { function, args, span } => {
                let (ret, function) = self.expression(function, ctx)?;
                match self.find_type(function) {
                    Type::Function(params, ret_ty, purity) => {
                        if args.len() != params.len() {
                            return err_type_error!(
                                self,
                                *span,
                                TypeError::WrongArity { got: args.len(), expected: params.len() }
                            );
                        }

                        if ctx.inside_pure && !matches!(purity, Purity::Pure) {
                            return err_type_error!(
                                self,
                                *span,
                                TypeError::Impurity,
                                "Cannot call impure functions from pure functions"
                            );
                        }

                        // TODO(ed): Annotate the errors?
                        let mut ret = ret;
                        for (a, p) in args.iter().zip(params.iter()) {
                            let span = a.span();
                            let (a_ret, a) = self.expression(a, ctx)?;
                            self.unify(span, ctx, *p, a)?;
                            self.add_constraint(a, span, Constraint::Variable);
                            self.check_constraints(span, ctx, a)?;
                            ret = self.unify_option(span, ctx, ret, a_ret)?;
                        }

                        with_ret(ret, ret_ty)
                    }
                    Type::Unknown => err_type_error!(
                        self,
                        *span,
                        TypeError::Violating(self.bake_type(function)),
                        "Unknown types cannot be called"
                    ),
                    _ => err_type_error!(
                        self,
                        *span,
                        TypeError::Violating(self.bake_type(function)),
                        "Not callable"
                    ),
                }
            }
            E::BlobAccess { value, field, span } => {
                let (outer_ret, outer) = self.expression(value, ctx)?;
                let field_ty = self.push_type(Type::Unknown);
                self.add_constraint(outer, *span, Constraint::Field(field.clone(), field_ty));
                self.check_constraints(*span, ctx, outer)?;
                // TODO(ed): Don't we do this further down? Do we need this code?
                // We copy functions
                let field_ty = match self.find_type(outer) {
                    Type::Function(_, _, _) => self.copy(field_ty),
                    _ => field_ty,
                };
                with_ret(outer_ret, field_ty)
            }
            E::Index { value, index: index_syn, span } => {
                let (value_ret, value) = self.expression(value, ctx)?;
                let (index_ret, index) = self.expression(index_syn, ctx)?;
                let expr = self.push_type(Type::Unknown);
                let index_span = index_syn.span();
                match **index_syn {
                    E::Int(i, _) => {
                        self.add_constraint(value, *span, Constraint::ConstantIndex(i, expr));
                    }
                    _ => {
                        self.add_constraint(index, index_span, Constraint::Indexes(value));
                        self.add_constraint(value, index_span, Constraint::IndexedBy(index));
                        self.add_constraint(value, index_span, Constraint::IndexingGives(expr));
                        self.add_constraint(expr, index_span, Constraint::GivenByIndex(value));
                    }
                }
                self.check_constraints(*span, ctx, value)?;
                self.check_constraints(*span, ctx, index)?;
                let ret = self.unify_option(*span, ctx, value_ret, index_ret)?;
                with_ret(ret, expr)
            }

            E::BinOp { a, b, op, span } => match op {
                BinOp::Nop => unreachable!(),
                BinOp::Equals | BinOp::AssertEq | BinOp::NotEquals => {
                    bin_op!(self, *span, ctx, a, b, Constraint::Equ, Type::Bool)
                }
                BinOp::Greater | BinOp::Less => {
                    bin_op!(self, *span, ctx, a, b, Constraint::Cmp, Type::Bool)
                }
                BinOp::GreaterEqual | BinOp::LessEqual => {
                    bin_op!(self, *span, ctx, a, b, Constraint::CmpEqu, Type::Bool)
                }
                BinOp::In => {
                    let (a_ret, a) = self.expression(a, ctx)?;
                    let (b_ret, b) = self.expression(b, ctx)?;
                    self.add_constraint(a, *span, Constraint::IsContainedIn(b));
                    self.add_constraint(b, *span, Constraint::Contains(a));
                    self.check_constraints(*span, ctx, a)?;
                    self.check_constraints(*span, ctx, b)?;
                    with_ret(
                        self.unify_option(*span, ctx, a_ret, b_ret)?,
                        self.push_type(Type::Bool),
                    )
                }
                BinOp::Add => bin_op!(self, *span, ctx, a, b, Constraint::Add),
                BinOp::Sub => bin_op!(self, *span, ctx, a, b, Constraint::Sub),
                BinOp::Mul => bin_op!(self, *span, ctx, a, b, Constraint::Mul),
                BinOp::Div => bin_op!(self, *span, ctx, a, b, Constraint::Mul, Type::Float),
                BinOp::And | BinOp::Or => {
                    let (a_ret, a) = self.expression(a, ctx)?;
                    let (b_ret, b) = self.expression(b, ctx)?;
                    let boolean = self.push_type(Type::Bool);
                    self.unify(*span, ctx, a, boolean)?;
                    self.unify(*span, ctx, b, boolean)?;
                    with_ret(self.unify_option(*span, ctx, a_ret, b_ret)?, a)
                }
            },
            E::UniOp { a, op, span } => match op {
                UniOp::Neg => {
                    let (a_ret, a) = self.expression(a, ctx)?;
                    self.add_constraint(a, *span, Constraint::Neg);
                    with_ret(a_ret, a)
                }
                UniOp::Not => {
                    let (a_ret, a) = self.expression(a, ctx)?;
                    let boolean = self.push_type(Type::Bool);
                    with_ret(a_ret, self.unify(*span, ctx, a, boolean)?)
                }
            },

            E::If { branches, span } => {
                let tys = branches
                    .iter()
                    .map(|branch| {
                        let condition_ret = if let Some(condition) = &branch.condition {
                            let span = condition.span();
                            let (ret, condition) = self.expression(condition, ctx)?;
                            let boolean = self.push_type(Type::Bool);
                            self.unify(span, ctx, boolean, condition)?;
                            ret
                        } else {
                            None
                        };
                        let (block_ret, block_value) =
                            self.expression_block(*span, &branch.body, ctx)?;
                        Ok((
                            span,
                            self.unify_option(*span, ctx, condition_ret, block_ret)?,
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
                            .unify_option(**span, ctx, *branch_ret, ret)
                            .help_no_span(
                                "The return from this block doesn't match the earlier branches"
                                    .into(),
                            )?;
                        value = self
                            .unify_option(**span, ctx, *branch_value, value)
                            .help_no_span(
                                "The value from this block doesn't match the earlier branches"
                                    .into(),
                            )?;
                    }
                    value
                };
                with_ret(ret, value.unwrap_or_else(|| self.push_type(Type::Void)))
            }

            E::Case { to_match, branches, fall_through, span } => {
                let (ret, to_match) = self.expression(to_match, ctx)?;
                self.add_constraint(to_match, *span, Constraint::Enum);

                let mut ret = ret;
                let mut value = None;
                let mut branch_names = BTreeSet::new();
                for branch in branches.iter() {
                    let name = branch.pattern.name.clone();
                    let constraint = &branch.variable.map(|var| self.variables[var].ty);
                    self.add_constraint(
                        to_match,
                        *span,
                        Constraint::Variant(name.clone(), *constraint),
                    );
                    // NOTE(ed): This unifies the variable with the enum, so it injects a function
                    // - for example - this makes it more permissive than if you place it after the
                    // `self.expression_block`.
                    self.check_constraints(*span, ctx, to_match)?;
                    let (branch_ret, branch) = self.expression_block(*span, &branch.body, ctx)?;
                    value = self.unify_option(*span, ctx, value, branch)?;
                    ret = self.unify_option(*span, ctx, ret, branch_ret)?;
                    branch_names.insert(name.clone());
                }

                if let Some(fall_through) = fall_through {
                    let (fall_ret, fall) = self.expression_block(*span, fall_through, ctx)?;
                    ret = self.unify_option(*span, ctx, fall_ret, ret)?;
                    value = self.unify_option(*span, ctx, fall, value)?;
                } else {
                    self.add_constraint(to_match, *span, Constraint::TotalEnum(branch_names));
                    self.check_constraints(*span, ctx, to_match)?;
                }
                with_ret(ret, value.unwrap_or_else(|| self.push_type(Type::Void)))
            }

            E::Function { name: _, params, ret, body, pure, span } => {
                let mut args = Vec::new();
                let mut seen = HashMap::new();
                for (_name, var, span, ty) in params.iter() {
                    let var_ty = self.variables[*var].ty;
                    let ty = self.inner_resolve_type(ctx, ty, &mut seen)?;
                    args.push(self.unify(*span, ctx, var_ty, ty)?);
                }

                let returns_void = ret.is_void();
                let ret_ty = self.inner_resolve_type(ctx, ret, &mut seen)?;

                let ctx = if *pure { ctx.enter_pure() } else { ctx };

                let (actual_ret, implicit_ret) = self.expression_block(*span, body, ctx)?;
                let actual_ret = if returns_void {
                    let void = Some(self.push_type(Type::Void));
                    self.unify_option(*span, ctx, actual_ret, void)?
                } else {
                    self.unify_option(*span, ctx, actual_ret, implicit_ret)
                        .help_no_span("The implicit and explicit return types differ".into())?
                };
                self.unify_option(*span, ctx, Some(ret_ty), actual_ret)
                    .help_no_span(
                        "The actual return type and the specified return type differ!".into(),
                    )?;

                // TODO[ed]: This is wrong.
                if actual_ret.map(|x| !self.is_void(x)).unwrap_or(false) && returns_void {
                    return err_type_error!(
                        self,
                        ret.span(),
                        TypeError::Exotic,
                        "The return type is explicitly set to `void`, but the function returns something"
                    );
                }

                self.unify_option(*span, ctx, Some(ret_ty), actual_ret)
                    .help(
                        self,
                        ret.span(),
                        "The actual return type differs from the specified return type".into(),
                    )?;

                let purity = if *pure { Purity::Pure } else { Purity::Impure };
                let f = self.push_type(Type::Function(args, ret_ty, purity));
                // Functions are the only expressions that we cannot return out of when evaluating.
                no_ret(f)
            }

            E::Blob { blob, fields, span, .. } => {
                let blob_ty = self.variables[*blob].ty;
                let (blob_name, blob_fields, blob_args) = match self.find_type(blob_ty) {
                    Type::Blob(name, _, fields, args) => (name, fields, args),
                    Type::ExternBlob(name, _, _, _, _) => {
                        return err_type_error!(
                            self,
                            *span,
                            TypeError::ExternBlobInstance { name: name.clone() }
                        );
                    }
                    _ => {
                        return err_type_error!(
                            self,
                            *span,
                            TypeError::Violating(self.bake_type(blob_ty)),
                            "A blob type was expected, but the given type isn't a blob"
                        )
                    }
                };

                let given_fields: BTreeMap<_, _> = fields
                    .iter()
                    .map(|(key, expr)| {
                        Ok((key.clone(), (expr.span(), self.push_type(Type::Unknown))))
                    })
                    .collect::<TypeResult<_>>()?;

                let mut errors = Vec::new();
                for (field, _) in blob_fields.iter() {
                    if !given_fields.contains_key(field) {
                        errors.push(type_error!(
                            self,
                            *span,
                            TypeError::MissingField {
                                blob: blob_name.clone(),
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
                                blob: blob_name.clone(),
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
                    *span,
                    fields_and_types.clone(),
                    blob_args.clone(),
                ));

                // Unify the fields with their real types
                let ret = Some(self.push_type(Type::Unknown));
                for (key, expr) in fields {
                    let (inner_ret, expr_ty) = self.expression(expr, ctx)?;
                    self.unify_option(*span, ctx, ret, inner_ret)?;
                    self.unify(expr.span(), ctx, expr_ty, fields_and_types[key].1)?;
                }

                with_ret(ret, self.unify(*span, ctx, given_blob, blob_ty)?)
            }

            E::Collection { collection: Collection::Tuple, values, span } => {
                let mut tys = Vec::new();
                let ret = Some(self.push_type(Type::Unknown));
                for expr in values.iter() {
                    let (inner_ret, ty) = self.expression(expr, ctx)?;
                    tys.push(ty);
                    self.unify_option(*span, ctx, ret, inner_ret)?;
                }
                with_ret(ret, self.push_type(Type::Tuple(tys)))
            }

            E::Collection { collection: Collection::List, values, span } => {
                let inner_ty = self.push_type(Type::Unknown);
                let ret = Some(self.push_type(Type::Unknown));
                for expr in values.iter() {
                    let (e_ret, e) = self.expression(expr, ctx)?;
                    self.unify(*span, ctx, inner_ty, e)?;
                    self.unify_option(*span, ctx, ret, e_ret)?;
                }
                with_ret(ret, self.push_type(Type::List(inner_ty)))
            }

            E::Collection { collection: Collection::Set, values, span } => {
                let inner_ty = self.push_type(Type::Unknown);
                let ret = Some(self.push_type(Type::Unknown));
                for expr in values.iter() {
                    let (e_ret, e) = self.expression(expr, ctx)?;
                    self.unify(*span, ctx, inner_ty, e)?;
                    self.unify_option(*span, ctx, ret, e_ret)?;
                }
                with_ret(ret, self.push_type(Type::Set(inner_ty)))
            }

            E::Collection { collection: Collection::Dict, values, span } => {
                let key_ty = self.push_type(Type::Unknown);
                let value_ty = self.push_type(Type::Unknown);
                let ret = Some(self.push_type(Type::Unknown));
                for (i, x) in values.iter().enumerate() {
                    let (e_ret, e) = self.expression(x, ctx)?;
                    // Even indexes are keys, odd are the values.
                    let ty = if i % 2 == 0 { key_ty } else { value_ty };
                    self.unify(*span, ctx, ty, e)?;
                    self.unify_option(*span, ctx, e_ret, ret)?;
                }
                with_ret(ret, self.push_type(Type::Dict(key_ty, value_ty)))
            }

            E::Float(_, _) => no_ret(self.push_type(Type::Float)),
            E::Int(_, _) => no_ret(self.push_type(Type::Int)),
            E::Str(_, _) => no_ret(self.push_type(Type::Str)),
            E::Bool(_, _) => no_ret(self.push_type(Type::Bool)),
            E::Nil(_) => no_ret(self.push_type(Type::Nil)),
        }?;
        // TODO[ed]: Don't agressively copy function! D:
        match self.find_type(expr) {
            Type::Function { .. } => with_ret(expr_ret, self.copy(expr)),
            _ => with_ret(expr_ret, expr),
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
            Type::Blob(name, _, fields, _) => RuntimeType::Blob(
                name.clone(),
                fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.inner_bake_type(ty.1, seen)))
                    .collect(),
            ),
            // TODO(ed): Should we print out the arguments to the external blob instead?
            Type::ExternBlob(name, span, fields, _, _) => RuntimeType::ExternBlob(
                name.clone(),
                fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.inner_bake_type(ty.1, seen)))
                    .collect(),
                match self.namespace_to_file.get(&span.file_id).unwrap() {
                    FileOrLib::Lib(name) => name.to_string(),
                    FileOrLib::File(path) => path.to_string_lossy().to_string(),
                },
            ),
            // TODO(ed): Should we print out the arguments to the enum instead?
            Type::Enum(name, _, variants, _) => RuntimeType::Enum(
                name.clone(),
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
                    Type::ExternBlob(blob_name, blob_span, fields, _, _)
                    | Type::Blob(blob_name, blob_span, fields, _) => match fields.get(name) {
                        Some((span, actual_ty)) => {
                            self.unify(*span, ctx, *expected_ty, *actual_ty).map(|_| ())
                        }
                        None => err_type_error!(
                            self,
                            span,
                            TypeError::MissingField {
                                blob: blob_name.clone(),
                                field: name.clone(),
                            }
                        )
                        .help(self, blob_span, "Defined here".to_string()),
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

                    Type::Enum(enum_name, enum_span, variants, _) => {
                        match (variants.get(var), maybe_v_b) {
                            (Some(_), None) => Ok(()),
                            (Some((_, v_a)), Some(v_b)) => {
                                self.unify(span, ctx, *v_a, *v_b).map(|_| ())
                            }
                            (None, _) => err_type_error!(
                                self,
                                span,
                                TypeError::UnknownVariant(enum_name, var.clone())
                            )
                            .help(
                                self,
                                enum_span,
                                "Defined here".to_string(),
                            ),
                        }
                    }

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

                    Type::Enum(enum_name, enum_span, enum_vars, _) => {
                        let missing = vars
                            .iter()
                            .cloned()
                            .filter(|var| !enum_vars.contains_key(var))
                            .collect::<Vec<_>>();
                        if !missing.is_empty() {
                            err_type_error!(
                                self,
                                span,
                                TypeError::MissingVariants(enum_name.clone(), missing)
                            )
                            .help(
                                self,
                                enum_span,
                                "Defined here".to_string(),
                            )
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
                                    TypeError::ExtraVariants(enum_name.clone(), extra)
                                )
                                .help(
                                    self,
                                    enum_span,
                                    "Defined here".to_string(),
                                )
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

                (
                    Type::Blob(a_blob, a_span, a_fields, _),
                    Type::Blob(b_blob, b_span, b_fields, _),
                ) => {
                    for (a_field, _) in a_fields.iter() {
                        if !b_fields.contains_key(a_field) {
                            return err_type_error!(
                                self,
                                span,
                                TypeError::MissingField {
                                    blob: b_blob.clone(),
                                    field: a_field.clone()
                                }
                            )
                            .help(
                                self,
                                b_span,
                                "Defined here".to_string(),
                            );
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
                                        blob: a_blob.clone(),
                                        field: b_field.clone()
                                    }
                                )
                                .help(
                                    self,
                                    a_span,
                                    "Defined here".to_string(),
                                );
                            }
                        };
                        self.sub_unify(span, ctx, a_ty, *b_ty, seen).help(
                            self,
                            *b_span,
                            format!("While checking field .{}", b_field),
                        )?;
                    }
                }

                (
                    Type::ExternBlob(_, _, _, a_args, a_id),
                    Type::ExternBlob(_, _, _, b_args, b_id),
                ) if a_id == b_id => {
                    for (i, (a, b)) in a_args.iter().zip(b_args.iter()).enumerate() {
                        self.sub_unify(span, ctx, *a, *b, seen)
                            .help_no_span(format!("While checking type argument #{}", i))?;
                    }
                }

                (
                    Type::Enum(a_name, a_span, a_variants, _),
                    Type::Enum(b_name, b_span, b_variants, _),
                ) => {
                    for (a_var, _) in a_variants.iter() {
                        if !b_variants.contains_key(a_var) {
                            return err_type_error!(
                                self,
                                span,
                                TypeError::UnknownVariant(b_name.clone(), a_var.clone())
                            )
                            .help(
                                self,
                                b_span,
                                "Defined here".to_string(),
                            );
                        }
                    }
                    for (b_var, (_b_span, b_ty)) in b_variants.iter() {
                        let (a_span, a_ty) = match a_variants.get(b_var) {
                            Some(a_ty) => *a_ty,
                            None => {
                                return err_type_error!(
                                    self,
                                    span,
                                    TypeError::UnknownVariant(a_name.clone(), b_var.clone())
                                )
                                .help(
                                    self,
                                    a_span,
                                    "Defined here".to_string(),
                                );
                            }
                        };
                        self.sub_unify(span, ctx, a_ty, *b_ty, seen).help(
                            self,
                            a_span,
                            format!("While checking variant {}", b_var),
                        )?;
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

            Type::ExternBlob(name, span, fields, args, namespace) => Type::ExternBlob(
                name.clone(),
                span,
                fields
                    .iter()
                    .map(|(name, (span, ty))| (name.clone(), (*span, self.inner_copy(*ty, seen))))
                    .collect(),
                args.iter().map(|ty| self.inner_copy(*ty, seen)).collect(),
                namespace,
            ),

            // TODO(ed): We can cheat here and just copy the table directly.
            Type::Blob(name, span, fields, args) => Type::Blob(
                name.clone(),
                span,
                fields
                    .iter()
                    .map(|(name, (span, ty))| (name.clone(), (*span, self.inner_copy(*ty, seen))))
                    .collect(),
                args.iter().map(|ty| self.inner_copy(*ty, seen)).collect(),
            ),

            Type::Enum(name, span, variants, args) => Type::Enum(
                name.clone(),
                span,
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

    fn can_assign(&mut self, span: Span, assignable: &Expression) -> TypeResult<()> {
        use Expression as E;
        match &assignable {
            E::Read { var, span } => {
                if self.variables[*var].kind.immutable() {
                    return err_type_error!(
                        self,
                        *span,
                        TypeError::Assignability,
                        "Cannot assign to constants"
                    );
                }
            }
            E::BlobAccess { .. } | E::Index { .. } => {}

            E::Variant { .. }
            | E::Call { .. }
            | E::BinOp { .. }
            | E::UniOp { .. }
            | E::If { .. }
            | E::Case { .. }
            | E::Function { .. }
            | E::Blob { .. }
            | E::Collection { .. }
            | E::Float(_, _)
            | E::Int(_, _)
            | E::Str(_, _)
            | E::Bool(_, _)
            | E::Nil(_) => {
                return err_type_error!(
                    self,
                    span,
                    TypeError::Assignability,
                    "Can only assign to variables, accesses and indexes"
                );
            }
        }
        Ok(())
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

    fn solve(&mut self, statements: &Vec<Statement>, start_var: Option<&Var>) -> TypeResult<()> {
        let ctx = TypeCtx::new();
        for statement in statements.iter() {
            self.outer_statement(statement, ctx)?;
        }

        match start_var {
            Some(var) => {
                let void = self.push_type(Type::Void);
                let start = self.push_type(Type::Function(Vec::new(), void, Purity::Undefined));
                let ty = self.variables[var.id].ty;
                self.unify(var.definition, ctx, ty, start)
                    .map(|_| ())
                    .or_else(|_| {
                        err_type_error!(
                            self,
                            var.definition,
                            TypeError::Mismatch {
                                got: self.bake_type(ty),
                                expected: self.bake_type(start),
                            },
                            "The start function has the wrong type"
                        )
                    })
            }
            None => {
                // TODO[ed]: Is this unreachable?
                err_type_error!(
                    self,
                    Span::zero(0),
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
    vars: &Vec<Var>,
    statements: &Vec<Statement>,
    namespace_to_file: &HashMap<NamespaceID, FileOrLib>,
) -> TypeResult<TypeChecker> {
    let mut tc = TypeChecker::new(vars, namespace_to_file);
    // TODO(ed): We assume the first global start we find is the start-function.
    // We check that there's a "start" in the main file in `name_resolution`.
    // I hope this is good enough.
    let start = vars.iter().find(|x| &x.name == "start" && x.is_global);
    tc.solve(&statements, start)?;
    Ok(tc)
}
