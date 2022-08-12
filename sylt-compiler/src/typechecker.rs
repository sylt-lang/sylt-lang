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
    ($self:expr, $span:expr, $ctx:expr, $a:expr, $b:expr, $con:expr, $ty_id:expr) => {{
        let (a_ret, a) = $self.expression($a, $ctx)?;
        let (b_ret, b) = $self.expression($b, $ctx)?;
        $self.add_constraint(a, $span, $con(b));
        $self.add_constraint(b, $span, $con(a));
        $self.check_constraints($span, $ctx, a)?;
        $self.check_constraints($span, $ctx, b)?;
        $self.unify($span, $ctx, $ty_id, a)?;
        with_ret($self.unify_option($span, $ctx, a_ret, b_ret)?, a)
    }};
    ($self:expr, $span:expr, $ctx:expr, $a:expr, $b:expr, $con:expr, $ret:expr, $ty_id:expr) => {{
        let no = $self.push_type(Type::Unknown);
        let (ret, _) = bin_op!($self, $span, $ctx, $a, $b, $con, no)?;
        let x = $self.push_type($ret);
        $self.unify($span, $ctx, $ty_id, x)?;
        with_ret(ret, x)
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
/// have the constraint in some way. For example, if some type has the `DivTop` constraint, the
/// divisor type must have the `DivBot` constraint. If this is not the case, the
/// typechecker may miss some constraints when unifying.
///
/// In theory, `Unknown` is the only type that can have a constraint. In practice, concrete types
/// may have constraints since they need to be checked at least once.
#[derive(Clone, Debug, Hash, PartialOrd, Ord, PartialEq, Eq)]
enum Constraint {
    Add(TyID),
    Sub(TyID),
    Mul(TyID),
    DivTop(TyID),
    DivBot(TyID),
    DivRes(TyID),
    Equ(TyID),
    Cmp(TyID),
    CmpEqu(TyID),

    Neg,

    ConstantIndex(i64, TyID),

    Field(String, TyID),

    Num,

    Enum,
    Variant(String, Option<TyID>),
    TotalEnum(BTreeSet<String>),

    Variable,
}

#[derive(Clone, Debug)]
pub struct TypeVariable {
    pub name: String,
    pub id: usize,
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
    fn new(
        variables: &[Var],
        num_types: usize,
        namespace_to_file: &HashMap<NamespaceID, FileOrLib>,
    ) -> Self {
        let mut res = Self {
            types: Vec::new(),
            variables: Vec::new(),
            namespace_to_file: namespace_to_file.clone(),
            file_to_namespace: namespace_to_file
                .iter()
                .map(|(a, b)| (b.clone(), a.clone()))
                .collect(),
        };
        // Assume everything is expressions
        for _id in 0..num_types {
            let _ = res.push_type(Type::Unknown);
        }
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

    pub fn get_variable_type(&self, var: usize) -> &Type {
        &self.find_no_mut(self.variables[var].ty).ty
    }

    pub fn get_type(&self, ty: TyID) -> &Type {
        &self.find_no_mut(ty).ty
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
        let t = self.inner_resolve_type(ctx, ty, &mut HashMap::new())?;
        Ok(t)
    }

    fn resolve_constraint(
        &mut self,
        span: Span,
        var: TyID,
        constraint: &TypeConstraint,
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

        let num_args = constraint.args.len();
        match constraint.name.name.as_str() {
            "Num" => {
                check_constraint_arity(self, span, "Num", num_args, 0)?;
                self.add_constraint(var, span, Constraint::Num);
            }
            "CmpEqu" => {
                check_constraint_arity(self, span, "Num", num_args, 0)?;
                self.add_constraint(var, span, Constraint::CmpEqu(var));
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
                let ty = self.copy(self.variables[*var].ty);
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

                    // NOTE(ed): Is this going to haunt me later?
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
                                self.resolve_constraint(*span, *var, constraint)?;
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

            T::Generic(name, _) => {
                return Ok(*seen
                    .entry(name.clone())
                    .or_insert_with(|| self.push_type(Type::Unknown)))
            }
        };
        Ok(self.push_type(ty))
    }

    // TODO(ed): ctx can be removed in some places? :O
    fn type_from_function(
        &mut self,
        ctx: TypeCtx,
        params: &[(String, usize, Span, ResolverType)],
        ret: &ResolverType,
        pure: bool,
    ) -> TypeResult<(TyID, TyID)> {
        let mut args = Vec::new();
        let mut seen = HashMap::new();
        for (_name, var, span, ty) in params.iter() {
            let var_ty = self.variables[*var].ty;
            let ty = self.inner_resolve_type(ctx, &ty, &mut seen)?;
            args.push(self.unify(*span, ctx, var_ty, ty)?);
        }
        let ret = self.inner_resolve_type(ctx, &ret, &mut seen)?;
        let purity = if pure { Purity::Pure } else { Purity::Impure };
        let f = self.push_type(Type::Function(args, ret, purity));
        Ok((f, ret))
    }

    fn definition(&mut self, statement: &Statement, ctx: TypeCtx) -> TypeResult<Option<TyID>> {
        use Expression as E;
        use Statement as S;
        if let S::Definition { var, ty, value, span, kind, .. } = statement {
            if ctx.inside_pure && !kind.immutable() {
                return err_type_error!(
                    self,
                    *span,
                    TypeError::Impurity,
                    "Cannot make mutable declarations in pure functions"
                );
            }
            let var_ty = self.variables[*var].ty;
            if let E::Function { params, ret, pure, .. } = value {
                let (f_ty, _) = self.type_from_function(ctx, params, ret, *pure)?;
                self.unify(*span, ctx, var_ty, f_ty)?;
            }
            let ty = self.resolve_type(ctx, ty)?;
            self.add_constraint(ty, *span, Constraint::Variable);
            self.unify(*span, ctx, var_ty, ty)?;
            // TODO(ed): Make sure the option is void or none - you cannot return otherwise.
            // But this might be caught somewhere else?
            let (value_ret, value_ty) = self.expression(value, ctx)?;
            self.unify(*span, ctx, var_ty, value_ty)?;
            Ok(value_ret)
        } else {
            unreachable!("Not a definition!");
        }
    }

    fn statement(&mut self, statement: &Statement, ctx: TypeCtx) -> TypeResult<Option<TyID>> {
        use Statement as S;
        let span = statement.span();
        let _handle =
            sylt_macro::timed_handle!("typecheck::statement", line_start = span.line_start);
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
                    BinOp::Div => { /* Very special case below */ }
                };

                if matches!(op, BinOp::Div) {
                    self.add_constraint(expression_ty, *span, Constraint::DivBot(target_ty));
                    self.add_constraint(target_ty, *span, Constraint::DivRes(target_ty));
                    self.add_constraint(target_ty, *span, Constraint::DivTop(expression_ty));
                    self.check_constraints(*span, ctx, expression_ty)?;
                    self.check_constraints(*span, ctx, target_ty)?;
                } else {
                    self.unify(*span, ctx, expression_ty, target_ty)?;
                }
                self.unify_option(*span, ctx, expression_ret, target_ret)
            }

            S::Definition { .. } => self.definition(statement, ctx),

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
        let _handle =
            sylt_macro::timed_handle!("typecheck::outer_statement", line = span.line_start);
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
                    true => {
                        Type::ExternBlob(name.clone(), *span, resolved_fields, type_params, *var)
                    }
                    false => Type::Blob(name.clone(), *span, resolved_fields, type_params),
                });
                self.unify(*span, ctx, ty, blob_ty)?;
            }

            S::Definition { .. } => {
                self.definition(statement, ctx)?;
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

    #[sylt_macro::timed]
    fn expression_block(
        &mut self,
        span: Span,
        statements: &Vec<Statement>,
        ctx: TypeCtx,
    ) -> TypeResult<(Option<TyID>, Option<TyID>)> {
        let mut ret = None;
        for stmt in statements.iter() {
            let stmt_ret = self.statement(stmt, ctx)?;
            ret = self.unify_option(span, ctx, ret, stmt_ret)?;
        }
        // We typecheck the last statement twice sometimes, doesn't matter though.
        let value = if let Some(Statement::StatementExpression { value, .. }) = statements.last() {
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
            E::Read { var, span, .. } | E::ReadUpvalue { var, span, .. } => {
                let var = &self.variables[*var];
                let immutable = var.kind.immutable();
                if ctx.inside_pure && !immutable {
                    return err_type_error!(
                        self,
                        *span,
                        TypeError::Impurity,
                        "Cannot access mutable variables from pure functions"
                    );
                }
                no_ret(var.ty)
            }
            E::Variant { enum_ty, variant, value, span, ty_ } => {
                let (value_ret, value) = self.expression(value, ctx)?;
                // TODO[ed]: We should be able to do without this!
                let enum_ty = self.copy(self.variables[*enum_ty].ty);
                self.add_constraint(
                    enum_ty,
                    *span,
                    Constraint::Variant(variant.clone(), Some(value)),
                );
                self.check_constraints(*span, ctx, enum_ty)?;
                self.unify(*span, ctx, enum_ty, *ty_)?;
                with_ret(value_ret, enum_ty)
            }
            E::Call { function, args, span, ty_id } => {
                let (ret, function) = self.expression(function, ctx)?;
                match self.find_type(function) {
                    Type::Function(params, ret_ty, purity) => {
                        self.unify(*span, ctx, ret_ty, *ty_id)?;
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
                        self.check_constraints(*span, ctx, ret_ty)?;

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
            E::BlobAccess { value, field, span, ty_id: field_ty } => {
                let (outer_ret, outer) = self.expression(value, ctx)?;
                let field_ty = *field_ty;
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
            E::Index { value, index: index_syn, span, ty_id: expr } => {
                let (value_ret, value) = self.expression(value, ctx)?;
                let (index_ret, index) = self.expression(index_syn, ctx)?;
                let int_type = self.push_type(Type::Int);
                self.unify(*span, ctx, index, int_type)?;
                match **index_syn {
                    E::Int { value: i, .. } => {
                        self.add_constraint(value, *span, Constraint::ConstantIndex(i, *expr))
                    }
                    _ => unreachable!("Should be handled in parser"),
                }
                self.check_constraints(*span, ctx, value)?;
                self.check_constraints(*span, ctx, index)?;
                let ret = self.unify_option(*span, ctx, value_ret, index_ret)?;
                with_ret(ret, *expr)
            }

            E::BinOp { a, b, op, span, ty_id } => match op {
                BinOp::Nop => unreachable!(),
                BinOp::Equals | BinOp::AssertEq | BinOp::NotEquals => {
                    bin_op!(self, *span, ctx, a, b, Constraint::Equ, Type::Bool, *ty_id)
                }
                BinOp::Greater | BinOp::Less => {
                    bin_op!(self, *span, ctx, a, b, Constraint::Cmp, Type::Bool, *ty_id)
                }
                BinOp::GreaterEqual | BinOp::LessEqual => {
                    bin_op!(
                        self,
                        *span,
                        ctx,
                        a,
                        b,
                        Constraint::CmpEqu,
                        Type::Bool,
                        *ty_id
                    )
                }
                BinOp::Add => bin_op!(self, *span, ctx, a, b, Constraint::Add, *ty_id),
                BinOp::Sub => bin_op!(self, *span, ctx, a, b, Constraint::Sub, *ty_id),
                BinOp::Mul => bin_op!(self, *span, ctx, a, b, Constraint::Mul, *ty_id),
                BinOp::Div => {
                    let (a_ret, a) = self.expression(a, ctx)?;
                    let (b_ret, b) = self.expression(b, ctx)?;
                    self.add_constraint(a, *span, Constraint::DivTop(b));
                    self.add_constraint(b, *span, Constraint::DivBot(a));
                    let c = *ty_id;
                    self.add_constraint(*ty_id, *span, Constraint::DivRes(a));
                    self.check_constraints(*span, ctx, a)?;
                    self.check_constraints(*span, ctx, b)?;
                    self.check_constraints(*span, ctx, c)?;
                    with_ret(self.unify_option(*span, ctx, a_ret, b_ret)?, c)
                }
                BinOp::And | BinOp::Or => {
                    let (a_ret, a) = self.expression(a, ctx)?;
                    let (b_ret, b) = self.expression(b, ctx)?;
                    let boolean = self.push_type(Type::Bool);
                    self.unify(*span, ctx, *ty_id, boolean)?;
                    self.unify(*span, ctx, a, boolean)?;
                    self.unify(*span, ctx, b, boolean)?;
                    with_ret(self.unify_option(*span, ctx, a_ret, b_ret)?, a)
                }
            },
            E::UniOp { a, op, span, ty_id } => match op {
                UniOp::Neg => {
                    let (a_ret, a) = self.expression(a, ctx)?;
                    self.add_constraint(a, *span, Constraint::Neg);
                    self.unify(*span, ctx, a, *ty_id)?;
                    with_ret(a_ret, a)
                }
                UniOp::Not => {
                    let (a_ret, a) = self.expression(a, ctx)?;
                    let boolean = self.push_type(Type::Bool);
                    self.unify(*span, ctx, a, *ty_id)?;
                    with_ret(a_ret, self.unify(*span, ctx, a, boolean)?)
                }
            },

            E::If { branches, span, ty_id } => {
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
                let value = value.or(ret).unwrap_or_else(|| self.push_type(Type::Void));
                self.unify(*span, ctx, *ty_id, value)?;
                with_ret(ret, value)
            }

            E::Case { to_match, branches, fall_through, span, ty_id } => {
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

                let value = value.or(ret).unwrap_or_else(|| self.push_type(Type::Void));
                self.unify(*span, ctx, *ty_id, value)?;
                with_ret(ret, value)
            }

            E::Function {
                name: _,
                params,
                ret,
                body,
                pure,
                span,
                upvalues: _,
                ty_id,
            } => {
                let (f_ty, ret_ty) = self.type_from_function(ctx, params, ret, *pure)?;
                self.unify(*span, ctx, *ty_id, f_ty)?;

                let ctx = if *pure { ctx.enter_pure() } else { ctx };
                let (actual_ret, implicit_ret) = self.expression_block(*span, body, ctx)?;
                let actual_ret = if ret.is_void() {
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

                if actual_ret.map(|x| self.is_void(x)).unwrap_or(true) && !ret.is_void() {
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

                // Functions are the only expressions that we cannot return out of when evaluating.

                no_ret(f_ty)
            }

            E::Blob { blob, fields, span, ty_id, .. } => {
                let blob_ty = self.copy(self.variables[*blob].ty);
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

                self.unify(*span, ctx, given_blob, blob_ty)?;
                self.unify(*span, ctx, *ty_id, blob_ty)?;
                with_ret(ret, *ty_id)
            }

            E::Collection { collection: Collection::Tuple, values, span, ty_id } => {
                let mut tys = Vec::new();
                let ret = Some(self.push_type(Type::Unknown));
                for expr in values.iter() {
                    let (inner_ret, ty) = self.expression(expr, ctx)?;
                    tys.push(ty);
                    self.unify_option(*span, ctx, ret, inner_ret)?;
                }
                let tuple_ty = self.push_type(Type::Tuple(tys));
                self.unify(*span, ctx, *ty_id, tuple_ty)?;
                with_ret(ret, *ty_id)
            }

            E::Collection {
                collection: Collection::List,
                values,
                span,
                ty_id: inner_ty,
            } => {
                let ret = Some(self.push_type(Type::Unknown));
                for expr in values.iter() {
                    let (e_ret, e) = self.expression(expr, ctx)?;
                    self.unify(*span, ctx, *inner_ty, e)?;
                    self.unify_option(*span, ctx, ret, e_ret)?;
                }
                with_ret(ret, self.push_type(Type::List(*inner_ty)))
            }

            E::Float { .. } => no_ret(self.push_type(Type::Float)),
            E::Int { .. } => no_ret(self.push_type(Type::Int)),
            E::Str { .. } => no_ret(self.push_type(Type::Str)),
            E::Bool { .. } => no_ret(self.push_type(Type::Bool)),
            E::Nil { .. } => no_ret(self.push_type(Type::Nil)),
        }?;
        // TODO[ed]: Don't agressively copy function! D:
        match self.find_type(expr) {
            Type::Function { .. } => with_ret(expr_ret, self.copy(expr)),
            _ => with_ret(expr_ret, expr),
        }
    }

    fn find_no_mut(&self, TyID(a): TyID) -> &TypeNode {
        let mut root = a;
        while let Some(TyID(next)) = self.types[root].parent {
            root = next;
        }

        &self.types[root]
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
                Constraint::DivTop(b) => self.div(span, ctx, a, *b), // NOTE(ed): Arguments are flipped
                Constraint::DivBot(b) => self.div(span, ctx, *b, a), // NOTE(ed): Arguments are flipped
                Constraint::DivRes(b) => self.div_res(span, ctx, *b, a),
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
                        C::DivTop(x) => C::DivTop(self.inner_copy(*x, seen)),
                        C::DivBot(x) => C::DivBot(self.inner_copy(*x, seen)),
                        C::DivRes(x) => C::DivRes(self.inner_copy(*x, seen)),
                        C::Equ(x) => C::Equ(self.inner_copy(*x, seen)),
                        C::Cmp(x) => C::Cmp(self.inner_copy(*x, seen)),
                        C::CmpEqu(x) => C::CmpEqu(self.inner_copy(*x, seen)),
                        C::Neg => C::Neg,
                        C::ConstantIndex(i, x) => C::ConstantIndex(*i, self.inner_copy(*x, seen)),
                        C::Field(f, x) => C::Field(f.clone(), self.inner_copy(*x, seen)),
                        C::Num => C::Num,
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
            E::Read { var, name, span, .. } | E::ReadUpvalue { var, name, span, .. } => {
                if self.variables[*var].kind.immutable() {
                    return err_type_error!(
                        self,
                        *span,
                        TypeError::Assignability,
                        "Cannot assign to constants {:?}",
                        name
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
            | E::Float { .. }
            | E::Int { .. }
            | E::Str { .. }
            | E::Bool { .. }
            | E::Nil { .. } => {
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

            (Type::Tuple(a), Type::Float | Type::Int) => {
                for a in a.iter() {
                    self.div(span, ctx, *a, b)?;
                }
                Ok(())
            }

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

    fn div_res(&mut self, span: Span, ctx: TypeCtx, a: TyID, b: TyID) -> TypeResult<()> {
        match (self.find_type(a), self.find_type(b)) {
            (Type::Float | Type::Int, Type::Float) => Ok(()),

            (Type::Unknown, _) => Ok(()),

            (Type::Float | Type::Int, _) => {
                let float = self.push_type(Type::Float);
                self.unify(span, ctx, b, float)?;
                Ok(())
            }

            (Type::Tuple(xs), Type::Unknown) => {
                let tys = xs.iter().map(|_| self.push_type(Type::Unknown)).collect();
                let tuple = self.push_type(Type::Tuple(tys));
                self.unify(span, ctx, b, tuple)?;
                // Retry with the new info
                self.div_res(span, ctx, a, b)
            }

            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b.iter()) {
                    self.div_res(span, ctx, *a, *b)?;
                }
                Ok(())
            }

            _ => err_type_error!(
                self,
                span,
                TypeError::Exotic,
                "Dividing {} cannot result in {}",
                self.bake_type(a),
                self.bake_type(b)
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
            | (Type::Float, Type::Int)
            | (Type::Str, Type::Str) => Ok(()),

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

            _ => err_type_error!(
                self,
                span,
                TypeError::Violating(self.bake_type(a)),
                "This type cannot be indexed with the constant index {}\n{}",
                index,
                "Only tuples can be indexed like this"
            ),
        }
    }

    #[sylt_macro::timed("typechecker::solve")]
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

pub(crate) fn solve(
    vars: &Vec<Var>,
    num_types: usize,
    statements: &Vec<Statement>,
    namespace_to_file: &HashMap<NamespaceID, FileOrLib>,
) -> TypeResult<TypeChecker> {
    let mut tc = TypeChecker::new(vars, num_types, namespace_to_file);
    // TODO(ed): We assume the first global start we find is the start-function.
    // We check that there's a "start" in the main file in `name_resolution`.
    // I hope this is good enough.
    let start = vars.iter().find(|x| &x.name == "start" && x.is_global);
    tc.solve(&statements, start)?;
    Ok(tc)
}
