use std::collections::{hash_map::Entry, HashMap};
use std::collections::{BTreeMap, BTreeSet};
use sylt_common::Type as RuntimeType;
use sylt_common::{error::Helper, Error, FileOrLib};
use sylt_parser::{
    expression::CaseBranch as ParserCaseBranch, expression::IfBranch as ParserIfBranch,
    Assignable as ParserAssignable, Expression as ParserExpression, Identifier, Span,
    Statement as ParserStatement, Type as ParserType, TypeAssignable as ParserTypeAssignable,
    TypeConstraint, VarKind, AST as ParserAST,
};

use crate::NamespaceID;

extern crate levenshtein;
use levenshtein::levenshtein;

type ResolveResult<T> = Result<T, Vec<Error>>;
type Ref = usize;

#[derive(Debug, Copy, Clone, PartialEq, PartialOrd, Ord, Eq)]
pub struct StackFrameId(usize);

macro_rules! raise_resolution_error {
    ($self:expr, $span:expr, $( $msg:expr ),* ) => {
        return Err(vec![
            resolution_error!($self, $span, $( $msg ),*)
        ])
    };
}

macro_rules! resolution_error {
    ($self:expr, $span:expr, $( $msg:expr ),* ) => {
        {
            let message = format!($( $msg ),*);
            Error::CompileError {
                file: $self.span_file(&$span),
                span: $span.clone(),
                message: Some(message),
                helpers: Vec::new(),
            }
        }
    };
}

trait Help {
    fn help(self, resolver: &Resolver, span: Span, message: String) -> Self;
    fn help_no_span(self, message: String) -> Self;
}

impl<T> Help for ResolveResult<T> {
    fn help(mut self, resolver: &Resolver, span: Span, message: String) -> Self {
        match &mut self {
            Ok(_) => {}
            Err(errs) => match &mut errs.last_mut() {
                Some(Error::CompileError { helpers, .. }) => {
                    helpers.push(Helper {
                        at: Some((resolver.span_file(&span), span)),
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
                Some(Error::CompileError { helpers, .. }) => {
                    helpers.push(Helper { at: None, message });
                }
                _ => panic!("Cannot help on this error since the error is empty"),
            },
        }
        self
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum BinOp {
    // For assignment
    Nop,
    // Comp
    Equals,
    NotEquals,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    // Misc
    AssertEq,
    // Mul
    Add,
    Sub,
    Mul,
    Div,
    // Bool
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq)]
pub enum UniOp {
    Neg,
    Not,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Collection {
    Tuple,
    List,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfBranch {
    pub condition: Option<Expression>,
    pub body: Vec<Statement>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CaseBranch {
    pub pattern: Identifier,
    pub variable: Option<Ref>,
    pub body: Vec<Statement>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Read {
        var: Ref,
        name: String,
        span: Span,
    },
    ReadUpvalue {
        var: Ref,
        name: String,
        span: Span,
    },
    Variant {
        ty: Ref,
        variant: String,
        value: Box<Expression>,
        span: Span,
    },
    Call {
        function: Box<Expression>,
        args: Vec<Expression>,
        span: Span,
    },
    BlobAccess {
        value: Box<Expression>,
        field: String,
        span: Span,
    },
    Index {
        value: Box<Expression>,
        index: Box<Expression>,
        span: Span,
    },

    BinOp {
        a: Box<Expression>,
        b: Box<Expression>,
        op: BinOp,
        span: Span,
    },
    UniOp {
        a: Box<Expression>,
        op: UniOp,
        span: Span,
    },

    If {
        branches: Vec<IfBranch>,
        span: Span,
    },
    Case {
        to_match: Box<Expression>,
        branches: Vec<CaseBranch>,
        fall_through: Option<Vec<Statement>>,
        span: Span,
    },
    Function {
        // TODO[et]: We want to know what upvalues we have.
        name: String,
        upvalues: BTreeSet<Ref>,
        params: Vec<(String, Ref, Span, Type)>,
        ret: Type,

        body: Vec<Statement>,
        pure: bool,

        span: Span,
    },
    Blob {
        blob: Ref,
        fields: Vec<(String, Expression)>, // Keep calling order
        self_var: Ref,
        span: Span,
    },

    Collection {
        collection: Collection,
        values: Vec<Expression>,
        span: Span,
    },

    Float(f64, Span),
    Int(i64, Span),
    Str(String, Span),
    Bool(bool, Span),
    Nil(Span),
}

impl Expression {
    pub fn span(&self) -> Span {
        match self {
            Expression::Read { span, .. }
            | Expression::ReadUpvalue { span, .. }
            | Expression::Variant { span, .. }
            | Expression::Call { span, .. }
            | Expression::BlobAccess { span, .. }
            | Expression::Index { span, .. }
            | Expression::BinOp { span, .. }
            | Expression::UniOp { span, .. }
            | Expression::If { span, .. }
            | Expression::Case { span, .. }
            | Expression::Function { span, .. }
            | Expression::Blob { span, .. }
            | Expression::Collection { span, .. }
            | Expression::Float(_, span)
            | Expression::Int(_, span)
            | Expression::Str(_, span)
            | Expression::Bool(_, span)
            | Expression::Nil(span) => *span,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    UserType(Ref, Vec<Type>, Span),
    Implied(Span),
    Resolved(RuntimeType, Span),
    Generic(String, Span),
    Tuple(Vec<Type>, Span),
    List(Box<Type>, Span),
    Fn {
        constraints: BTreeMap<String, Vec<TypeConstraint>>,
        params: Vec<Type>,
        ret: Box<Type>,
        is_pure: bool,
        span: Span,
    },
}

impl Type {
    pub fn span(&self) -> Span {
        match self {
            Type::UserType(_, _, span)
            | Type::Implied(span)
            | Type::Resolved(_, span)
            | Type::Generic(_, span)
            | Type::Tuple(_, span)
            | Type::List(_, span)
            | Type::Fn { span, .. } => *span,
        }
    }

    pub fn is_void(&self) -> bool {
        return matches!(self, Type::Resolved(RuntimeType::Void, _));
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Assignment {
        op: BinOp,
        target: Expression,
        value: Expression,
        span: Span,
    },

    Blob {
        name: String,
        var: Ref,
        span: Span,
        variables: Vec<String>,
        fields: HashMap<String, (Span, Type)>,
        external: bool,
    },

    Enum {
        name: String,
        var: Ref,
        span: Span,
        variables: Vec<String>,
        variants: HashMap<String, (Span, Type)>,
    },

    /// Defines a new variable.
    ///
    /// Example: `a := <expression>`.
    ///
    /// Valid definition operators are `::`, `:=` and `: <type> =`.
    Definition {
        name: String,
        var: Ref,
        kind: VarKind,
        ty: Type,
        value: Expression,
        span: Span,
    },

    /// Defines a an external variable - here the type is required.
    ///
    /// Example: `a: int = external`.
    ///
    /// Valid definition operators are `: <type> :`, and `: <type> =`.
    ExternalDefinition {
        name: String,
        var: Ref,
        kind: VarKind,
        ty: Type,
        span: Span,
    },

    /// Do something as long as something else evaluates to true.
    ///
    /// `loop <expression> <statement>`.
    Loop {
        condition: Expression,
        body: Vec<Statement>, // TODO(ed): The parser-statement-loop should have a vector here.
        span: Span,
    },

    /// Jump out of a loop.
    ///
    /// `break`.
    Break(Span),

    /// Go back to the start of the loop.
    ///
    /// `continue`.
    Continue(Span),

    /// Returns a value from a function.
    ///
    /// `ret [<expression>]`.
    Ret {
        value: Option<Expression>,
        span: Span,
    },

    /// Groups together statements that are executed after another.
    ///
    /// `{ <statement>.. }`.
    Block {
        statements: Vec<Statement>,
        span: Span,
    },

    /// A free-standing expression. It's just a `<expression>`.
    StatementExpression { value: Expression, span: Span },

    /// Throws an error if it is ever evaluated.
    ///
    /// `<!>`.
    Unreachable(Span),
}

impl Statement {
    pub fn span(&self) -> Span {
        match self {
            Statement::Assignment { span, .. }
            | Statement::Blob { span, .. }
            | Statement::Block { span, .. }
            | Statement::Break(span)
            | Statement::Continue(span)
            | Statement::Definition { span, .. }
            | Statement::Enum { span, .. }
            | Statement::ExternalDefinition { span, .. }
            | Statement::Loop { span, .. }
            | Statement::Ret { span, .. }
            | Statement::StatementExpression { span, .. }
            | Statement::Unreachable(span) => *span,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Var {
    pub id: Ref,
    pub name: String,
    pub definition: Span,
    pub kind: VarKind,

    pub captured_by: BTreeSet<StackFrameId>,

    // This flag is only used to check if start is infact global...
    pub is_global: bool,
}

#[derive(Debug, Clone, PartialEq)]
enum Name {
    Name(Ref),
    Namespace(FileOrLib, Span),
}

struct Resolver {
    namespaces: HashMap<FileOrLib, HashMap<String, Name>>,
    stack: Vec<(String, Ref)>,
    stack_frames: Vec<StackFrameId>,

    variables: Vec<Var>,
    namespace_to_file: HashMap<NamespaceID, FileOrLib>,
    file_to_namespace: HashMap<FileOrLib, NamespaceID>,
}

impl Resolver {
    fn new(namespace_to_file: HashMap<NamespaceID, FileOrLib>) -> Self {
        let file_to_namespace = namespace_to_file
            .iter()
            .map(|(a, b)| (b.clone(), a.clone()))
            .collect();
        Self {
            namespace_to_file,
            file_to_namespace,
            namespaces: HashMap::new(),
            variables: Vec::new(),
            stack: Vec::new(),
            stack_frames: Vec::new(),
        }
    }

    fn span_file(&self, span: &Span) -> FileOrLib {
        self.namespace_to_file[&span.file_id].clone()
    }

    fn add_help(&self, err: Error, span: Span, msg: String) -> Error {
        let wrapper: ResolveResult<()> = Err(vec![err]);
        wrapper.help(self, span, msg).unwrap_err()[0].clone()
    }

    fn add_help_no_span(&self, err: Error, msg: String) -> Error {
        let wrapper: ResolveResult<()> = Err(vec![err]);
        wrapper.help_no_span(msg).unwrap_err()[0].clone()
    }

    fn find_similar_name(&self, namespace_id: usize, name: &str) -> Option<(usize, String)> {
        let best_stack = self
            .stack
            .iter()
            .rev()
            .map(|(var_name, _)| (levenshtein(var_name, name), var_name.clone()))
            .min();

        let namespace = &self.namespace_to_file[&namespace_id];
        let best_global = self.namespaces[namespace]
            .keys()
            .map(|var_name| (levenshtein(var_name, name), var_name.clone()))
            .min();

        IntoIterator::into_iter([best_stack, best_global])
            .min()
            .unwrap()
            .clone()
    }

    fn lookup_global(&self, namespace_id: usize, name: &str) -> Option<&Name> {
        let namespace = &self.namespace_to_file[&namespace_id];
        self.namespaces[namespace].get(name)
    }

    fn lookup(&mut self, name: &str, span: Span) -> ResolveResult<Ref> {
        let stack_frame_id = self.stack_frames.last().cloned().unwrap_or(StackFrameId(0));

        for (var_name, var_id) in self.stack.iter().rev() {
            if var_name == name {
                self.variables[*var_id].captured_by.insert(stack_frame_id);
                return Ok(*var_id);
            }
        }

        match self.lookup_global(span.file_id, name).clone() {
            Some(Name::Name(var_id)) => {
                let var_id = *var_id;
                self.variables[var_id].captured_by.insert(stack_frame_id);

                Ok(var_id)
            },
            Some(Name::Namespace(..)) => Err(vec![resolution_error!(
                self,
                span,
                "When resolving the name {:?} - a namespace was found",
                name
            )]),
            None => {
                let err =
                    resolution_error!(self, span, "Failed to resolve {:?} - nothing matched", name);
                let err = match self.find_similar_name(span.file_id, name) {
                    Some((distance, name)) if distance < 8 => {
                        self.add_help_no_span(err, format!("Maybe you ment {:?}?", name))
                    }
                    _ => err,
                };

                Err(vec![err])
            }
        }
    }

    fn namespace_list(&self, namespace_id: usize, assignable: &ParserAssignable) -> Option<usize> {
        use sylt_parser::AssignableKind as AK;
        (match &assignable.kind {
            AK::Read(ident) => match self.lookup_global(namespace_id, &ident.name) {
                Some(Name::Namespace(file_or_lib, _)) => Some(file_or_lib),
                _ => None,
            },
            AK::Access(prev, ident) => {
                match self
                    .namespace_list(namespace_id, prev)
                    .map(|new_namespace| self.lookup_global(new_namespace, &ident.name))
                    .flatten()
                {
                    Some(Name::Namespace(file_or_lib, _)) => Some(file_or_lib),
                    _ => None,
                }
            }
            AK::Index { .. }
            | AK::Variant { .. }
            | AK::Call { .. }
            | AK::ArrowCall { .. }
            | AK::Expression { .. } => None,
        })
        .map(|file_or_lib| self.file_to_namespace.get(file_or_lib).cloned())
        .flatten()
    }

    fn type_vec(&mut self, parser_tys: &[ParserType]) -> ResolveResult<Vec<Type>> {
        let mut tys = Vec::new();
        let mut errs = Vec::new();
        for ty in parser_tys.iter() {
            match self.ty(ty) {
                Err(mut es) => errs.append(&mut es),
                Ok(ty) => tys.push(ty),
            }
        }
        if errs.is_empty() {
            Ok(tys)
        } else {
            Err(errs)
        }
    }

    fn ty(&mut self, ty: &ParserType) -> ResolveResult<Type> {
        use sylt_parser::TypeKind as TK;
        use Type as T;
        let span = ty.span;
        Ok(match &ty.kind {
            TK::Implied => T::Implied(span),
            TK::Resolved(t) => T::Resolved(t.clone(), span),
            TK::UserDefined(t, gs) => {
                let r = match self.ty_assignable(t)? {
                    T::UserType(r, _, _) => r,
                    _ => raise_resolution_error! {
                        self,
                        span,
                        "This is not a reference to a user defined type"
                    },
                };
                let gs = self.type_vec(gs)?;
                T::UserType(r, gs, span)
            }
            TK::Fn { constraints, params, ret, is_pure } => T::Fn {
                is_pure: *is_pure,
                span,
                constraints: constraints.clone(),
                params: self.type_vec(params)?,
                ret: Box::new(self.ty(ret)?),
            },
            TK::Tuple(gs) => T::Tuple(self.type_vec(gs)?, span),
            TK::List(t) => T::List(Box::new(self.ty(t)?), span),
            TK::Generic(name) => T::Generic(name.clone(), span),
            TK::Grouping(t) => self.ty(t)?,
        })
    }

    fn namespace_type_list(
        &self,
        namespace_id: NamespaceID,
        ty_ass: &ParserTypeAssignable,
    ) -> ResolveResult<NamespaceID> {
        use sylt_parser::TypeAssignableKind as TAK;
        let (maybe_name, ident) = match &ty_ass.kind {
            TAK::Read(ident) => (self.lookup_global(namespace_id, &ident.name), ident),
            TAK::Access(namespace_list, ty) => (
                self.lookup_global(
                    self.namespace_type_list(namespace_id, &namespace_list)?,
                    &ty.name,
                ),
                ty,
            ),
        };
        Ok(match maybe_name {
            Some(Name::Name(_)) => raise_resolution_error! {
                self,
                ident.span,
                "{:?} is a variable, not a type",
                ident.name
            },
            None => raise_resolution_error! {
                self,
                ident.span,
                "No type named {:?}",
                ident.name
            },
            Some(Name::Namespace(namespace, _)) => *self.file_to_namespace.get(namespace).unwrap(),
        })
    }

    fn ty_assignable(&mut self, ty_ass: &ParserTypeAssignable) -> ResolveResult<Type> {
        use sylt_parser::TypeAssignableKind as TAK;
        let span = ty_ass.span;
        Ok(match &ty_ass.kind {
            TAK::Read(ident) => {
                Type::UserType(self.lookup(&ident.name, ident.span)?, Vec::new(), span)
            }
            TAK::Access(namespace, ty) => {
                let new_namespace = self.namespace_type_list(span.file_id, &namespace)?;
                match self.lookup_global(new_namespace, &ty.name) {
                    Some(Name::Name(r)) => Type::UserType(*r, Vec::new(), span),
                    None => raise_resolution_error! {
                        self,
                        ty.span,
                        "No type named {:?}",
                        ty.name
                    },
                    Some(Name::Namespace(_, _)) => raise_resolution_error! {
                        self,
                        ty.span,
                        "{:?} is a namespace, not a type",
                        ty.name
                    },
                }
            }
        })
    }

    fn assignable(&mut self, assignable: &ParserAssignable) -> ResolveResult<Expression> {
        use sylt_parser::AssignableKind as AK;
        use Expression as E;
        let span = assignable.span;
        Ok(match &assignable.kind {
            AK::Read(Identifier { name, span }) => {
                let var = self.lookup(name, *span)?;
                let span = *span;
                E::Read { var, name: name.clone(), span }
            }
            AK::Variant { enum_ass, variant, value } => {
                // Checking that this is a valid type, should be done in the typechecker
                let ty = if let E::Read { var, .. } = self.assignable(enum_ass)? {
                    var
                } else {
                    raise_resolution_error! {
                        self,
                        span,
                        "This is not ok TODO(ed)"
                    };
                };
                let value = Box::new(self.expression(value)?);
                E::Variant { ty, variant: variant.name.clone(), value, span }
            }
            AK::Call(function, parser_args) => {
                let function = Box::new(self.assignable(function)?);
                let mut args = Vec::new();
                for arg in parser_args.iter() {
                    args.push(self.expression(arg)?);
                }
                E::Call { function, args, span }
            }
            AK::ArrowCall(extra_arg, function, parser_args) => {
                let extra_arg = self.expression(extra_arg)?;
                let function = Box::new(self.assignable(function)?);
                let mut args = vec![extra_arg];
                for arg in parser_args.iter() {
                    args.push(self.expression(arg)?);
                }
                E::Call { function, args, span }
            }
            AK::Access(assignable, ident) => match self.namespace_list(span.file_id, assignable) {
                Some(ns) => {
                    let var = match self.lookup_global(ns, &ident.name) {
                        Some(Name::Name(var)) => *var,
                        Some(Name::Namespace(..)) => {
                            return Err(vec![resolution_error!(
                                self,
                                span,
                                "When resolving the name {:?} - a namespace was found",
                                ident.name
                            )])
                        }
                        None => {
                            return Err(vec![resolution_error!(
                                self,
                                span,
                                "Failed to resolve {:?} - nothing matched",
                                ident.name
                            )])
                        }
                    };
                    let span = ident.span;
                    E::Read { var, name: "access".to_string(), span }
                }
                None => {
                    let value = Box::new(self.assignable(assignable)?);
                    E::BlobAccess { value, field: ident.name.clone(), span: ident.span }
                }
            },
            AK::Index(assignable, index) => {
                let value = Box::new(self.assignable(assignable)?);
                let index = Box::new(self.expression(index)?);
                E::Index { value, index, span }
            }
            AK::Expression(value) => self.expression(value)?,
        })
    }

    fn collection(
        &mut self,
        collection: Collection,
        expr: &[ParserExpression],
        span: Span,
    ) -> ResolveResult<Expression> {
        let mut values = Vec::new();
        for e in expr.iter() {
            values.push(self.expression(e)?);
        }
        Ok(Expression::Collection { collection, values, span })
    }

    fn binop(
        &mut self,
        op: BinOp,
        a: &ParserExpression,
        b: &ParserExpression,
        span: Span,
    ) -> ResolveResult<Expression> {
        let a = Box::new(self.expression(a)?);
        let b = Box::new(self.expression(b)?);
        Ok(Expression::BinOp { op, a, b, span })
    }

    fn uniop(&mut self, op: UniOp, a: &ParserExpression, span: Span) -> ResolveResult<Expression> {
        let a = Box::new(self.expression(a)?);
        Ok(Expression::UniOp { op, a, span })
    }

    fn if_branch(&mut self, branch: &ParserIfBranch) -> ResolveResult<IfBranch> {
        let condition = match &branch.condition {
            Some(cond) => Some(self.expression(&cond)?),
            None => None,
        };
        let body = self.block(&branch.body)?;
        let span = branch.span;
        Ok(IfBranch { condition, body, span })
    }

    fn case_branch(&mut self, branch: &ParserCaseBranch) -> ResolveResult<CaseBranch> {
        let variable = &branch
            .variable
            .as_ref()
            .map(|var| self.push_var(var, VarKind::Const));
        let mut body = Vec::new();
        for stmt in branch.body.iter() {
            match self.statement(stmt)? {
                None => {}
                Some(stmt) => body.push(stmt),
            }
        }
        Ok(CaseBranch {
            pattern: branch.pattern.clone(),
            variable: *variable,
            body,
            span: branch.pattern.span,
        })
    }

    fn block(&mut self, parser_stmts: &[ParserStatement]) -> ResolveResult<Vec<Statement>> {
        let mut stmts = Vec::new();
        let mut errs = Vec::new();
        for stmt in parser_stmts.iter() {
            match self.statement(stmt) {
                Ok(Some(stmt)) => stmts.push(stmt),
                Ok(None) => {}
                Err(mut es) => errs.append(&mut es),
            }
        }
        if errs.is_empty() {
            Ok(stmts)
        } else {
            Err(errs)
        }
    }

    fn expression(&mut self, expr: &ParserExpression) -> ResolveResult<Expression> {
        use sylt_parser::expression::ComparisonKind as CK;
        use sylt_parser::ExpressionKind as EK;
        use Expression as E;
        let span = expr.span;

        Ok(match &expr.kind {
            EK::Get(g) => self.assignable(g)?,
            EK::Add(a, b) => self.binop(BinOp::Add, a, b, span)?,
            EK::Sub(a, b) => self.binop(BinOp::Sub, a, b, span)?,
            EK::Mul(a, b) => self.binop(BinOp::Mul, a, b, span)?,
            EK::Div(a, b) => self.binop(BinOp::Div, a, b, span)?,
            EK::Neg(a) => self.uniop(UniOp::Neg, a, span)?,
            EK::Comparison(a, kind, b) => match kind {
                CK::Equals => self.binop(BinOp::Equals, a, b, span)?,
                CK::NotEquals => self.binop(BinOp::NotEquals, a, b, span)?,
                CK::Greater => self.binop(BinOp::Greater, a, b, span)?,
                CK::GreaterEqual => self.binop(BinOp::GreaterEqual, a, b, span)?,
                CK::Less => self.binop(BinOp::Less, a, b, span)?,
                CK::LessEqual => self.binop(BinOp::LessEqual, a, b, span)?,
            },
            EK::AssertEq(a, b) => self.binop(BinOp::AssertEq, a, b, span)?,
            EK::And(a, b) => self.binop(BinOp::And, a, b, span)?,
            EK::Or(a, b) => self.binop(BinOp::Or, a, b, span)?,
            EK::Not(a) => self.uniop(UniOp::Not, a, span)?,
            EK::Parenthesis(x) => self.expression(x)?,
            EK::If(parser_branches) => {
                let mut branches = Vec::new();
                for branch in parser_branches.iter() {
                    branches.push(self.if_branch(branch)?);
                }
                E::If { branches, span }
            }
            EK::Case { to_match, branches: parser_branches, fall_through } => {
                let to_match = Box::new(self.expression(to_match)?);
                let mut branches = Vec::new();
                for branch in parser_branches.iter() {
                    branches.push(self.case_branch(branch)?);
                }
                let fall_through = match fall_through {
                    Some(x) => Some(self.block(x)?),
                    None => None,
                };
                E::Case { to_match, branches, fall_through, span }
            }
            EK::Function { name, params: parser_params, ret, body, pure } => {
                // Functions are the only things that care about the stackframe
                let ss = self.stack.len();
                let stack_frame_id = StackFrameId(self.stack_frames.len() + 1);
                self.stack_frames.push(stack_frame_id);
                // ------- //
                let name = name.clone();
                let mut params = Vec::new();
                for (n, t) in parser_params.iter() {
                    let var = self.push_var(n, VarKind::Const);
                    params.push((n.name.clone(), var, n.span, self.ty(t)?));
                }
                let ret = self.ty(ret)?;
                let body = self.block(body)?;
                // ------- //

                self.stack_frames.pop();
                self.stack.truncate(ss);
                let upvalues = self
                    .stack
                    .iter()
                    .filter(|(_, id)| self.variables.get(*id).unwrap().captured_by.contains(&stack_frame_id))
                    .map(|(_, id)| id)
                    .cloned()
                    .collect();
                E::Function {
                    name,
                    upvalues,
                    params,
                    ret,
                    body,
                    pure: *pure,
                    span,
                }
            }
            EK::Blob { blob, fields: parser_fields } => {
                let blob = match self.ty_assignable(blob)? {
                    Type::UserType(blob, ..) => blob,
                    _ => unreachable!("Blobs are always userdefined!"),
                };
                let mut fields = Vec::new();
                let self_var = self.new_var(
                    &Identifier { name: "self".to_string(), span },
                    VarKind::Mutable,
                );
                for (name, field) in parser_fields.iter() {
                    let ss = self.stack.len();
                    if matches!(field.kind, EK::Function { .. }) {
                        self.stack.push(("self".to_string(), self_var));
                    }
                    fields.push((name.clone(), self.expression(field)?));
                    self.stack.truncate(ss);
                }
                E::Blob { blob, fields, self_var, span }
            }
            EK::Tuple(values) => self.collection(Collection::Tuple, &values, span)?,
            EK::List(values) => self.collection(Collection::List, &values, span)?,
            EK::Float(f) => E::Float(*f, span),
            EK::Int(i) => E::Int(*i, span),
            EK::Str(s) => E::Str(s.clone(), span),
            EK::Bool(b) => E::Bool(*b, span),
            EK::Nil => E::Nil(span),
        })
    }

    fn statement(&mut self, stmt: &ParserStatement) -> ResolveResult<Option<Statement>> {
        use sylt_parser::StatementKind as SK;
        use Statement as S;
        let span = stmt.span;
        Ok(match &stmt.kind {
            // These are already handled
            SK::EmptyStatement | SK::FromUse { .. } | SK::Use { .. } => None,

            SK::Blob { name, variables, fields, external } => {
                let var = self.lookup(&name.name, span)?;
                Some(S::Blob {
                    name: name.name.clone(),
                    var,
                    span,
                    variables: variables.iter().map(|var| var.name.clone()).collect(),
                    fields: fields
                        .iter()
                        .map(|(field, ty)| Ok((field.name.clone(), (field.span, self.ty(ty)?))))
                        .collect::<ResolveResult<_>>()?,
                    external: *external,
                })
            }
            SK::Enum { name, variables, variants } => {
                let var = self.lookup(&name.name, span)?;
                Some(S::Enum {
                    name: name.name.clone(),
                    var,
                    span,
                    variables: variables.iter().map(|var| var.name.clone()).collect(),
                    variants: variants
                        .iter()
                        .map(|(var, ty)| Ok((var.name.clone(), (var.span, self.ty(ty)?))))
                        .collect::<ResolveResult<_>>()?,
                })
            }

            SK::ExternalDefinition { ident, kind, ty } => Some(S::ExternalDefinition {
                name: ident.name.clone(),
                var: self.lookup(&ident.name, span)?,
                kind: *kind,
                span: ident.span,
                ty: self.ty(ty)?,
            }),

            SK::Definition { ident, kind, ty, value } => {
                let (value, var) = if self.stack.is_empty() {
                    // Outer statement - it's a global so just evaluate the value and push a dummy
                    // value on the stack.
                    let fake_ident = Identifier {
                        name: format!("== STACK BEGIN {:?} ==", ident.name),
                        span: ident.span,
                    };
                    self.push_var(&fake_ident, *kind);
                    let value = self.expression(value)?;
                    // Clear the stack imediately
                    self.stack.clear();
                    let var = self.lookup(&ident.name, span)?;
                    (value, var)
                } else if matches!(value.kind, sylt_parser::ExpressionKind::Function { .. }) {
                    // Function, push the var before!
                    let var = self.push_var(ident, *kind);
                    let value = self.expression(value)?;
                    (value, var)
                } else {
                    // Value, push the var after!
                    let value_maybe = self.expression(value);
                    let var = self.push_var(ident, *kind);
                    (value_maybe?, var)
                };
                Some(S::Definition {
                    span: ident.span,
                    name: ident.name.clone(),
                    var,
                    kind: *kind,
                    ty: self.ty(ty)?,
                    value,
                })
            }

            SK::Assignment { kind, target, value } => {
                use sylt_parser::Op;
                let op = match kind {
                    Op::Nop => BinOp::Nop,
                    Op::Add => BinOp::Add,
                    Op::Sub => BinOp::Sub,
                    Op::Mul => BinOp::Mul,
                    Op::Div => BinOp::Div,
                };
                let value = self.expression(value)?;
                let target = self.assignable(target)?;
                Some(S::Assignment { op, target, value, span })
            }
            SK::Loop { condition, body } => {
                let condition = self.expression(condition)?;
                let body = match self.statement(body)? {
                    Some(body) => vec![body],
                    None => Vec::new(),
                };
                Some(S::Loop { condition, body, span })
            }
            SK::Break => Some(S::Break(span)),
            SK::Continue => Some(S::Continue(span)),
            SK::Ret { value } => Some(S::Ret {
                value: match value {
                    Some(value) => Some(self.expression(value)?),
                    None => None,
                },
                span,
            }),
            SK::Block { statements } => {
                let ss = self.stack.len();
                let statements = self.block(statements)?;
                self.stack.truncate(ss);
                Some(S::Block { statements, span })
            }
            SK::StatementExpression { value } => {
                Some(S::StatementExpression { value: self.expression(value)?, span })
            }
            SK::Unreachable => Some(S::Unreachable(span)),
        })
    }

    fn insert_namespace_and_add_definitions(
        &mut self,
        file_or_lib: &FileOrLib,
        statements: &[ParserStatement],
    ) -> ResolveResult<()> {
        let mut namespace = HashMap::new();
        let mut errs = Vec::new();
        for stmt in statements.iter() {
            let (name, var) = match &stmt.kind {
                sylt_parser::StatementKind::Blob { name, .. }
                | sylt_parser::StatementKind::Enum { name, .. } => {
                    let var = self.new_global(name, VarKind::Const);
                    (name.name.clone(), Name::Name(var))
                }

                sylt_parser::StatementKind::ExternalDefinition { ident, kind, .. }
                | sylt_parser::StatementKind::Definition { ident, kind, .. } => {
                    let var = self.new_global(ident, *kind);
                    (ident.name.clone(), Name::Name(var))
                }

                sylt_parser::StatementKind::Assignment { .. }
                | sylt_parser::StatementKind::Block { .. }
                | sylt_parser::StatementKind::Break
                | sylt_parser::StatementKind::Continue
                | sylt_parser::StatementKind::EmptyStatement
                | sylt_parser::StatementKind::FromUse { .. }
                | sylt_parser::StatementKind::Loop { .. }
                | sylt_parser::StatementKind::Ret { .. }
                | sylt_parser::StatementKind::StatementExpression { .. }
                | sylt_parser::StatementKind::Unreachable
                | sylt_parser::StatementKind::Use { .. } => continue,
            };
            match namespace.entry(name.clone()) {
                Entry::Vacant(ent) => {
                    ent.insert(var);
                }
                Entry::Occupied(old) => {
                    let err = resolution_error!(
                        self,
                        stmt.span,
                        "Name collision - duplicate definitions of the namespace {:?}",
                        name
                    );
                    let span = match old.get() {
                        Name::Name(r) => self.variables[*r].definition,
                        Name::Namespace(_, span) => *span,
                    };
                    let err = self.add_help(err, span, "First definition is here".into());
                    errs.push(err);
                }
            }
        }
        self.namespaces.insert(file_or_lib.clone(), namespace);
        if errs.is_empty() {
            Ok(())
        } else {
            Err(errs)
        }
    }

    fn new_var(&mut self, ident: &Identifier, kind: VarKind) -> Ref {
        let id = self.variables.len();

        self.variables.push(Var {
            id,
            name: ident.name.clone(),
            definition: ident.span,
            kind,

            captured_by: BTreeSet::new(),
            is_global: false,
        });
        id
    }

    fn new_global(&mut self, ident: &Identifier, kind: VarKind) -> Ref {
        let id = self.variables.len();

        self.variables.push(Var {
            id,
            name: ident.name.clone(),
            definition: ident.span,
            kind,

            captured_by: BTreeSet::new(),
            is_global: true,
        });
        id
    }

    fn push_var(&mut self, ident: &Identifier, kind: VarKind) -> usize {
        let var = self.new_var(ident, kind);
        self.stack.push((ident.name.clone(), var));
        var
    }

    fn resolve_global_variables(
        &mut self,
        file_or_lib: &FileOrLib,
        statements: &[ParserStatement],
    ) -> ResolveResult<()> {
        let mut errs = Vec::new();
        for stmt in statements {
            match &stmt.kind {
                sylt_parser::StatementKind::Use { name, file, .. } => {
                    if !self.namespaces.contains_key(file) {
                        errs.push(resolution_error!(
                            self,
                            name.span(),
                            "No namespace named {:?}",
                            file
                        ));
                        continue;
                    };
                    let to_ns = self.namespaces.get_mut(&file_or_lib).unwrap();
                    let to_insert = Name::Namespace(file.clone(), name.span().clone());
                    match to_ns.entry(name.name().to_string()) {
                        Entry::Vacant(ent) => {
                            ent.insert(to_insert);
                        }
                        Entry::Occupied(occ) if occ.get() != &to_insert => {
                            let span = match occ.get() {
                                Name::Name(r) => self.variables[*r].definition,
                                Name::Namespace(_, span) => *span,
                            };
                            let err = resolution_error!(
                                self,
                                stmt.span,
                                "Name collision - duplicate definitions of {:?}",
                                name.name()
                            );
                            let err = self.add_help_no_span(
                                err,
                                format!("Maybe {:?} is already imported?", name.name()),
                            );
                            let err = self.add_help(err, span, "First definition is here".into());
                            errs.push(err);
                        }
                        Entry::Occupied(_) => { /* We allow importing the same thing multiple times */
                        }
                    }
                }
                sylt_parser::StatementKind::FromUse { imports, file, .. } => {
                    for (import_name, import_as) in imports.iter() {
                        let from_ns = match self.namespaces.get(file) {
                            None => {
                                errs.push(resolution_error!(
                                    self,
                                    stmt.span,
                                    "No namespace named {:?}",
                                    file
                                ));
                                continue;
                            }
                            Some(from_ns) => from_ns,
                        };
                        let to_insert = match from_ns.get(&import_name.name) {
                            None => {
                                errs.push(resolution_error!(
                                    self,
                                    import_name.span,
                                    "Cannot find {:?} in namespace {:?}",
                                    import_name.name,
                                    file
                                ));
                                continue;
                            }
                            Some(to_insert) => to_insert,
                        };
                        let to_insert = to_insert.clone();
                        let var = import_as.as_ref().unwrap_or(import_name);
                        let to_ns = self.namespaces.get_mut(&file_or_lib).unwrap();
                        match to_ns.entry(var.name.clone()) {
                            Entry::Vacant(ent) => {
                                ent.insert(to_insert);
                            }
                            Entry::Occupied(occ) if occ.get() != &to_insert => {
                                let span = match occ.get() {
                                    Name::Name(r) => self.variables[*r].definition,
                                    Name::Namespace(_, span) => *span,
                                };
                                let err = resolution_error!(
                                    self,
                                    var.span,
                                    "A Name collision - duplicate definitions of {:?}",
                                    var.name
                                );
                                errs.push(self.add_help(
                                    err,
                                    span,
                                    "First definition is here".into(),
                                ));
                            }
                            Entry::Occupied(_) => { /* We allow importing the same thing multiple times */
                            }
                        }
                    }
                }

                sylt_parser::StatementKind::Assignment { .. }
                | sylt_parser::StatementKind::Blob { .. }
                | sylt_parser::StatementKind::Block { .. }
                | sylt_parser::StatementKind::Break
                | sylt_parser::StatementKind::Continue
                | sylt_parser::StatementKind::Definition { .. }
                | sylt_parser::StatementKind::EmptyStatement
                | sylt_parser::StatementKind::Enum { .. }
                | sylt_parser::StatementKind::ExternalDefinition { .. }
                | sylt_parser::StatementKind::Loop { .. }
                | sylt_parser::StatementKind::Ret { .. }
                | sylt_parser::StatementKind::StatementExpression { .. }
                | sylt_parser::StatementKind::Unreachable => {}
            };
        }
        if errs.is_empty() {
            Ok(())
        } else {
            Err(errs)
        }
    }
}

pub fn resolve<'a>(
    tree: &'a ParserAST,
    namespace_to_file: &HashMap<NamespaceID, FileOrLib>,
) -> ResolveResult<(Vec<Var>, Vec<Statement>)> {
    let mut resolver = Resolver::new(namespace_to_file.clone());

    // Create namespaces and insert the variables in them
    for (file_or_lib, module) in tree.modules.iter() {
        resolver.insert_namespace_and_add_definitions(file_or_lib, &module.statements)?;
    }
    for (file_or_lib, module) in tree.modules.iter() {
        resolver.resolve_global_variables(file_or_lib, &module.statements)?;
    }

    let mut out = Vec::new();
    for (_, module) in tree.modules.iter() {
        for stmt in module.statements.iter() {
            if let Some(resolved) = resolver.statement(&stmt)? {
                out.push(resolved);
            }
        }
    }
    if resolver.lookup_global(0, "start").is_none() {
        raise_resolution_error! {
            resolver,
            Span::zero(0),
            "Expected a start function in the main module - but couldn't find it"
        }
    }
    Ok((resolver.variables, out))
}
