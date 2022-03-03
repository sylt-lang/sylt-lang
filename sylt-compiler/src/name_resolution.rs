use std::collections::{hash_map::Entry, HashMap};

use sylt_common::{error::Helper, Error, FileOrLib};
use sylt_parser::{
    expression::CaseBranch as ParserCaseBranch, expression::IfBranch as ParserIfBranch,
    Assignable as ParserAssignable, Expression as ParserExpression, Identifier, Span,
    Statement as ParserStatement, Type as ParserType, TypeAssignable as ParserTypeAssignable,
    VarKind, AST as ParserAST,
};

use crate::NamespaceID;

type ResolveResult<T> = Result<T, Vec<Error>>;
type Ref = usize;

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
                Some(Error::TypeError { helpers, .. }) => {
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
    In,
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
    Set,
    Dict,
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
    pub variable: Option<Identifier>,
    pub body: Vec<Statement>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Read {
        var: Ref,
        span: Span,
    },
    Variant {
        variant: String,
        span: Span,
    },
    Call {
        value: Box<Expression>,
        args: Vec<(Expression, Span)>,
        span: Span,
    },
    BlobAccess {
        value: Box<Expression>,
        field: String,
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
        name: String,
        params: Vec<(String, Span, Type)>,
        ret: Type,

        body: Vec<Statement>,
        pure: bool,

        span: Span,
    },
    Blob {
        blob: Type,
        fields: Vec<(String, Expression)>, // Keep calling order
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

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Noop,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Assignment {
        op: BinOp,
        target: Expression,
        value: Expression,
        span: Span,
    },

    /// Defines a new variable.
    ///
    /// Example: `a := <expression>`.
    ///
    /// Valid definition operators are `::`, `:=` and `: <type> =`.
    Definition {
        ident: Identifier,
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
        ident: Identifier,
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

#[derive(Debug, Clone, PartialEq)]
pub enum TypeAssignable {
    SomeTypeAssignable,
}

#[derive(Debug, Clone, PartialEq)]
struct Var {
    id: Ref,
    definition: Option<Span>,
    kind: VarKind,
    usage: Vec<Span>,
}

#[derive(Debug, Clone, PartialEq)]
enum Name {
    Name(Ref),
    Namespace(FileOrLib, Span),
}

struct Resolver {
    namespaces: HashMap<FileOrLib, HashMap<String, Name>>,
    stack: Vec<(String, Ref)>,
    variables: Vec<Var>,
    namespace_to_file: HashMap<NamespaceID, FileOrLib>,
}

impl Resolver {
    fn new(namespace_to_file: HashMap<NamespaceID, FileOrLib>) -> Self {
        Self {
            namespace_to_file,
            namespaces: HashMap::new(),
            variables: Vec::new(),
            stack: Vec::new(),
        }
    }

    fn span_file(&self, span: &Span) -> FileOrLib {
        self.namespace_to_file[&span.file_id].clone()
    }

    fn add_help(&self, err: Error, span: Span, msg: String) -> Error {
        let wrapper: ResolveResult<()> = Err(vec![err]);
        wrapper.help(self, span, msg).unwrap_err()[0].clone()
    }

    fn ty(&mut self, _: &ParserType) -> ResolveResult<Type> {
        Ok(Type::Noop)
    }

    fn ty_assignable(&mut self, _: &ParserTypeAssignable) -> ResolveResult<Type> {
        panic!();
    }

    fn assignable(&mut self, _: &ParserAssignable) -> ResolveResult<Expression> {
        panic!();
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
        if let Some(var) = &branch.variable {
            self.push_var(var.clone(), VarKind::Const);
        }
        let mut body = Vec::new();
        for stmt in branch.body.iter() {
            match self.statement(stmt)? {
                None => {}
                Some(stmt) => body.push(stmt),
            }
        }
        Ok(CaseBranch {
            pattern: branch.pattern.clone(),
            variable: branch.variable.clone(),
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
                CK::In => self.binop(BinOp::In, a, b, span)?,
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
                let mut params = Vec::new();
                for (n, t) in parser_params.iter() {
                    params.push((n.name.clone(), n.span, self.ty(t)?));
                }
                E::Function {
                    name: name.clone(),
                    params,
                    ret: self.ty(ret)?,
                    body: self.block(body)?,
                    pure: *pure,
                    span,
                }
            }
            EK::Blob { blob, fields: parser_fields } => {
                let blob = self.ty_assignable(blob)?;
                let mut fields = Vec::new();
                for (name, field) in parser_fields.iter() {
                    fields.push((name.clone(), self.expression(field)?));
                }
                E::Blob { blob, fields, span }
            }
            EK::Tuple(values) => self.collection(Collection::Tuple, &values, span)?,
            EK::List(values) => self.collection(Collection::Tuple, &values, span)?,
            EK::Set(values) => self.collection(Collection::Tuple, &values, span)?,
            EK::Dict(values) => self.collection(Collection::Tuple, &values, span)?,
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
            SK::Blob { .. }
            | SK::EmptyStatement
            | SK::Enum { .. }
            | SK::ExternalDefinition { .. }
            | SK::FromUse { .. }
            | SK::Use { .. } => None,

            SK::Definition { ident, kind, ty, value } => {
                let ss = self.stack.len();
                let value = match (
                    matches!(value.kind, sylt_parser::ExpressionKind::Function { .. }),
                    ss == 0,
                ) {
                    (true, true) | (false, true) => {
                        // Outer statement - it's a global so just evaluate the value!
                        self.expression(value)?
                    }
                    (true, false) => {
                        // Function, push the var before!
                        self.push_var(ident.clone(), *kind);
                        self.expression(value)?
                    }
                    (false, false) => {
                        // Value, push the var after!
                        let expr = self.expression(value)?;
                        self.push_var(ident.clone(), *kind);
                        expr
                    }
                };
                let ty = self.ty(ty)?;
                Some(Statement::Definition {
                    span: ident.span,
                    ident: ident.clone(),
                    kind: *kind,
                    ty,
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
                Some(S::Block { statements: self.block(statements)?, span })
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
                    let var = self.new_var(name.span, VarKind::Const);
                    (name.name.clone(), Name::Name(var))
                }

                sylt_parser::StatementKind::ExternalDefinition { ident, kind, .. }
                | sylt_parser::StatementKind::Definition { ident, kind, .. } => {
                    let var = self.new_var(ident.span, *kind);
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
                        Name::Name(r) => self.variables[*r].definition.unwrap(),
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

    fn new_var(&mut self, definition: Span, kind: VarKind) -> Ref {
        let id = self.variables.len();

        self.variables.push(Var {
            id,
            definition: Some(definition),
            kind,
            usage: Vec::new(),
        });
        id
    }

    fn define_variable(&mut self, file_or_lib: &FileOrLib, ident: Identifier, name: Name) {
        self.namespaces
            .get_mut(file_or_lib)
            .map(|x| x.insert(ident.name, name));
    }

    fn push_var(&mut self, ident: Identifier, kind: VarKind) {
        let var = self.new_var(ident.span, kind);
        self.stack.push((ident.name, var));
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
                                Name::Name(r) => self.variables[*r].definition.unwrap(),
                                Name::Namespace(_, span) => *span,
                            };
                            let err = resolution_error!(
                                self,
                                stmt.span,
                                "Name collision - duplicate definitions of {:?}",
                                name
                            );
                            errs.push(self.add_help(err, span, "First definition is here".into()));
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
                                    Name::Name(r) => self.variables[*r].definition.unwrap(),
                                    Name::Namespace(_, span) => *span,
                                };
                                let err = resolution_error!(
                                    self,
                                    var.span,
                                    "Name collision - duplicate definitions of {:?}",
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
) -> ResolveResult<Vec<Statement>> {
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
            resolver.statement(&stmt)?.map(|x| out.push(x));
        }
    }
    Ok(out)
}
