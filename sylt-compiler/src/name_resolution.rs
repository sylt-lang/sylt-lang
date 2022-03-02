use std::collections::{hash_map::Entry, HashMap};

use sylt_common::{error::Helper, Error, FileOrLib};
use sylt_parser::{Identifier, Span, Statement as ParserStatement, VarKind, AST as ParserAST};

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
    NotEquals,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    In,
    Add,
    Sub,
    Mul,
    Div,
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
    },
    Function {
        name: String,
        params: Vec<(String, Span, Type)>,
        ret: Type,

        body: Vec<Statement>,
        pure: bool,
    },
    Blob {
        blob: TypeAssignable,
        fields: Vec<(String, Expression)>, // Keep calling order
    },

    Collection {
        collection: Collection,
        values: Vec<Expression>,
        span: Span,
    },

    Float(f64),
    Int(i64),
    Str(String),
    Bool(bool),
    Nil,
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
        body: Box<Statement>,
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
    variables: Vec<Var>,
    namespace_to_file: HashMap<NamespaceID, FileOrLib>,
}

impl Resolver {
    fn new(namespace_to_file: HashMap<NamespaceID, FileOrLib>) -> Self {
        Self {
            namespace_to_file,
            namespaces: HashMap::new(),
            variables: Vec::new(),
        }
    }

    fn span_file(&self, span: &Span) -> FileOrLib {
        self.namespace_to_file[&span.file_id].clone()
    }

    fn add_help(&self, err: Error, span: Span, msg: String) -> Error {
        let wrapper: ResolveResult<()> = Err(vec![err]);
        wrapper.help(self, span, msg).unwrap_err()[0].clone()
    }

    fn statement(&mut self, stmt: &ParserStatement) -> ResolveResult<Option<Statement>> {
        Ok(match &stmt.kind {
            // These are already handled
            sylt_parser::StatementKind::EmptyStatement
            | sylt_parser::StatementKind::Use { .. }
            | sylt_parser::StatementKind::FromUse { .. }
            | sylt_parser::StatementKind::Blob { .. }
            | sylt_parser::StatementKind::Enum { .. } => None,

            sylt_parser::StatementKind::Definition { ident, kind, ty, value } => todo!("Edvard"),
            Start here! Start inserting some definitions and see what happens.

            sylt_parser::StatementKind::Assignment { kind, target, value } => todo!(),
            sylt_parser::StatementKind::ExternalDefinition { ident, kind, ty } => todo!(),
            sylt_parser::StatementKind::Loop { condition, body } => todo!(),
            sylt_parser::StatementKind::Break => todo!(),
            sylt_parser::StatementKind::Continue => todo!(),
            sylt_parser::StatementKind::Ret { value } => todo!(),
            sylt_parser::StatementKind::Block { statements } => todo!(),
            sylt_parser::StatementKind::StatementExpression { value } => todo!(),
            sylt_parser::StatementKind::Unreachable => todo!(),
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
                        Entry::Occupied(_) => { /* We allow importing the same thing multiple times */ }
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
                            Entry::Occupied(_) => { /* We allow importing the same thing multiple times */ }
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
