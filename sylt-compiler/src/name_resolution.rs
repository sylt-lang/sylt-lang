use std::collections::HashMap;

use sylt_common::{Error, FileOrLib};
use sylt_parser::{Identifier, Span, Statement as ParserStatement, VarKind, AST as ParserAST};

use crate::NamespaceID;

type ResolveResult<T> = Result<T, Vec<Error>>;
type Ref = usize;
type Namespace = usize;

#[derive(Debug, Clone, PartialEq)]
struct Var {
    id: Ref,
    definition: Option<Span>,
    kind: VarKind,
    usage: Vec<Span>,
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
enum Name {
    Name(Ref),
    Namespace(usize),
}

#[derive(Debug, Clone, PartialEq)]
enum TypeAssignable {
    SomeTypeAssignable,
}

struct Resolver {
    namespaces: HashMap<FileOrLib, HashMap<String, Name>>,
    variables: Vec<Var>,
}

impl Resolver {
    fn new() -> Self {
        Self {
            namespaces: HashMap::new(),
            variables: Vec::new(),
        }
    }

    fn statement(&mut self, stmt: &ParserStatement) -> Option<Statement> {
        match &stmt.kind {
            sylt_parser::StatementKind::EmptyStatement
            | sylt_parser::StatementKind::Use { .. }
            | sylt_parser::StatementKind::FromUse { .. }
            | sylt_parser::StatementKind::Blob { .. }
            | sylt_parser::StatementKind::Enum { .. } => None,

            sylt_parser::StatementKind::Definition { ident, kind, ty, value } => todo!("Erik"),

            sylt_parser::StatementKind::Assignment { kind, target, value } => todo!(),
            sylt_parser::StatementKind::ExternalDefinition { ident, kind, ty } => todo!(),
            sylt_parser::StatementKind::Loop { condition, body } => todo!(),
            sylt_parser::StatementKind::Break => todo!(),
            sylt_parser::StatementKind::Continue => todo!(),
            sylt_parser::StatementKind::Ret { value } => todo!(),
            sylt_parser::StatementKind::Block { statements } => todo!(),
            sylt_parser::StatementKind::StatementExpression { value } => todo!(),
            sylt_parser::StatementKind::Unreachable => todo!(),
        }
    }

    fn insert_namespace(&mut self, file_or_lib: FileOrLib) {
        self.namespaces.insert(file_or_lib, HashMap::new());
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

    fn define_namespace_variables(
        &mut self,
        file_or_lib: FileOrLib,
        statements: Vec<ParserStatement>,
    ) -> Result<(), Error> {
        for stmt in statements {
            match stmt.kind {
                sylt_parser::StatementKind::Use { path, name, file } => todo!(),
                sylt_parser::StatementKind::FromUse { path, imports, file } => todo!(),
                sylt_parser::StatementKind::Blob { name, variables, fields } => todo!(),
                sylt_parser::StatementKind::Enum { name, variables, variants } => todo!(),
                sylt_parser::StatementKind::Definition { ident, kind, ty, value } => {
                    let var = self.new_var(ident.span, kind);
                    self.define_variable(&file_or_lib, ident, Name::Name(var))
                }
                sylt_parser::StatementKind::ExternalDefinition { ident, kind, ty } => {
                    let var = self.new_var(ident.span, kind);
                    self.define_variable(&file_or_lib, ident, Name::Name(var))
                }

                sylt_parser::StatementKind::Loop { .. }
                | sylt_parser::StatementKind::Assignment { .. }
                | sylt_parser::StatementKind::Break
                | sylt_parser::StatementKind::Continue
                | sylt_parser::StatementKind::Ret {  .. }
                | sylt_parser::StatementKind::Block { .. }
                | sylt_parser::StatementKind::StatementExpression { .. }
                | sylt_parser::StatementKind::Unreachable
                | sylt_parser::StatementKind::EmptyStatement => {}
            };
        }
        Ok(())
    }
}

pub fn resolve<'a>(
    tree: &'a ParserAST,
    namespace_to_file: &HashMap<NamespaceID, FileOrLib>,
) -> Result<Vec<Statement>, Vec<Error>> {
    let mut resolver = Resolver::new();

    // Create namespaces and insert the variables in them
    tree.modules.iter().for_each(|(file_or_lib, module)| {
        resolver.insert_namespace(file_or_lib.clone());
        resolver.define_namespace_variables(file_or_lib.clone(), module.statements);
    });

    Ok(
        tree.modules
            .iter()
            .map(|(_, module)| {
                module
                    .statements
                    .iter()
                    .map(|stmt| resolver.statement(&stmt))
                    .filter_map(|x| x)
            })
            .flatten()
            .collect::<Vec<Statement>>()
    )
}
