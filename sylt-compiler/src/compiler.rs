use std::collections::{hash_map::Entry, HashMap};
use std::io::Write;
use sylt_common::error::Error;
use sylt_common::FileOrLib;
use sylt_parser::statement::NameIdentifier;
use sylt_parser::{Identifier, StatementKind, AST};

mod dependency;
mod intermediate;
mod lua;
mod ty;
mod typechecker;

type Namespace = HashMap<String, Name>;
type NamespaceID = usize;
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Name {
    Name,
    Namespace(NamespaceID),
}

struct Compiler {
    namespace_id_to_file: HashMap<NamespaceID, FileOrLib>,

    namespaces: Vec<Namespace>,

    panic: bool,
    errors: Vec<Error>,
}

#[macro_export]
macro_rules! error {
    ($compiler:expr, $span:expr, $( $msg:expr ),+ ) => {
        if !$compiler.panic {
            $compiler.panic = true;

            let msg = format!($( $msg ),*).into();
            let err = Error::CompileError {
                file: $compiler.file_from_namespace($span.file_id).clone(),
                span: $span,
                message: Some(msg),
            };
            $compiler.errors.push(err);
        }
    };
}

macro_rules! error_no_panic {
    ($compiler:expr, $span:expr, $( $msg:expr ),+ ) => {
        {
            error!($compiler, $span, $( $msg ),*);
            $compiler.panic = false;
        }
    };
}
impl Compiler {
    fn new() -> Self {
        Self {
            namespace_id_to_file: HashMap::new(),
            namespaces: Vec::new(),

            panic: false,
            errors: Vec::new(),
        }
    }

    fn file_from_namespace(&self, namespace: usize) -> &FileOrLib {
        self.namespace_id_to_file.get(&namespace).unwrap()
    }

    fn compile(mut self, lua_file: &mut dyn Write, tree: AST) -> Result<(), Vec<Error>> {
        assert!(!tree.modules.is_empty(), "Cannot compile an empty program");

        self.extract_globals(&tree);

        let mut statements = match dependency::initialization_order(&tree, &self) {
            // TODO(ed): This clone can probably be removed.
            Ok(statements) => statements
                .into_iter()
                .map(|(a, b)| (a.clone(), b))
                .collect(),
            Err(statements) => {
                statements.iter().for_each(|(statement, _)| {
                    error_no_panic!(self, statement.span, "Dependency cycle")
                });
                return Err(self.errors);
            }
        };
        if !self.errors.is_empty() {
            return Err(self.errors);
        }

        let typechecker = typechecker::solve(&mut statements, &self.namespace_id_to_file)?;

        let ir = intermediate::compile(&typechecker, &statements);
        let usage_count = intermediate::count_usages(&ir);

        for i in ir.iter() {
            eprintln!("> {:?}", i);
        }
        lua::generate(&ir, &usage_count, lua_file);

        Ok(())
    }

    fn extract_globals(&mut self, tree: &AST) {
        // Find all files and map them to their namespace
        let mut include_to_namespace = HashMap::new();
        for (path, _) in tree.modules.iter() {
            let slot = self.namespaces.len();
            self.namespaces.push(Namespace::new());

            if include_to_namespace.insert(path.clone(), slot).is_some() {
                unreachable!("File was read twice!?");
            }
        }

        // Reversed map
        self.namespace_id_to_file = include_to_namespace
            .iter()
            .map(|(a, b): (&FileOrLib, &usize)| (*b, (*a).clone()))
            .collect();

        let mut from_statements = Vec::new();

        // Find all globals in all files and declare them. The globals are
        // initialized at a later stage.
        for (path, module) in tree.modules.iter() {
            let slot = include_to_namespace[path];

            let mut namespace = Namespace::new();
            for statement in module.statements.iter() {
                use StatementKind::*;
                let (name, ident_name, span) = match &statement.kind {
                    FromUse { .. } => {
                        // We cannot resolve this here since the namespace
                        // might not be loaded yet. We process these after.
                        from_statements.push(statement.clone());
                        continue;
                    }
                    Use { name, file, .. } => {
                        let ident = match name {
                            NameIdentifier::Implicit(ident) => ident,
                            NameIdentifier::Alias(ident) => ident,
                        };
                        let other = include_to_namespace[file];
                        (Name::Namespace(other), ident.name.clone(), ident.span)
                    }
                    Enum { name, .. }
                    | Blob { name, .. }
                    | Definition { ident: Identifier { name, .. }, .. }
                    | ExternalDefinition { ident: Identifier { name, .. }, .. } => {
                        (Name::Name, name.clone(), statement.span)
                    }

                    // Handled later since we need type information.
                    IsCheck { .. } | EmptyStatement => continue,

                    _ => {
                        error!(self, statement.span, "Invalid outer statement");
                        continue;
                    }
                };
                match namespace.entry(ident_name.to_owned()) {
                    Entry::Vacant(vac) => {
                        vac.insert(name);
                    }
                    Entry::Occupied(_) => {
                        error!(
                            self,
                            span, "A global variable with the name '{}' already exists", ident_name
                        );
                    }
                }
            }
            self.namespaces[slot] = namespace;
        }

        for from_stmt in from_statements.into_iter() {
            let slot = from_stmt.span.file_id;
            match from_stmt.kind {
                StatementKind::FromUse { imports, file, .. } => {
                    let from_slot = include_to_namespace[&file];
                    for (ident, alias) in imports.iter() {
                        let name = match self.namespaces[from_slot].get(&ident.name) {
                            Some(name) => *name,
                            None => {
                                error!(
                                    self,
                                    ident.span, "Nothing named '{}' in '{:?}'", ident.name, file
                                );
                                continue;
                            }
                        };
                        let real_ident = alias.as_ref().unwrap_or(ident);
                        match self.namespaces[slot].entry(real_ident.name.clone()) {
                            Entry::Vacant(vac) => {
                                vac.insert(name);
                            }
                            Entry::Occupied(_) => {
                                error!(
                                    self,
                                    real_ident.span,
                                    "A global variable with the name '{}' already exists",
                                    real_ident.name
                                );
                            }
                        }
                    }
                }
                _ => unreachable!(),
            }
        }
    }
}

pub fn compile(lua_file: &mut dyn Write, prog: AST) -> Result<(), Vec<Error>> {
    Compiler::new().compile(lua_file, prog)
}
