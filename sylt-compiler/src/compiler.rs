use std::collections::HashMap;
use std::io::Write;
use sylt_common::error::Error;
use sylt_common::FileOrLib;
use sylt_parser::AST;

mod dependency;
mod intermediate;
mod lua;
mod name_resolution;
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
                helpers: Vec::new(),
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

    fn tree_to_statements(

    #[cfg_attr(timed, sylt_macro::timed("compile"))]
    fn compile(mut self, lua_file: &mut dyn Write, tree: AST) -> Result<(), Vec<Error>> {
        assert!(!tree.modules.is_empty(), "Cannot compile an empty program");

        let (vars, statements) = name_resolution::resolve(&tree, &self.namespace_id_to_file)?;
        let typechecker = typechecker::solve(&vars, &statements, &self.namespace_id_to_file)?;

        let ir = intermediate::compile(&typechecker, &statements);
        let usage_count = intermediate::count_usages(&ir);

        lua::generate(&ir, &usage_count, lua_file);

        Ok(())
    }

    fn extract_globals(&mut self, tree: &AST) {
        // Find all files and map them to their namespace
        let mut include_to_namespace = HashMap::new();
        for (path, module) in tree.modules.iter() {
            self.namespaces.push(Namespace::new());

            if include_to_namespace
                .insert(path.clone(), module.file_id)
                .is_some()
            {
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
        for (_, module) in tree.modules.iter() {
            let slot = module.file_id;

            let mut namespace = Namespace::new();
            for statement in module.statements.iter() {
                use StatementKind::*;
                let (name, ident_name, span) = match &statement.kind {
                    FromUse { .. } => {
                        // We cannot resolve this here since the namespace
                        // might not be loaded yet. We process these after.
                        from_statements.push((slot, statement.clone()));
                        continue;
                    }
                    Use { name, file, .. } => {
                        let ident = name.ident();
                        let other = include_to_namespace[file];
                        (Name::Namespace(other), ident.name.clone(), ident.span)
                    }
                    Enum { name, .. }
                    | Blob { name, .. }
                    | Definition { ident: name, .. }
                    | ExternalDefinition { ident: name, .. } => {
                        (Name::Name, name.name.clone(), name.span)
                    }

                    // Handled later since we need type information.
                    EmptyStatement => continue,

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

        for (slot, from_stmt) in from_statements.into_iter() {
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
