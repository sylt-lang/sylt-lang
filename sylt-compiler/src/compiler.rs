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

type NamespaceID = usize;

struct Compiler {
    namespace_id_to_file: HashMap<NamespaceID, FileOrLib>,

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
            panic: false,
            errors: Vec::new(),
        }
    }

    fn file_from_namespace(&self, namespace: usize) -> &FileOrLib {
        self.namespace_id_to_file.get(&namespace).unwrap()
    }

    #[cfg_attr(timed, sylt_macro::timed("compile"))]
    fn compile(&mut self, lua_file: &mut dyn Write, tree: AST) -> Result<(), Vec<Error>> {
        assert!(!tree.modules.is_empty(), "Cannot compile an empty program");

        self.extract_namespaces(&tree);
        let (vars, statements) = name_resolution::resolve(&tree, &self.namespace_id_to_file)?;

        // TODO[ed]: These clones are unneeded!
        let statements = match dependency::initialization_order(&statements) {
            // TODO(ed): This clone can probably be removed.
            Ok(statements) => statements,
            Err(statements) => {
                statements.iter().for_each(|statement| {
                    error_no_panic!(self, statement.span(), "Dependency cycle")
                });
                return Err(self.errors.clone());
            }
        };
        if !self.errors.is_empty() {
            return Err(self.errors.clone());
        }

        let statements = statements.iter().map(|s| (*s).clone()).collect();
        let typechecker = typechecker::solve(&vars, &statements, &self.namespace_id_to_file)?;

        let ir = intermediate::compile(&typechecker, &statements);
        let usage_count = intermediate::count_usages(&ir);

        lua::generate(&ir, &usage_count, lua_file);

        Ok(())
    }

    fn extract_namespaces(&mut self, tree: &AST) {
        // Find all files and map them to their namespace
        let mut include_to_namespace = HashMap::new();
        for (path, module) in tree.modules.iter() {
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
    }
}

pub fn compile(lua_file: &mut dyn Write, prog: AST) -> Result<(), Vec<Error>> {
    Compiler::new().compile(lua_file, prog)
}
