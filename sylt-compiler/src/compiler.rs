use std::collections::{hash_map::Entry, HashMap};
use std::io::Write;
use sylt_common::error::Error;
use sylt_common::prog::Prog;
use sylt_common::{FileOrLib, Op, Type, Value};
use sylt_parser::statement::NameIdentifier;
use sylt_parser::{Identifier, Span, StatementKind, AST};

mod dependency;
mod lua;
mod ty;
mod typechecker;

type VarSlot = usize;

#[derive(Debug, Clone)]
struct Variable {
    name: String,
    slot: usize,
    span: Span,

    captured: bool,
    active: bool,
}

impl Variable {
    fn new(name: String, slot: usize, span: Span) -> Self {
        Self { name, slot, span, captured: false, active: false }
    }
}

#[derive(Debug, Clone)]
struct Upvalue {
    parent: usize,
    upupvalue: bool,

    name: String,
    slot: usize,
    span: Span,
}

enum Lookup {
    Upvalue(Upvalue),
    Variable(Variable),
}

impl Upvalue {
    fn capture(var: &Variable) -> Self {
        Self {
            parent: var.slot,
            upupvalue: false,

            name: var.name.clone(),
            slot: 0,
            span: var.span,
        }
    }

    fn loft(up: &Upvalue) -> Self {
        Self {
            parent: up.slot,
            upupvalue: true,
            slot: 0,
            ..up.clone()
        }
    }
}

#[derive(Debug, Copy, Clone)]
struct Context {
    namespace: NamespaceID,
    frame: usize,
}

type Namespace = HashMap<String, Name>;
type ConstantID = usize;
type NamespaceID = usize;
type BlobID = usize;
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Name {
    External,
    Global(ConstantID),
    Blob(BlobID),
    Enum(BlobID),
    Namespace(NamespaceID),
}

#[derive(Debug, Copy, Clone)]
struct LoopFrame {
    continue_addr: usize,
    break_addr: usize,
    stack_size: usize,
}

#[derive(Debug)]
/// Emulates the runtime stackframe.
/// [variables] and [upvalues] are used like stacks.
struct Frame {
    variables: Vec<Variable>,
    upvalues: Vec<Upvalue>,
}

impl Frame {
    fn new(name: &str, span: Span) -> Self {
        let variables = vec![Variable::new(name.to_string(), 0, span)];
        Self { variables, upvalues: Vec::new() }
    }
}

struct Compiler {
    namespace_id_to_file: HashMap<NamespaceID, FileOrLib>,

    namespaces: Vec<Namespace>,

    frames: Vec<Frame>,

    panic: bool,
    errors: Vec<Error>,

    constants: Vec<Value>,

    values: HashMap<Value, usize>,
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

            frames: Vec::new(),

            panic: false,
            errors: Vec::new(),

            constants: Vec::new(),

            values: HashMap::new(),
        }
    }

    fn file_from_namespace(&self, namespace: usize) -> &FileOrLib {
        self.namespace_id_to_file.get(&namespace).unwrap()
    }

    fn constant(&mut self, value: Value) -> Op {
        let slot = match self.values.entry(value.clone()) {
            Entry::Vacant(e) => {
                let slot = self.constants.len();
                e.insert(slot);
                self.constants.push(value);
                slot
            }
            Entry::Occupied(e) => *e.get(),
        };
        Op::Constant(slot)
    }

    fn resolve_and_capture(&mut self, name: &str, frame: usize, span: Span) -> Result<Lookup, ()> {
        // Frame 0 has globals which cannot be captured.
        if frame == 0 {
            return Err(());
        }

        let variables = &self.frames[frame].variables;
        for var in variables.iter().rev() {
            if &var.name == name && var.active {
                return Ok(Lookup::Variable(var.clone()));
            }
        }

        let upvalues = &self.frames[frame].upvalues;
        for up in upvalues.iter().rev() {
            if &up.name == name {
                return Ok(Lookup::Upvalue(up.clone()));
            }
        }

        let up = match self.resolve_and_capture(name, frame - 1, span) {
            Ok(Lookup::Upvalue(up)) => Upvalue::loft(&up),
            Ok(Lookup::Variable(var)) => Upvalue::capture(&var),
            _ => {
                return Err(());
            }
        };
        let up = self.upvalue(up, frame);
        Ok(Lookup::Upvalue(up))
    }

    fn define(&mut self, name: &str, span: Span) -> VarSlot {
        let frame = &mut self.frames.last_mut().unwrap().variables;
        let slot = frame.len();
        let var = Variable::new(name.to_string(), slot, span);
        frame.push(var);
        slot
    }

    fn upvalue(&mut self, mut up: Upvalue, frame: usize) -> Upvalue {
        let ups = &mut self.frames[frame].upvalues;
        let slot = ups.len();
        up.slot = slot;
        ups.push(up.clone());
        up
    }

    fn activate(&mut self, slot: VarSlot) {
        self.frames.last_mut().unwrap().variables[slot].active = true;
    }

    fn compile(
        mut self,
        typecheck: bool,
        lua_file: Box<dyn Write>,
        tree: AST,
    ) -> Result<Prog, Vec<Error>> {
        assert!(!tree.modules.is_empty(), "Cannot compile an empty program");
        let name = "/preamble/";
        let start_span = tree.modules[0].1.span;
        self.frames.push(Frame::new(name, start_span));

        self.extract_globals(&tree);

        let statements = match dependency::initialization_order(&tree, &self) {
            Ok(statements) => statements,
            Err(statements) => {
                statements.iter().for_each(|(statement, _)| {
                    error_no_panic!(self, statement.span, "Dependency cycle")
                });
                statements
            }
        };
        if !self.errors.is_empty() {
            return Err(self.errors);
        }

        if typecheck {
            typechecker::solve(&statements, &self.namespace_id_to_file)?;
        }

        let mut lua_compiler = lua::LuaCompiler::new(&mut self, Box::new(lua_file));

        lua_compiler.preamble(Span::zero(0), 0);
        for (statement, namespace) in statements.iter() {
            lua_compiler.compile(statement, *namespace);
        }
        lua_compiler.postamble(Span::zero(0));

        if !self.errors.is_empty() {
            return Err(self.errors);
        }

        Ok(Prog::Lua)
    }

    fn extract_globals(&mut self, tree: &AST) -> usize {
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

        let mut num_constants = 0;
        let mut from_statements = Vec::new();
        // Find all globals in all files and declare them. The globals are
        // initialized at a later stage.
        for (path, module) in tree.modules.iter() {
            let slot = include_to_namespace[path];

            let mut namespace = Namespace::new();
            for statement in module.statements.iter() {
                use StatementKind::*;
                let (name, ident_name, span) = match &statement.kind {
                    Blob { name, .. } => {
                        let blob =
                            self.constant(Value::Ty(Type::Blob(name.clone(), Default::default())));
                        if let Op::Constant(slot) = blob {
                            (Name::Blob(slot), name.clone(), statement.span)
                        } else {
                            unreachable!()
                        }
                    }
                    FromUse { .. } => {
                        // We cannot resolve this here since the namespace
                        // might not be loaded yet. We process these after.
                        from_statements.push(statement.clone());
                        continue;
                    }
                    Enum { name, .. } => {
                        let enum_ = Type::Enum(name.clone(), Default::default());
                        match self.constant(Value::Ty(enum_)) {
                            Op::Constant(slot) => (Name::Enum(slot), name.clone(), statement.span),
                            _ => unreachable!(),
                        }
                    }
                    Use { name, file, .. } => {
                        let ident = match name {
                            NameIdentifier::Implicit(ident) => ident,
                            NameIdentifier::Alias(ident) => ident,
                        };
                        let other = include_to_namespace[file];
                        (Name::Namespace(other), ident.name.clone(), ident.span)
                    }
                    Definition { ident: Identifier { name, .. }, .. } => {
                        let var = self.define(name, statement.span);
                        self.activate(var);
                        num_constants += 1;
                        (Name::Global(var), name.clone(), statement.span)
                    }
                    ExternalDefinition { ident: Identifier { name, .. }, .. } => {
                        let var = self.define(name, statement.span);
                        self.activate(var);
                        num_constants += 1;
                        (Name::External, name.clone(), statement.span)
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
        num_constants
    }
}

pub fn compile(
    typecheck: bool,
    lua_file: Box<dyn Write>,
    prog: AST,
) -> Result<Prog, Vec<Error>> {
    Compiler::new().compile(typecheck, lua_file, prog)
}
