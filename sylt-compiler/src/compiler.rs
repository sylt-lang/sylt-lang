use std::collections::{hash_map::Entry, HashMap};
use std::path::{Path, PathBuf};
use sylt_common::error::Error;
use sylt_common::prog::Prog;
use sylt_common::{Op, RustFunction, Type, Value};
use sylt_parser::statement::NameIdentifier;
use sylt_parser::{
    Context as ParserContext,
    Assignable, AssignableKind, Identifier, Span,
    StatementKind, Type as ParserType, TypeKind, VarKind, AST,
};

mod typechecker;
mod dependency;
mod bytecode;
mod lua;

type VarSlot = usize;

#[derive(Debug, Clone)]
struct Variable {
    name: String,
    ty: Type,
    slot: usize,
    line: usize,
    kind: VarKind,

    captured: bool,
    active: bool,
}

impl Variable {
    fn new(name: String, kind: VarKind, ty: Type, slot: usize, span: Span) -> Self {
        Self {
            name,
            ty,
            slot,
            kind,
            line: span.line,

            captured: false,
            active: false,
        }
    }
}

#[derive(Debug, Clone)]
struct Upvalue {
    parent: usize,
    upupvalue: bool,

    name: String,
    ty: Type,
    slot: usize,
    line: usize,
    kind: VarKind,
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
            ty: var.ty.clone(),
            slot: 0,
            line: var.line,
            kind: var.kind,
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

impl Context {
    fn from_namespace(namespace: NamespaceID) -> Self {
        Self {
            namespace,
            frame: 0,
        }
    }
}

type Namespace = HashMap<String, Name>;
type ConstantID = usize;
type NamespaceID = usize;
type BlobID = usize;
type BlockID = usize;
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Name {
    External(VarKind),
    Global(ConstantID),
    Blob(BlobID),
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
        let variables = vec![Variable::new(
            name.to_string(),
            VarKind::Const,
            Type::Void,
            0,
            span,
        )];
        Self {
            variables,
            upvalues: Vec::new(),
        }
    }
}

struct Compiler {
    namespace_id_to_path: HashMap<NamespaceID, PathBuf>,

    namespaces: Vec<Namespace>,

    frames: Vec<Frame>,
    functions: HashMap<String, (usize, RustFunction, Type)>,

    panic: bool,
    errors: Vec<Error>,

    strings: Vec<String>,
    constants: Vec<Value>,

    values: HashMap<Value, usize>,
}

#[macro_export]
macro_rules! error {
    ($compiler:expr, $ctx:expr, $span:expr, $( $msg:expr ),+ ) => {
        if !$compiler.panic {
            $compiler.panic = true;

            let msg = format!($( $msg ),*).into();
            let err = Error::CompileError {
                file: $compiler.file_from_namespace($ctx.namespace).into(),
                span: $span,
                message: Some(msg),
            };
            $compiler.errors.push(err);
        }
    };
}

macro_rules! error_no_panic {
    ($compiler:expr, $ctx:expr, $span:expr, $( $msg:expr ),+ ) => {
        {
            error!($compiler, $ctx, $span, $( $msg ),*);
            $compiler.panic = false;
        }
    };
}
impl Compiler {
    fn new() -> Self {
        Self {
            namespace_id_to_path: HashMap::new(),
            namespaces: Vec::new(),

            frames: Vec::new(),
            functions: HashMap::new(),

            panic: false,
            errors: Vec::new(),

            strings: Vec::new(),
            constants: Vec::new(),

            values: HashMap::new(),
        }
    }

    fn pop_frame(&mut self, ctx: Context) -> Frame {
        assert_eq!(
            self.frames.len() - 1,
            ctx.frame,
            "Can only pop top stackframe"
        );
        self.frames.pop().unwrap()
    }

    fn file_from_namespace(&self, namespace: usize) -> &Path {
        self.namespace_id_to_path.get(&namespace).unwrap()
    }

    fn string(&mut self, string: &str) -> usize {
        self.strings
            .iter()
            .enumerate()
            .find_map(|(i, x)| if x == string { Some(i) } else { None })
            .unwrap_or_else(|| {
                let slot = self.strings.len();
                self.strings.push(string.into());
                slot
            })
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

    fn resolve_type_namespace(
        &mut self,
        assignable: &Assignable,
        namespace: usize,
        ctx: Context,
    ) -> Option<usize> {
        use AssignableKind::*;
        match &assignable.kind {
            Access(inner, ident) => self
                .resolve_type_namespace(&inner, namespace, ctx)
                .and_then(|namespace| self.namespaces[namespace].get(&ident.name))
                .and_then(|o| match o {
                    Name::Namespace(namespace) => Some(*namespace),
                    _ => None,
                })
                .or_else(|| {
                    error!(
                        self,
                        ctx,
                        assignable.span,
                        "While parsing namespace access '{}' is not a namespace",
                        ident.name
                    );
                    None
                }),
            Read(ident) => {
                self
                .namespaces[namespace].get(&ident.name)
                .and_then(|o| match o {
                    Name::Namespace(namespace) => Some(*namespace),
                    _ => None,
                })
                .or_else(|| {
                    error!(
                        self,
                        ctx,
                        assignable.span,
                        "While parsing namespace '{}' is not a namespace",
                        ident.name
                    );
                None
                })
            }
            ArrowCall(..) | Call(..) => {
                error!(self, ctx, assignable.span, "Cannot have calls in types");
                None
            }
            Index(_, _) => {
                error!(self, ctx, assignable.span, "Cannot have indexing in types");
                None
            }
            Expression(_) => {
                error!(self, ctx, assignable.span, "Cannot have expressions in types");
                None
            }
        }
    }

    fn resolve_type_ident(
        &mut self,
        assignable: &Assignable,
        namespace: usize,
        ctx: Context,
    ) -> Type {
        use AssignableKind::*;
        match &assignable.kind {
            Read(ident) => self.namespaces[namespace]
                .get(&ident.name)
                .and_then(|name| match name {
                    Name::Blob(blob) => match &self.constants[*blob] {
                        Value::Ty(ty) => Some(ty.clone()),
                        _ => None,
                    }
                    _ => None,
                })
                .unwrap_or_else(|| {
                    error!(
                        self,
                        ctx, assignable.span, "While parsing type '{}' is not a blob", ident.name
                    );
                    Type::Void
                }),
            Access(inner, ident) => self
                .resolve_type_namespace(&inner, namespace, ctx)
                .and_then(|namespace| self.namespaces[namespace].get(&ident.name))
                .and_then(|name| match name {
                    Name::Blob(blob) => match &self.constants[*blob] {
                        Value::Ty(ty) => Some(ty.clone()),
                        _ => None,
                    }
                    _ => None,
                })
                .unwrap_or_else(|| {
                    error!(
                        self,
                        ctx, assignable.span, "While parsing type '{}' is not a blob", ident.name
                    );
                    Type::Void
                }),
            ArrowCall(..) | Call(..) => {
                error!(self, ctx, assignable.span, "Cannot have calls in types");
                Type::Void
            }
            Index(..) => {
                error!(self, ctx, assignable.span, "Cannot have indexing in types");
                Type::Void
            }
            Expression(_) => {
                error!(self, ctx, assignable.span, "Cannot have expressions in types");
                Type::Void
            }
        }
    }

    fn resolve_type(&mut self, ty: &ParserType, ctx: Context) -> Type {
        use TypeKind::*;
        match &ty.kind {
            Implied => Type::Unknown,
            Resolved(ty) => ty.clone(),
            UserDefined(assignable) => self.resolve_type_ident(&assignable, ctx.namespace, ctx),
            Union(a, b) => match (self.resolve_type(a, ctx), self.resolve_type(b, ctx)) {
                (Type::Union(_), _) => panic!("Didn't expect union on RHS - check parser"),
                (a, Type::Union(mut us)) => {
                    us.insert(a);
                    Type::Union(us)
                }
                (a, b) => Type::Union(vec![a, b].into_iter().collect()),
            },
            Fn(params, ret) => {
                let params = params.iter().map(|t| self.resolve_type(t, ctx)).collect();
                let ret = Box::new(self.resolve_type(ret, ctx));
                Type::Function(params, ret)
            }
            Tuple(fields) => {
                Type::Tuple(fields.iter().map(|t| self.resolve_type(t, ctx)).collect())
            }
            List(kind) => Type::List(Box::new(self.resolve_type(kind, ctx))),
            Set(kind) => Type::Set(Box::new(self.resolve_type(kind, ctx))),
            Dict(key, value) => Type::Dict(
                Box::new(self.resolve_type(key, ctx)),
                Box::new(self.resolve_type(value, ctx)),
            ),
            Generic(name) => Type::Generic(name.name.clone()),
        }
    }

    fn define(&mut self, name: &str, kind: VarKind, span: Span) -> VarSlot {
        let frame = &mut self.frames.last_mut().unwrap().variables;
        let slot = frame.len();
        let var = Variable::new(name.to_string(), kind, Type::Unknown, slot, span);
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
        tree: AST,
        functions: &[(String, RustFunction, String)],
    ) -> Result<Prog, Vec<Error>> {
        assert!(!tree.modules.is_empty(), "Cannot compile an empty program");
        let name = "/preamble/";
        let start_span = tree.modules[0].1.span;
        self.frames.push(Frame::new(name, start_span));
        let ctx = Context {
            frame: 0,
            ..Context::from_namespace(0)
        };

        let _num_constants = self.extract_globals(&tree);

        let num_functions = functions.len();
        self.functions = functions
            .to_vec()
            .into_iter()
            .enumerate()
            .map(|(i, (s, f, sig))| (s.clone(), (i, f, self.resolve_type(&parse_signature(&s, &sig), ctx))))
            .collect();
        assert_eq!(
            num_functions,
            self.functions.len(),
            "There are {} names and {} extern functions - some extern functions share name",
            self.functions.len(),
            num_functions
        );

        let statements = match dependency::initialization_order(&tree, &self) {
            Ok(statements) => statements,
            Err(statements) => {
                statements.iter().for_each(|(statement, namespace)|
                    error_no_panic!(self, Context::from_namespace(*namespace), statement.span, "Dependency cycle")
                );
                statements
            }
        };
        if !self.errors.is_empty() {
            return Err(self.errors);
        }

        // let blocks = {
        //     let mut bytecode_compiler = bytecode::BytecodeCompiler::new(&mut self);
        //     bytecode_compiler.preamble(start_span, num_constants);

        //     for (statement, namespace) in statements.iter() {
        //         bytecode_compiler.compile(statement, *namespace);
        //     }

        //     bytecode_compiler.postamble(start_span);
        //     bytecode_compiler.blocks
        // };

        {
            let mut lua_compiler = lua::LuaCompiler::new(&mut self);

            lua_compiler.preamble(Span::zero(), 0);
            for (statement, namespace) in statements.iter() {
                lua_compiler.compile(statement, *namespace);
            }
            lua_compiler.postamble(Span::zero());

            println!("{}", lua_compiler.blocks);
        }

        if !self.errors.is_empty() {
            return Err(self.errors);
        }

        if typecheck {
            typechecker::solve(&mut self, &statements)?;
        }

        if self.errors.is_empty() {
            Ok(Prog {
                blocks: Vec::new(),
                functions: functions.iter().map(|(_, f, _)| *f).collect(),
                constants: self.constants,
                strings: self.strings,
            })
        } else {
            Err(self.errors)
        }
    }

    fn extract_globals(&mut self, tree: &AST) -> usize {
        // Find all files and map them to their namespace
        let mut path_to_namespace_id = HashMap::<PathBuf, usize>::new();
        for (path, _) in tree.modules.iter() {
            let slot = self.namespaces.len();
            self.namespaces.push(Namespace::new());

            if path_to_namespace_id.insert(path.into(), slot).is_some() {
                unreachable!("File was read twice!?");
            }
        }

        // Reversed map
        self.namespace_id_to_path = path_to_namespace_id
            .iter()
            .map(|(a, b)| (*b, (*a).clone()))
            .collect();

        let mut num_constants = 0;
        // Find all globals in all files and declare them. The globals are
        // initialized at a later stage.
        for (path, module) in tree.modules.iter() {
            let slot = path_to_namespace_id[path];
            let ctx = Context::from_namespace(slot);

            let mut namespace = Namespace::new();
            for statement in module.statements.iter() {
                use StatementKind::*;
                let (name, ident_name, span) = match &statement.kind {
                    Blob { name, .. } => {
                        let blob = self.constant(Value::Ty(Type::Blob(name.clone(), Default::default())));
                        if let Op::Constant(slot) = blob {
                            (Name::Blob(slot), name.clone(), statement.span)
                        } else {
                            unreachable!()
                        }
                    },
                    Use { path: _, name, file } => {
                        let ident = match name {
                            NameIdentifier::Implicit(ident) => ident,
                            NameIdentifier::Alias(ident) => ident,
                        };
                        let other = path_to_namespace_id[file];
                        (Name::Namespace(other), ident.name.clone(), ident.span)
                    }
                    Definition { ident: Identifier { name, .. }, kind, .. } => {
                        let var = self.define(name, *kind, statement.span);
                        self.activate(var);
                        num_constants += 1;
                        (Name::Global(var), name.clone(), statement.span)
                    }
                    ExternalDefinition { ident: Identifier { name, .. }, kind, .. } => {
                        let var = self.define(name, *kind, statement.span);
                        self.activate(var);
                        num_constants += 1;
                        (Name::External(*kind), name.clone(), statement.span)
                    }

                    // Handled later since we need type information.
                    | IsCheck { .. }
                    | EmptyStatement => continue,

                    _ => {
                        error!(self, ctx, statement.span, "Invalid outer statement");
                        continue;
                    }
                };

                match namespace.entry(ident_name.to_owned()) {
                    Entry::Vacant(vac) => { vac.insert(name); }
                    Entry::Occupied(_) => {
                        error!(
                            self,
                            ctx,
                            span,
                            "A global variable with the name '{}' already exists",
                            ident_name
                        );
                    }
                }
            }
            self.namespaces[slot] = namespace;
        }
        num_constants
    }
}

// TODO(ed): Move this up into sylt?
fn parse_signature(func_name: &str, sig: &str) -> ParserType {
    let token_stream = sylt_tokenizer::string_to_tokens(sig);
    let tokens: Vec<_> = token_stream.iter().map(|p| p.token.clone()).collect();
    let spans: Vec<_> = token_stream.iter().map(|p| p.span).collect();
    let path = PathBuf::from(func_name);
    let ctx = ParserContext::new(&tokens, &spans, &path, &path);
    match sylt_parser::parse_type(ctx) {
        Ok((_, ty)) => ty,
        Err((_, errs)) => {
            for err in errs {
                eprintln!("{}", err);
            }
            panic!("Error parsing function signature for {}", func_name);
        }
    }
}

pub fn compile(typecheck: bool, prog: AST, functions: &[(String, RustFunction, String)]) -> Result<Prog, Vec<Error>> {
    Compiler::new().compile(typecheck, prog, functions)
}

pub(crate) fn first_ok_or_errs<I, T, E>(mut iter: I) -> Result<T, Vec<E>>
where I: Iterator<Item = Result<T, E>>
{
    let mut errs = Vec::new();
    loop {
        match iter.next() {
            Some(Ok(t)) => return Ok(t),
            Some(Err(e)) => errs.push(e),
            None => return Err(errs),
        }
    }
}
