use crate::error::Error;
use crate::syntree;
use syntree::*;
use crate::{Op, Block, Value, Type};
use std::collections::{hash_map::Entry, HashMap};
use crate::rc::Rc;
use std::cell::RefCell;
use std::path::PathBuf;

type VarSlot = usize;

struct Variable {
    name: String,
    ty: Type,
    slot: usize,
    line: usize,

    active: bool,
}

impl Variable {
    fn new(name: String, ty: Type, slot: usize, span: Span) -> Self {
        Self {
            name,
            ty,
            slot,
            line: span.line,

            active: false,
        }
    }

    fn filler() -> Self {
        Variable::new("/filler/".into(), Type::Unknown, 0, Span { line: 0 })
    }
}

type Namespace = HashMap<String, Name>;
type ConstantID = usize;
type NamespaceID = usize;
type BlobID = usize;
#[derive(Debug, Copy, Clone)]
enum Name {
    Slot(ConstantID),
    Blob(BlobID),
    Namespace(NamespaceID),
}

struct Compiler {
    blocks: Vec<Block>,

    namespace_id_to_path: HashMap<NamespaceID, String>,

    namespaces: Vec<Namespace>,
    blobs: Vec<usize>,

    // TODO(ed): Stackframes

    panic: bool,
    errors: Vec<Error>,

    strings: Vec<String>,
    constants: Vec<Value>,

    values: HashMap<Value, usize>,
}

macro_rules! error {
    ($compiler:expr, $namespace:expr, $span:expr, $( $msg:expr ),+ ) => {
        if !$compiler.panic {
            $compiler.panic = true;

            let msg = format!($( $msg ),*).into();
            let err = Error::CompileError {
                file: $compiler.file_for_namespace($namespace.clone()).into(),
                line: $span.line,
                message: Some(msg),
            };
            $compiler.errors.push(err);
        }
    };
}

impl Compiler {
    fn new() -> Self {
        Self {
            blocks: Vec::new(),

            namespace_id_to_path: HashMap::new(),
            namespaces: Vec::new(),
            blobs: Vec::new(),

            panic: false,
            errors: Vec::new(),

            strings: Vec::new(),
            constants: Vec::new(),

            values: HashMap::new(),
        }
    }

    fn file_for_namespace(&self, namespace: NamespaceID) -> &str {
        self.namespace_id_to_path.get(&namespace).unwrap()
    }

    fn constant(&mut self, value: Value) -> Op {
        let slot = match self.values.entry(value.clone()) {
            Entry::Vacant(e) => {
                let slot = self.constants.len();
                e.insert(slot);
                self.constants.push(value);
                slot
            }
            Entry::Occupied(e) => {
                *e.get()
            }
        };
        Op::Constant(slot)
    }

    fn add_op(&mut self, span: Span, op: Op) -> usize {
        self.blocks.last_mut().unwrap().add(op, span.line)
    }

    fn assignable(&mut self, ass: &Assignable, namespace: NamespaceID) -> NamespaceID {
        use AssignableKind::*;

        match &ass.kind {
            Read(ident) => {
                self.read_identifier(&ident.name, ass.span, namespace)
            }
            Call(a, expr) => {
                self.assignable(a, namespace);
                for expr in expr.iter() {
                    self.expression(expr, namespace);
                }
                self.add_op(ass.span, Op::Call(expr.len()));
                namespace
            }
            Access(a, b) => {
                let namespace = self.assignable(a, namespace);
                self.assignable(b, namespace);
                namespace
            }
            Index(a, b) => {
                self.assignable(a, namespace);
                self.expression(b, namespace);
                self.add_op(ass.span, Op::GetIndex);
                namespace
            }
        }
    }

    fn un_op(&mut self, a: &Expression, ops: &[Op], span: Span, namespace: NamespaceID) {
        self.expression(&a, namespace);
        for op in ops {
            self.add_op(span, *op);
        }
    }

    fn bin_op(&mut self, a: &Expression, b: &Expression, ops: &[Op], span: Span, namespace: NamespaceID) {
        self.expression(&a, namespace);
        self.expression(&b, namespace);
        for op in ops {
            self.add_op(span, *op);
        }
    }

    fn push(&mut self, value: Value, span: Span) {
        let value = self.constant(value);
        self.add_op(span, value);
    }

    fn expression(&mut self, expression: &Expression, namespace: NamespaceID) {
        use ExpressionKind::*;

        match &expression.kind {
            Get(a) => { self.assignable(a, namespace); },

            Add(a, b) => self.bin_op(a, b, &[Op::Add], expression.span, namespace),
            Sub(a, b) => self.bin_op(a, b, &[Op::Sub], expression.span, namespace),
            Mul(a, b) => self.bin_op(a, b, &[Op::Mul], expression.span, namespace),
            Div(a, b) => self.bin_op(a, b, &[Op::Div], expression.span, namespace),

            Eq(a, b)   => self.bin_op(a, b, &[Op::Equal], expression.span, namespace),
            Neq(a, b)  => self.bin_op(a, b, &[Op::Equal, Op::Not], expression.span, namespace),
            Gt(a, b)   => self.bin_op(a, b, &[Op::Greater], expression.span, namespace),
            Gteq(a, b) => self.bin_op(a, b, &[Op::Less, Op::Not], expression.span, namespace),
            Lt(a, b)   => self.bin_op(a, b, &[Op::Less], expression.span, namespace),
            Lteq(a, b) => self.bin_op(a, b, &[Op::Greater, Op::Not], expression.span, namespace),

            AssertEq(a, b) => self.bin_op(a, b, &[Op::Equal, Op::Assert], expression.span, namespace),

            Neg(a) => self.un_op(a, &[Op::Neg], expression.span, namespace),

            In(a, b) => self.bin_op(a, b, &[Op::Contains], expression.span, namespace),

            And(a, b) => self.bin_op(a, b, &[Op::And], expression.span, namespace),
            Or(a, b)  => self.bin_op(a, b, &[Op::Or], expression.span, namespace),
            Not(a)    => self.un_op(a, &[Op::Neg], expression.span, namespace),

            Function { params, ret, body } => {
                // TODO(ed): Push a stackframe here

                let file = PathBuf::from(self.file_for_namespace(namespace));
                let mut block = Block::new_tree("fn", namespace, &file);
                for (ident, ty) in params.iter() {
                    let param = self.define(&ident.name, &VarKind::Const, ty, ident.span);
                    self.activate(param);
                }

                // TODO(ed): Pop the stackframe here
                self.statement(&body, namespace);
            }

            Instance { blob, fields } => {
                self.assignable(blob, namespace);
                for (name, field) in fields.iter() {
                    let name = self.constant(Value::Field(name.clone()));
                    self.add_op(field.span, name);
                    self.expression(field, namespace);
                }
                self.add_op(expression.span, Op::Call(fields.len() * 2));
            }

            Tuple(x) | List(x) | Set(x) | Dict(x) => {
                for expr in x.iter() {
                    self.expression(expr, namespace);
                }
                self.add_op(expression.span, match &expression.kind {
                    Tuple(_) => Op::Tuple(x.len()),
                    List(_) => Op::List(x.len()),
                    Set(_) => Op::Set(x.len()),
                    Dict(_) => Op::Dict(x.len()),
                    _ => unreachable!(),
                });
            }

            Float(a) => self.push(Value::Float(*a), expression.span),
            Bool(a)  => self.push(Value::Bool(*a), expression.span),
            Int(a)   => self.push(Value::Int(*a), expression.span),
            Str(a)   => self.push(Value::String(Rc::new(a.clone())), expression.span),
            Nil      => self.push(Value::Nil, expression.span),
        }
    }

    fn read_identifier(&mut self, name: &String, span: Span, namespace: NamespaceID) -> NamespaceID {
        match self.namespaces[0].get(name) {
            Some(Name::Slot(slot)) => {
                let op = Op::ReadGlobal(*slot);
                self.add_op(span, op);
                namespace
            },
            Some(Name::Namespace(new_namespace)) => {
                *new_namespace
            },
            Some(Name::Blob(blob)) => {
                let op = Op::Constant(*blob);
                self.add_op(span, op);
                namespace
            },
            _ => {
                error!(self, namespace, span, "No active variable called '{}' could be found", name);
                namespace
            },
        }
    }

    fn set_identifier(&mut self, name: &String, span: Span, namespace: NamespaceID) {
        match self.namespaces[0].get(name) {
            Some(Name::Slot(slot)) => {
                let op = Op::AssignGlobal(*slot);
                self.add_op(span, op);
            },
            _ => {
                error!(self, namespace, span, "No active variable called '{}' could be found", name);
            },
        }
    }

    fn resolve_type(&self, assignable: Assignable, namespace: NamespaceID) -> Type {
        unimplemented!();
    }

    fn define(&mut self, name: &String, kind: &VarKind, ty: &syntree::Type, span: Span) -> VarSlot {
        // TODO(ed): Fix the types
        // TODO(ed): Mutability
        // TODO(ed): Scoping
        // let slot = self.globals.len();
        // let var = Variable::new(name.clone(), Type::Unknown, slot, span);
        // self.globals.push(var);
        // slot
        0
    }

    fn activate(&mut self, slot: VarSlot) {
        // self.globals[slot].active = true;
    }

    fn statement(&mut self, statement: &Statement, namespace: NamespaceID) {
        use StatementKind::*;

        match &statement.kind {
            EmptyStatement => {},

            Print { value } => {
                self.expression(value, namespace);
                self.add_op(statement.span, Op::Print);
            }

            Definition { ident, kind, ty, value } => {
                // TODO(ed): Don't use type here - type check the tree first.
                let slot = self.define(&ident.name, kind, ty, statement.span);
                self.expression(value, namespace);
                self.activate(slot);
            }

            Assignment { kind, target, value } => {
                use AssignableKind::*;

                match &target.kind {
                    Read(ident) => {
                        self.expression(value, namespace);
                        self.set_identifier(&ident.name, statement.span, namespace);
                    }
                    Call(_a, _expr) => {
                        error!(self, namespace, statement.span, "Cannot assign to result from function call");
                    }
                    Access(_a, _b) => {
                        unimplemented!("Assignment to accesses is not implemented");
                    }
                    Index(a, b) => {
                        self.assignable(a, namespace);
                        self.expression(b, namespace);
                        self.expression(value, namespace);
                        self.add_op(statement.span, Op::AssignIndex);
                    }
                }

                self.expression(value, namespace);
            }

            StatementExpression { value } => {
                self.expression(value, namespace);
                self.add_op(statement.span, Op::Pop);
            }

            Block { .. } => {}

            Use { .. } => {}

            Blob { .. } => {}

            t => { unimplemented!("{:?}", t); }
        }
    }

    fn module(&mut self, module: &Module, namespace: NamespaceID) {
        for statement in module.statements.iter() {
            self.statement(statement, namespace);
        }
    }

    fn compile(mut self, tree: Prog) -> Result<crate::Prog, Vec<Error>> {
        assert!(!tree.modules.is_empty(), "Cannot compile an empty program");
        self.blocks.push(Block::new("/preamble/", &tree.modules[0].0));

        println!("{:#?}", tree);

        let globals = self.extract_globals(&tree);
        let nil = self.constant(Value::Nil);
        for _ in 0..globals {
            self.add_op(Span { line: 0 }, nil);
        }

        let namespace = 0;
        let module = &tree.modules[0].1;
        self.module(module, namespace);

        let nil = self.constant(Value::Nil);
        self.add_op(module.span, nil);
        self.add_op(module.span, Op::Return);

        if self.errors.is_empty() {
            Ok(crate::Prog {
                blocks: self.blocks.into_iter().map(|x| Rc::new(RefCell::new(x))).collect(),
                functions: Vec::new(),
                constants: self.constants,
                strings: self.strings,
            })
        } else {
            Err(self.errors)
        }
    }

    fn extract_globals(&mut self, tree: &Prog) -> usize {
        // TODO(ed): Check for duplicates
        let mut path_to_namespace_id = HashMap::new();
        for (full_path, _) in tree.modules.iter() {
            let slot = path_to_namespace_id.len();
            let path = full_path.file_stem().unwrap().to_str().unwrap().to_owned();
            match path_to_namespace_id.entry(path) {
                Entry::Vacant(vac) => {
                    vac.insert(slot);
                    self.namespaces.push(Namespace::new());
                }

                Entry::Occupied(_) => {
                    error!(self, slot, Span { line: 0 }, "Reading module '{}' twice. How?", full_path.display());
                }
            }
        }

        let mut globals = 0;
        for (path, module) in tree.modules.iter() {
            let path = path.file_stem().unwrap().to_str().unwrap();
            let slot = path_to_namespace_id[path];
            for statement in module.statements.iter() {
                use StatementKind::*;
                let namespace = &mut self.namespaces[slot];
                match &statement.kind {
                    Use { file: Identifier { name, span } } => {
                        let other = path_to_namespace_id[name];
                        match namespace.entry(name.to_owned()) {
                            Entry::Vacant(vac) => {
                                vac.insert(Name::Namespace(other));
                            }
                            Entry::Occupied(_) => {
                                error!(
                                    self,
                                    slot,
                                    span,
                                    "A global variable with the name '{}' already exists",
                                    name
                                );
                            }
                        }
                    }

                    // TODO(ed): Maybe break this out into it's own "type resolution thing?"
                    Blob { name, .. } => {
                        match namespace.entry(name.to_owned()) {
                            Entry::Vacant(vac) => {
                                let id = self.blobs.len();
                                let blob = crate::Blob::new_tree(id, slot, name);
                                let slot = self.constants.len();
                                self.constants.push(Value::Blob(Rc::new(blob)));
                                vac.insert(Name::Blob(slot));
                            }

                            Entry::Occupied(_) => {
                                error!(
                                    self,
                                    slot,
                                    statement.span,
                                    "A global variable with the name '{}' already exists", name
                                );
                            }
                        }
                    }

                    Definition { ident: Identifier { name, span }, .. } => {
                        match namespace.entry(name.to_owned()) {
                            Entry::Vacant(vac) => {
                                // NOTE(ed): +1 is to ignore the entry point
                                vac.insert(Name::Slot(globals + 1));
                                globals += 1;
                            }

                            Entry::Occupied(_) => {
                                error!(
                                    self,
                                    slot,
                                    span,
                                    "A global variable with the name '{}' already exists", name
                                );
                            }
                        }
                    }

                    _ => {
                        // TODO(ed): Throw error
                    }
                }
            }
        }

        // TODO(ed): Resolve the types of all blob fields here!
        // Thank god we're a scripting language - otherwise this would be impossible.
        self.namespace_id_to_path = path_to_namespace_id.into_iter().map(|(a, b)| (b, a)).collect();

        globals
    }
}


pub fn compile(prog: Prog) -> Result<crate::Prog, Vec<Error>> {
    Compiler::new().compile(prog)
}
