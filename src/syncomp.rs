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

#[derive(Debug, Copy, Clone)]
struct Context {
    block_slot: BlockID,
    namespace: NamespaceID,
}

type Namespace = HashMap<String, Name>;
type ConstantID = usize;
type NamespaceID = usize;
type BlobID = usize;
type BlockID = usize;
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
                file: $compiler.file_from_context($namespace).into(),
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

    fn file_from_context(&self, ctx: Context) -> &str {
        self.namespace_id_to_path.get(&ctx.namespace).unwrap()
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

    fn add_op(&mut self, ctx: Context, span: Span, op: Op) -> usize {
        self.blocks.get_mut(ctx.block_slot).expect("Invalid block id").add(op, span.line)
    }

    fn assignable(&mut self, ass: &Assignable, ctx: Context) -> Context {
        use AssignableKind::*;

        match &ass.kind {
            Read(ident) => {
                self.read_identifier(&ident.name, ass.span, ctx)
            }
            Call(a, expr) => {
                self.assignable(a, ctx);
                for expr in expr.iter() {
                    self.expression(expr, ctx);
                }
                self.add_op(ctx, ass.span, Op::Call(expr.len()));
                ctx
            }
            Access(a, b) => {
                let ctx = self.assignable(a, ctx);
                self.assignable(b, ctx);
                ctx
            }
            Index(a, b) => {
                self.assignable(a, ctx);
                self.expression(b, ctx);
                self.add_op(ctx, ass.span, Op::GetIndex);
                ctx
            }
        }
    }

    fn un_op(&mut self, a: &Expression, ops: &[Op], span: Span, ctx: Context) {
        self.expression(&a, ctx);
        for op in ops {
            self.add_op(ctx, span, *op);
        }
    }

    fn bin_op(&mut self, a: &Expression, b: &Expression, ops: &[Op], span: Span, ctx: Context) {
        self.expression(&a, ctx);
        self.expression(&b, ctx);
        for op in ops {
            self.add_op(ctx, span, *op);
        }
    }

    fn push(&mut self, value: Value, span: Span, ctx: Context) {
        let value = self.constant(value);
        self.add_op(ctx, span, value);
    }

    fn expression(&mut self, expression: &Expression, ctx: Context) {
        use ExpressionKind::*;

        match &expression.kind {
            Get(a) => { self.assignable(a, ctx); },

            Add(a, b) => self.bin_op(a, b, &[Op::Add], expression.span, ctx),
            Sub(a, b) => self.bin_op(a, b, &[Op::Sub], expression.span, ctx),
            Mul(a, b) => self.bin_op(a, b, &[Op::Mul], expression.span, ctx),
            Div(a, b) => self.bin_op(a, b, &[Op::Div], expression.span, ctx),

            Eq(a, b)   => self.bin_op(a, b, &[Op::Equal], expression.span, ctx),
            Neq(a, b)  => self.bin_op(a, b, &[Op::Equal, Op::Not], expression.span, ctx),
            Gt(a, b)   => self.bin_op(a, b, &[Op::Greater], expression.span, ctx),
            Gteq(a, b) => self.bin_op(a, b, &[Op::Less, Op::Not], expression.span, ctx),
            Lt(a, b)   => self.bin_op(a, b, &[Op::Less], expression.span, ctx),
            Lteq(a, b) => self.bin_op(a, b, &[Op::Greater, Op::Not], expression.span, ctx),

            AssertEq(a, b) => self.bin_op(a, b, &[Op::Equal, Op::Assert], expression.span, ctx),

            Neg(a) => self.un_op(a, &[Op::Neg], expression.span, ctx),

            In(a, b) => self.bin_op(a, b, &[Op::Contains], expression.span, ctx),

            And(a, b) => self.bin_op(a, b, &[Op::And], expression.span, ctx),
            Or(a, b)  => self.bin_op(a, b, &[Op::Or], expression.span, ctx),
            Not(a)    => self.un_op(a, &[Op::Neg], expression.span, ctx),

            Function { params, ret, body } => {
                let file = self.file_from_context(ctx);
                let file_as_path = PathBuf::from(file);

                // TODO(ed): Better name
                let name = format!("fn {}:{}", file, expression.span.line);

                let inner_ctx = Context {
                    block_slot: self.blocks.len(),
                    ..ctx
                };
                self.blocks.push(Block::new_tree(&name, inner_ctx.namespace, &file_as_path));

                // TODO(ed): Push a stackframe here
                let mut param_types = Vec::new();
                for (ident, ty) in params.iter() {
                    param_types.push(self.resolve_type(&ty, inner_ctx));
                    let param = self.define(&ident.name, &VarKind::Const, ty, ident.span);
                    self.activate(param);
                }
                let ret = self.resolve_type(&ret, inner_ctx);
                let ty = Type::Function(param_types, Box::new(ret));
                self.blocks[inner_ctx.block_slot].ty = ty.clone();

                self.statement(&body, inner_ctx);
                // TODO(ed): Do some fancy program analysis
                let nil = self.constant(Value::Nil);
                self.add_op(inner_ctx, body.span, nil);
                self.add_op(inner_ctx, body.span, Op::Return);

                // TODO(ed): Pop the stackframe here

                let function = Value::Function(Rc::new(Vec::new()), ty, inner_ctx.block_slot);
                let function = self.constant(function);
                self.add_op(ctx, expression.span, function);

            }

            Instance { blob, fields } => {
                self.assignable(blob, ctx);
                for (name, field) in fields.iter() {
                    let name = self.constant(Value::Field(name.clone()));
                    self.add_op(ctx, field.span, name);
                    self.expression(field, ctx);
                }
                self.add_op(ctx, expression.span, Op::Call(fields.len() * 2));
            }

            Tuple(x) | List(x) | Set(x) | Dict(x) => {
                for expr in x.iter() {
                    self.expression(expr, ctx);
                }
                self.add_op(ctx, expression.span, match &expression.kind {
                    Tuple(_) => Op::Tuple(x.len()),
                    List(_) => Op::List(x.len()),
                    Set(_) => Op::Set(x.len()),
                    Dict(_) => Op::Dict(x.len()),
                    _ => unreachable!(),
                });
            }

            Float(a) => self.push(Value::Float(*a), expression.span, ctx),
            Bool(a)  => self.push(Value::Bool(*a), expression.span, ctx),
            Int(a)   => self.push(Value::Int(*a), expression.span, ctx),
            Str(a)   => self.push(Value::String(Rc::new(a.clone())), expression.span, ctx),
            Nil      => self.push(Value::Nil, expression.span, ctx),
        }
    }

    fn read_identifier(&mut self, name: &String, span: Span, ctx: Context) -> Context {
        match self.namespaces[0].get(name) {
            Some(Name::Slot(slot)) => {
                let op = Op::ReadGlobal(*slot);
                self.add_op(ctx, span, op);
                ctx
            },
            Some(Name::Namespace(new_namespace)) => {
                Context { namespace: *new_namespace, ..ctx }
            },
            Some(Name::Blob(blob)) => {
                let op = Op::Constant(*blob);
                self.add_op(ctx, span, op);
                ctx
            },
            _ => {
                error!(self, ctx, span, "No active variable called '{}' could be found", name);
                ctx
            },
        }
    }

    fn set_identifier(&mut self, name: &String, span: Span, ctx: Context) {
        match self.namespaces[0].get(name) {
            Some(Name::Slot(slot)) => {
                let op = Op::AssignGlobal(*slot);
                self.add_op(ctx, span, op);
            },
            _ => {
                error!(self, ctx, span, "No active variable called '{}' could be found", name);
            },
        }
    }

    fn resolve_type(&self, ty: &syntree::Type, ctx: Context) -> Type {
        // TODO(ed): Implement this
        Type::Void
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

    fn statement(&mut self, statement: &Statement, ctx: Context) {
        use StatementKind::*;

        match &statement.kind {
            EmptyStatement => {},

            Print { value } => {
                self.expression(value, ctx);
                self.add_op(ctx, statement.span, Op::Print);
            }

            Definition { ident, kind, ty, value } => {
                // TODO(ed): Don't use type here - type check the tree first.
                let slot = self.define(&ident.name, kind, ty, statement.span);
                self.expression(value, ctx);
                self.activate(slot);
            }

            Assignment { kind, target, value } => {
                use AssignableKind::*;

                match &target.kind {
                    Read(ident) => {
                        self.expression(value, ctx);
                        self.set_identifier(&ident.name, statement.span, ctx);
                    }
                    Call(_a, _expr) => {
                        error!(self, ctx, statement.span, "Cannot assign to result from function call");
                    }
                    Access(_a, _b) => {
                        unimplemented!("Assignment to accesses is not implemented");
                    }
                    Index(a, b) => {
                        self.assignable(a, ctx);
                        self.expression(b, ctx);
                        self.expression(value, ctx);
                        self.add_op(ctx, statement.span, Op::AssignIndex);
                    }
                }

                self.expression(value, ctx);
            }

            StatementExpression { value } => {
                self.expression(value, ctx);
                self.add_op(ctx, statement.span, Op::Pop);
            }

            Block { statements } => {
                for statement in statements {
                    self.statement(statement, ctx);
                }
            }

            Use { .. } => {}

            Blob { .. } => {}

            t => { unimplemented!("{:?}", t); }
        }
    }

    fn module(&mut self, module: &Module, ctx: Context) {
        for statement in module.statements.iter() {
            self.statement(statement, ctx);
        }
    }

    fn compile(mut self, tree: Prog) -> Result<crate::Prog, Vec<Error>> {
        assert!(!tree.modules.is_empty(), "Cannot compile an empty program");
        self.blocks.push(Block::new("/preamble/", &tree.modules[0].0));
        let ctx = Context {
            namespace: 0,
            block_slot: 0,
        };

        println!("{:#?}", tree);

        let globals = self.extract_globals(&tree);
        let nil = self.constant(Value::Nil);
        for _ in 0..globals {
            self.add_op(ctx, Span { line: 0 }, nil);
        }

        let module = &tree.modules[0].1;
        self.module(module, ctx);

        let nil = self.constant(Value::Nil);
        self.add_op(ctx, module.span, nil);
        self.add_op(ctx, module.span, Op::Return);

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
                    error!(self, Context { namespace: slot, block_slot: 0 },
                           Span { line: 0 }, "Reading module '{}' twice. How?", full_path.display());
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
                                    Context { namespace: slot, block_slot: 0 },
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
                                    Context { namespace: slot, block_slot: 0 },
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
                                    Context { namespace: slot, block_slot: 0 },
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

        globals;
        0
    }
}


pub fn compile(prog: Prog) -> Result<crate::Prog, Vec<Error>> {
    Compiler::new().compile(prog)
}
