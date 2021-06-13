use crate::error::Error;
use crate::syntree;
use syntree::*;
use crate::{Op, Block, Value, Type, Blob, RustFunction};
use std::collections::{hash_map::Entry, HashMap};
use crate::rc::Rc;
use std::cell::RefCell;
use std::path::PathBuf;

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

impl Upvalue {
    fn capture(var: &Variable, slot: usize) -> Self {
        Self {
            parent: var.slot,
            upupvalue: false,

            name: var.name.clone(),
            ty: var.ty.clone(),
            slot,
            line: var.line,
            kind: var.kind,
        }
    }

    fn loft(up: &Upvalue, slot: usize) -> Self {
        Self {
            parent: up.slot,
            upupvalue: true,
            ..up.clone()
        }
    }
}

#[derive(Debug, Copy, Clone)]
struct Context {
    block_slot: BlockID,
    namespace: NamespaceID,
    scope: usize,
    frame: usize,
}

impl Context {
    fn from_namespace(namespace: NamespaceID) -> Self {
        Self {
            namespace,
            block_slot: 0,
            scope: 0,
            frame: 0,
        }
    }
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

#[derive(Debug)]
struct Frame {
    variables: Vec<Variable>,
    upvalues: Vec<Upvalue>,
}

impl Frame {
    fn new(name: &str, span: Span) -> Self {
        let variables = vec![Variable::new(name.to_string(), VarKind::Const, Type::Void, 0, span)];
        Self {
            variables,
            upvalues: Vec::new(),
        }
    }
}

struct Compiler {
    blocks: Vec<Block>,
    namespace_id_to_path: HashMap<NamespaceID, String>,

    namespaces: Vec<Namespace>,
    blobs: Vec<Blob>,

    stack: Vec<Frame>,
    functions: HashMap<String, (usize, RustFunction)>,

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

            stack: Vec::new(),
            functions: HashMap::new(),

            panic: false,
            errors: Vec::new(),

            strings: Vec::new(),
            constants: Vec::new(),

            values: HashMap::new(),
        }
    }

    fn push_frame_and_block(&mut self, ctx: Context, name: &str, span: Span) -> Context {
        let file_as_path = PathBuf::from(self.file_from_context(ctx));

        let block = Block::new_tree(&name, ctx.namespace, &file_as_path);
        self.blocks.push(block);

        self.stack.push(Frame::new(name, span));
        Context {
            block_slot: self.blocks.len() - 1,
            frame: self.stack.len() - 1,
            ..ctx
        }
    }

    fn pop_frame(&mut self, ctx: Context) {
        assert_eq!(self.stack.len() - 1, ctx.frame, "Can only pop top stackframe");
        self.stack.pop();
    }

    fn file_from_context(&self, ctx: Context) -> &str {
        self.namespace_id_to_path.get(&ctx.namespace).unwrap()
    }

    fn string(&mut self, string: &str) -> usize {
        if let Some(slot) = self.strings
            .iter()
            .enumerate()
            .find_map(|(i, x)| if x == string { Some(i) } else { None }) {
            slot
        } else {
            let slot = self.strings.len();
            self.strings.push(string.into());
            slot
        }
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

    fn patch(&mut self, ctx: Context, ip: usize, op: Op) {
        self.blocks.get_mut(ctx.block_slot).expect("Invalid block id").ops[ip] = op;
    }

    fn next_ip(&mut self, ctx: Context) -> usize {
        self.blocks.get_mut(ctx.block_slot).expect("Invalid block id").curr()
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
            Access(a, field) => {
                let ctx = self.assignable(a, ctx);
                let slot = self.string(&field.name);
                self.add_op(ctx, field.span, Op::GetField(slot));
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

            Function { name, params, ret, body } => {
                let file = self.file_from_context(ctx);
                let name = format!("fn {} {}:{}", name, file, expression.span.line);

                // === Frame begin ===
                let inner_ctx = self.push_frame_and_block(ctx, &name, expression.span);
                let mut param_types = Vec::new();
                for (ident, ty) in params.iter() {
                    param_types.push(self.resolve_type(&ty, inner_ctx));
                    let param = self.define(&ident.name, VarKind::Const, ident.span);
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

                let function = Value::Function(Rc::new(Vec::new()), ty, inner_ctx.block_slot);
                self.pop_frame(inner_ctx);
                // === Frame end ===

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

    fn resolve_read_for_frame(&mut self,
        name: &str,
        frame: usize,
        span: Span,
        ctx: Context,
    ) -> Result<(), ()> {
        if frame == 0 {
            for (slot, var) in self.stack[0].variables.iter().enumerate() {
                if var.active && &var.name == name {
                    let op = Op::ReadGlobal(slot);
                    self.add_op(ctx, span, op);
                    return Ok(());
                }
            }
        } else {
            for (slot, var) in self.stack[frame].variables.iter_mut().enumerate().rev() {
                if var.active && &var.name == name {
                    assert!(frame == ctx.frame, "Upvalues aren't implemented");
                    let op = Op::ReadLocal(slot);
                    self.add_op(ctx, span, op);
                    return Ok(());
                }
            }
        }
        Err(())
    }

    fn read_identifier(&mut self, name: &str, span: Span, ctx: Context) -> Context {
        for frame in (0..ctx.frame+1).into_iter().rev() {
            if self.resolve_read_for_frame(name, frame, span, ctx).is_ok() {
                return ctx;
            }
        }

        match self.namespaces[ctx.namespace].get(name) {
            Some(Name::Slot(slot)) => {
                let op = Op::Constant(*slot);
                self.add_op(ctx, span, op);
                return ctx;
            },
            Some(Name::Namespace(new_namespace)) => {
                return Context { namespace: *new_namespace, ..ctx }
            },
            Some(Name::Blob(blob)) => {
                let op = Op::Constant(*blob);
                self.add_op(ctx, span, op);
                return ctx;
            },
            None => {},
        }

        if let Some((slot, _)) = self.functions.get(name) {
            let slot = *slot;
            let op = self.constant(Value::ExternFunction(slot));
            self.add_op(ctx, span, op);
            return ctx;
        }

        error!(self, ctx, span, "No active variable called '{}' could be found", name);
        ctx
    }

    fn resolve_set_for_frame(&mut self,
        name: &str,
        frame: usize,
        span: Span,
        ctx: Context,
    ) -> Result<(), ()> {
        if frame == 0 {
            for (slot, var) in self.stack[0].variables.iter().enumerate() {
                if var.active && &var.name == name {
                    // NOTE(ed): In the global namespace - everyhing is legal before start:
                    if var.kind.immutable() && ctx.frame != 0 {
                        error!(self, ctx, span, "Cannot modify constant '{}'", var.name);
                    }
                    let op = Op::AssignGlobal(slot);
                    self.add_op(ctx, span, op);
                    return Ok(());
                }
            }
        } else {
            for (slot, var) in self.stack[frame].variables.iter_mut().enumerate().rev() {
                if var.active && &var.name == name {
                    assert!(frame == ctx.frame, "Upvalues aren't implemented");
                    if var.kind.immutable() {
                        error!(self, ctx, span, "Cannot modify constant '{}'", var.name);
                    }
                    let op = Op::AssignLocal(slot);
                    self.add_op(ctx, span, op);
                    return Ok(());
                }
            }
        }
        Err(())
    }


    fn set_identifier(&mut self, name: &str, span: Span, ctx: Context) {
        for frame in (0..ctx.frame+1).into_iter().rev() {
            if self.resolve_set_for_frame(name, frame, span, ctx).is_ok() {
                return;
            }
        }
        error!(self, ctx, span, "No active assignable value called '{}' could be found", name);
    }

    fn resolve_type(&self, ty: &syntree::Type, ctx: Context) -> Type {
        // TODO(ed): Implement this
        Type::Void
    }

    fn define(&mut self, name: &str, kind: VarKind, span: Span) -> VarSlot {
        // TODO(ed): Fix the types
        let stack = &mut self.stack.last_mut().unwrap().variables;
        let slot = stack.len();
        let var = Variable::new(name.to_string(), kind, Type::Unknown, slot, span);
        stack.push(var);
        slot
    }

    fn activate(&mut self, slot: VarSlot) {
        self.stack.last_mut().unwrap().variables[slot].active = true;
    }

    fn statement(&mut self, statement: &Statement, ctx: Context) {
        use StatementKind::*;
        self.panic = false;

        match &statement.kind {
            Use { .. }
            | EmptyStatement => {}

            Blob { name, fields } => {
                if let Some(Name::Blob(slot)) = self.namespaces[ctx.namespace].get(name) {
                    self.blobs[*slot].fields = fields
                        .iter()
                        .map(|(k, v)| (k.clone(), self.resolve_type(v, ctx)))
                        .collect();
                } else {
                    error!(self, ctx, statement.span, "No blob with the name '{}' in this namespace", name);
                }
            }

            Print { value } => {
                self.expression(value, ctx);
                self.add_op(ctx, statement.span, Op::Print);
            }

            Definition { ident, kind, ty, value } => {
                // TODO(ed): Don't use type here - type check the tree first.
                self.expression(value, ctx);

                if ctx.frame == 0 {
                    // Global
                    self.set_identifier(&ident.name, statement.span, ctx);
                } else {
                    // Local variable
                    let slot = self.define(&ident.name, *kind, statement.span);
                    let ty = self.resolve_type(ty, ctx);
                    let op = if let Op::Constant(ty) = self.constant(Value::Ty(ty)) {
                        if kind.force() {
                            Op::Define(ty)
                        } else {
                            Op::Force(ty)
                        }
                    } else {
                        error!(self, ctx, statement.span, "Failed to add type declaration");
                        Op::Illegal
                    };
                    self.add_op(ctx, statement.span, op);
                    self.activate(slot);
                }
            }

            Assignment { target, value, kind } => {
                use syntree::Op::*;
                use AssignableKind::*;

                let mutator = |kind|
                    match kind {
                        Add
                        | Sub
                        | Mul
                        | Div => true,
                        Nop => false,
                    }
                ;

                let write_mutator_op = |comp: &mut Self, ctx, kind| {
                    let op = match kind {
                        Add => { Op::Add }
                        Sub => { Op::Sub }
                        Mul => { Op::Mul }
                        Div => { Op::Div }
                        Nop => { return; }
                    };
                    comp.add_op(ctx, statement.span, op);
                };

                match &target.kind {
                    Read(ident) => {
                        if mutator(*kind) {
                            self.read_identifier(&ident.name, statement.span, ctx);
                        }
                        self.expression(value, ctx);

                        write_mutator_op(self, ctx, *kind);

                        self.set_identifier(&ident.name, statement.span, ctx);
                    }
                    Call(_, _) => {
                        error!(self, ctx, statement.span, "Cannot assign to result from function call");
                    }
                    Access(a, field) => {
                        self.assignable(a, ctx);
                        let slot = self.string(&field.name);

                        if mutator(*kind) {
                            self.add_op(ctx, statement.span, Op::Copy(1));
                            self.add_op(ctx, field.span, Op::GetField(slot));
                        }
                        self.expression(value, ctx);
                        write_mutator_op(self, ctx, *kind);

                        self.add_op(ctx, field.span, Op::AssignField(slot));
                    }
                    Index(a, b) => {
                        self.assignable(a, ctx);
                        self.expression(b, ctx);

                        if mutator(*kind) {
                            self.add_op(ctx, statement.span, Op::Copy(2));
                            self.add_op(ctx, statement.span, Op::GetIndex);
                        }
                        self.expression(value, ctx);
                        write_mutator_op(self, ctx, *kind);

                        self.add_op(ctx, statement.span, Op::AssignIndex);
                    }
                }
            }

            StatementExpression { value } => {
                self.expression(value, ctx);
                self.add_op(ctx, statement.span, Op::Pop);
            }

            Block { statements } => {
                let ss = self.stack[ctx.frame].variables.len();

                for statement in statements {
                    self.statement(statement, ctx);
                }

                while ss < self.stack[ctx.frame].variables.len() {
                    // TODO(ed): Upvalues
                    let var = self.stack[ctx.frame].variables.pop().unwrap();
                    if var.captured {
                        self.add_op(ctx, statement.span, Op::PopUpvalue);
                    } else {
                        self.add_op(ctx, statement.span, Op::Pop);
                    }
                }
            }

            Loop { condition, body } => {
                let start = self.next_ip(ctx);
                self.expression(condition, ctx);
                let jump_from = self.add_op(ctx, condition.span, Op::Illegal);
                self.statement(body, ctx);
                self.add_op(ctx, body.span, Op::Jmp(start));
                let out = self.next_ip(ctx);
                self.patch(ctx, jump_from, Op::JmpFalse(out));
            }

            If { condition, pass, fail } => {
                self.expression(condition, ctx);

                let jump_from = self.add_op(ctx, condition.span, Op::Illegal);
                self.statement(pass, ctx);
                let jump_out = self.add_op(ctx, condition.span, Op::Illegal);
                self.statement(fail, ctx);

                self.patch(ctx, jump_from, Op::JmpFalse(jump_out + 1));

                let end = self.next_ip(ctx);
                self.patch(ctx, jump_out, Op::Jmp(end));
            }

            Unreachable { } => {
                self.add_op(ctx, statement.span, Op::Unreachable);
            }

            Ret { value } => {
                self.expression(value, ctx);
                self.add_op(ctx, statement.span, Op::Return);
            }
        }
    }

    fn module(&mut self, module: &Module, ctx: Context) {
        for statement in module.statements.iter() {
            self.statement(statement, ctx);
        }
    }

    fn compile(mut self, tree: Prog, functions: &[(String, RustFunction)]) -> Result<crate::Prog, Vec<Error>> {
        assert!(!tree.modules.is_empty(), "Cannot compile an empty program");
        self.functions = functions
            .to_vec()
            .into_iter()
            .enumerate()
            .map(|(i, (s, f))| (s, (i, f)))
            .collect();

        let name = "/preamble/";
        self.blocks.push(Block::new(name, &tree.modules[0].0));
        self.stack.push(Frame::new(name, Span { line: 0 }));
        let ctx = Context {
            block_slot: self.blocks.len() - 1,
            frame: self.stack.len() - 1,
            ..Context::from_namespace(0)
        };

        //println!("{:#?}", tree);

        self.extract_globals(&tree);

        for (_, module) in tree.modules.iter().skip(1) {
            self.module(module, ctx);
        }
        let module = &tree.modules[0].1;
        self.module(module, ctx);

        self.read_identifier("start", Span { line: 0 }, ctx);
        self.add_op(ctx, Span { line: 0 }, Op::Call(0));

        let nil = self.constant(Value::Nil);
        self.add_op(ctx, module.span, nil);
        self.add_op(ctx, module.span, Op::Return);

        self.pop_frame(ctx);

        if self.errors.is_empty() {
            Ok(crate::Prog {
                blocks: self.blocks.into_iter().map(|x| Rc::new(RefCell::new(x))).collect(),
                functions: functions.iter().map(|(_, f)| *f).collect(),
                blobs: self.blobs,
                constants: self.constants,
                strings: self.strings,
            })
        } else {
            Err(self.errors)
        }
    }

    fn extract_globals(&mut self, tree: &Prog) {
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
                    error!(self, Context::from_namespace(slot),
                           Span { line: 0 }, "Reading module '{}' twice! How?", full_path.display());
                }
            }
        }

        self.namespace_id_to_path = path_to_namespace_id.iter().map(|(a, b)| (b.clone(), a.clone())).collect();

        for (path, module) in tree.modules.iter() {
            let path = path.file_stem().unwrap().to_str().unwrap();
            let slot = path_to_namespace_id[path];
            let ctx = Context::from_namespace(slot);
            for statement in module.statements.iter() {
                use StatementKind::*;
                let mut namespace = self.namespaces.remove(slot);
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
                                    ctx,
                                    span,
                                    "A global variable with the name '{}' already exists",
                                    name
                                );
                            }
                        }
                    }

                    Blob { name, .. } => {
                        match namespace.entry(name.to_owned()) {
                            Entry::Vacant(_) => {
                                let id = self.blobs.len();
                                self.blobs.push(crate::Blob::new_tree(id, slot, name));
                                let blob = self.constant(Value::Blob(id));
                                if let Op::Constant(slot) = blob {
                                    namespace.insert(name.to_owned(), Name::Blob(slot));
                                } else {
                                    unreachable!();
                                }
                            }

                            Entry::Occupied(_) => {
                                error!(
                                    self,
                                    ctx,
                                    statement.span,
                                    "A global variable with the name '{}' already exists", name
                                );
                            }
                        }
                    }

                    Definition { ident: Identifier { name, .. }, kind, ty, .. } => {
                        let var = self.define(name, *kind, statement.span);
                        self.activate(var);
                        let nil = self.constant(Value::Nil);
                        self.add_op(ctx, Span { line: 0 }, nil);

                        let ty = self.resolve_type(ty, ctx);
                        let op = if let Op::Constant(ty) = self.constant(Value::Ty(ty)) {
                            Op::Force(ty)
                        } else {
                            error!(self, ctx, statement.span, "Failed to resolve the type");
                            Op::Illegal
                        };
                        self.add_op(ctx, Span { line: 0 }, op);
                    }

                    _ => {
                        // TODO(ed): Throw error
                    }
                }
                self.namespaces.insert(slot, namespace);
            }
        }
    }
}


pub fn compile(prog: Prog, functions: &[(String, RustFunction)]) -> Result<crate::Prog, Vec<Error>> {
    Compiler::new().compile(prog, functions)
}
