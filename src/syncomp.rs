use crate::error::Error;
use crate::syntree;
use syntree::*;
use crate::{Op, Block, Value, Type};
use std::collections::{hash_map::Entry, HashMap};
use crate::rc::Rc;
use std::cell::RefCell;
use std::path::Path;

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

struct Compiler {
    globals: Vec<Variable>,
    blocks: Vec<Block>,

    // TODO(ed): Stackframes

    panic: bool,
    errors: Vec<Error>,

    strings: Vec<String>,
    constants: Vec<Value>,

    values: HashMap<Value, usize>,
}

macro_rules! compile_error {
    ($compiler:expr, $span:expr, $( $msg:expr ),+ ) => {
        if !$compiler.panic {
            $compiler.panic = true;

            let msg = format!($( $msg ),*).into();
            let err = Error::CompileError {
                file: $compiler.current_file().into(),
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
            globals: Vec::new(),
            blocks: Vec::new(),

            panic: false,
            errors: Vec::new(),

            strings: Vec::new(),
            constants: Vec::new(),

            values: HashMap::new(),
        }
    }

    fn current_file(&self) -> &Path {
        &self.blocks.last().expect("No blocks pushed").file
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

    fn assignable(&mut self, ass: &Assignable) {
        use AssignableKind::*;

        match &ass.kind {
            Read(ident) => {
                self.read(&ident.name, ass.span);
            }
            Call(a, expr) => {
                self.assignable(a);
                for expr in expr.iter() {
                    self.expression(expr);
                }
                self.add_op(ass.span, Op::Call(expr.len()));
            }
            Access(a, b) => {
                self.assignable(a);
                self.assignable(b);
            }
            Index(a, b) => {
                self.assignable(a);
                self.expression(b);
                self.add_op(ass.span, Op::GetIndex);
            }
        }
    }

    fn un_op(&mut self, a: &Expression, ops: &[Op], span: Span) {
        self.expression(&a);
        for op in ops {
            self.add_op(span, *op);
        }
    }

    fn bin_op(&mut self, a: &Expression, b: &Expression, ops: &[Op], span: Span) {
        self.expression(&a);
        self.expression(&b);
        for op in ops {
            self.add_op(span, *op);
        }
    }

    fn push(&mut self, value: Value, span: Span) {
        let value = self.constant(value);
        self.add_op(span, value);
    }

    fn expression(&mut self, expression: &Expression) {
        use ExpressionKind::*;

        match &expression.kind {
            Get(a) => self.assignable(a),

            Add(a, b) => self.bin_op(a, b, &[Op::Add], expression.span),
            Sub(a, b) => self.bin_op(a, b, &[Op::Sub], expression.span),
            Mul(a, b) => self.bin_op(a, b, &[Op::Mul], expression.span),
            Div(a, b) => self.bin_op(a, b, &[Op::Div], expression.span),

            Eq(a, b)   => self.bin_op(a, b, &[Op::Equal], expression.span),
            Neq(a, b)  => self.bin_op(a, b, &[Op::Equal, Op::Not], expression.span),
            Gt(a, b)   => self.bin_op(a, b, &[Op::Greater], expression.span),
            Gteq(a, b) => self.bin_op(a, b, &[Op::Less, Op::Not], expression.span),
            Lt(a, b)   => self.bin_op(a, b, &[Op::Less], expression.span),
            Lteq(a, b) => self.bin_op(a, b, &[Op::Greater, Op::Not], expression.span),

            AssertEq(a, b) => self.bin_op(a, b, &[Op::Equal, Op::Assert], expression.span),

            Neg(a) => self.un_op(a, &[Op::Neg], expression.span),

            In(a, b) => self.bin_op(a, b, &[Op::Contains], expression.span),

            And(a, b) => self.bin_op(a, b, &[Op::And], expression.span),
            Or(a, b)  => self.bin_op(a, b, &[Op::Or], expression.span),
            Not(a)    => self.un_op(a, &[Op::Neg], expression.span),

            // ...

            Tuple(x) | List(x) | Set(x) | Dict(x) => {
                for expr in x.iter() {
                    self.expression(expr);
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

            _ => { unimplemented!(); }
        }

    }

    fn read(&mut self, name: &String, span: Span) {
        for var in self.globals.iter().rev() {
            if var.active && &var.name == name {
                self.add_op(span, Op::ReadGlobal(var.slot));
                return;
            }
        }

        compile_error!(self, span, "No active variable called '{}' could be found", name);
    }

    fn set(&mut self, name: &String, span: Span) {
        for var in self.globals.iter().rev() {
            if var.active && &var.name == name {
                self.add_op(span, Op::AssignGlobal(var.slot));
                return;
            }
        }

        compile_error!(self, span, "No active variable called '{}' could be found", name);
    }

    fn define(&mut self, name: &String, kind: &VarKind, ty: &syntree::Type, span: Span) -> VarSlot {
        // TODO(ed): Fix the types
        // TODO(ed): Mutability
        // TODO(ed): Scoping
        let slot = self.globals.len();
        let var = Variable::new(name.clone(), Type::Unknown, slot, span);
        self.globals.push(var);
        slot
    }

    fn activate(&mut self, slot: VarSlot) {
        self.globals[slot].active = true;
    }

    fn statement(&mut self, statement: &Statement) {
        use StatementKind::*;

        match &statement.kind {
            EmptyStatement => {},

            Print { value } => {
                self.expression(value);
                self.add_op(statement.span, Op::Print);
            }

            Definition { ident, kind, ty, value } => {
                // TODO(ed): Don't use type here - type check the tree first.
                let slot = self.define(&ident.name, kind, ty, statement.span);
                self.expression(value);
                self.activate(slot);
            }

            Assignment { kind, target, value } => {
                use AssignableKind::*;

                match &target.kind {
                    Read(ident) => {
                        self.expression(value);
                        self.set(&ident.name, statement.span);
                    }
                    Call(a, expr) => {
                        compile_error!(self, statement.span, "Cannot assign to result from function call");
                    }
                    Access(a, b) => {
                        unimplemented!("Assignment to accesses is not implemented");
                    }
                    Index(a, b) => {
                        self.assignable(a);
                        self.expression(b);
                        self.expression(value);
                        self.add_op(statement.span, Op::AssignIndex);
                    }
                }

                self.expression(value);
            }

            StatementExpression { value } => {
                self.expression(value);
            }

            _ => { unimplemented!(); }
        }
    }

    fn module(&mut self, module: &Module) {
        for statement in module.statements.iter() {
            self.statement(statement);
        }
    }

    fn compile(mut self, tree: Prog) -> Result<crate::Prog, Vec<Error>> {
        assert!(!tree.modules.is_empty(), "Cannot compile an empty program");
        self.blocks.push(Block::new("/preamble/", &tree.modules[0].0));
        self.globals.push(Variable::filler());

        let module = &tree.modules[0].1;
        self.module(module);

        let nil = self.constant(Value::Int(1));
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
}


pub fn compile(prog: Prog) -> Result<crate::Prog, Vec<Error>> {
    Compiler::new().compile(prog)
}
