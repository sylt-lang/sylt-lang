use crate::error::Error;
use crate::syntree::*;
use crate::{Op, Block, Value, Type};
use std::collections::{hash_map::Entry, HashMap};
use crate::rc::Rc;
use std::cell::RefCell;
use std::path::Path;

struct Variable {
    name: String,
    typ: Type,
    slot: usize,
    line: usize,
}

struct Compiler {
    globals: Vec<Variable>,
    blocks: Vec<Block>,

    panic: bool,
    errors: Vec<Error>,

    strings: Vec<String>,
    constants: Vec<Value>,

    values: HashMap<Value, usize>,
}

macro_rules! compile_error {
    ($compiler:expr, $tree:expr, $( $msg:expr ),+ ) => {
        if !$compiler.panic {
            $compiler.panic = true;

            let msg = format!($( $msg ),*).into();
            let err = Error::CompileError {
                file: $compiler.current_file().into(),
                line: $tree.span,
                message: Some(msg),
            };
            $compiler.errors.push(err);
        }
    };
    ($compiler:expr, $( $msg:expr ),+ ) => {
        if !$compiler.panic {
            $compiler.panic = true;

            let msg = format!($( $msg ),*).into();
            let err = Error::CompileError {
                file: $compiler.current_file().into(),
                line: 0,
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

            Float(a) => self.push(Value::Float(*a), expression.span),
            Bool(a)  => self.push(Value::Bool(*a), expression.span),
            Int(a)   => self.push(Value::Int(*a), expression.span),
            Str(a)   => self.push(Value::String(Rc::new(a.clone())), expression.span),
            Nil      => self.push(Value::Nil, expression.span),

            _ => { unimplemented!(); }
        }

    }

    fn statement(&mut self, statement: &Statement) {
        use StatementKind::*;

        match &statement.kind {
            EmptyStatement => {},

            Print { value } => {
                self.expression(value);
                self.add_op(statement.span, Op::Print);
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
