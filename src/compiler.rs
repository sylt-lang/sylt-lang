use std::path::{Path, PathBuf};
use std::cell::RefCell;
use std::collections::{HashMap, hash_map::Entry};
use std::rc::Rc;

use crate::{Blob, Block, Op, Prog, RustFunction, Type, Value};
use crate::error::{Error, ErrorKind};
use crate::sectionizer::Section;
use crate::tokenizer::Token;

macro_rules! nextable_enum {
    ( $name:ident { $( $thing:ident ),* $( , )? } ) => {
        #[derive(PartialEq, PartialOrd, Clone, Copy, Debug)]
        enum $name {
            $( $thing, )*
        }

        impl $name {
            pub fn next(&self) -> Self {
                *[$( $name::$thing, )*].iter()
                    .find(|x| { x > &self })
                    .unwrap_or(self)
            }
        }
    };
}

macro_rules! error {
    ($thing:expr, $msg:expr) => {
        $thing.error(ErrorKind::SyntaxError($thing.line(), $thing.peek()), Some(String::from($msg)))
    };
}

macro_rules! expect {
    ($thing:expr, $exp_head:pat $( | $exp_rest:pat ),* , $msg:expr) => {
        match $thing.peek() {
            $exp_head $( | $exp_rest )* => { $thing.eat(); true },
            _ => { error!($thing, $msg); false } ,
        }
    };
}

// NOTE(ed): This can cause some strange bugs. It would be nice if we could
// remove this function, but to do that we need to rewrite some code. Like
// tuples and fields. Might be worth it tough.
macro_rules! parse_branch {
    ($compiler:expr, $block:expr, [ $( $call:expr ),* ]) => {
        {
            let block_length = $block.ops.len();
            let token_length = $compiler.current_token;
            let num_errors = $compiler.errors.len();
            let mut stored_errors = Vec::new();

            // Loop for early return on success.
            let success = loop {
                // We risk getting a lot of errors if we are in an invalid state
                // when we start the parse.
                if $compiler.panic {
                    break false;
                }
                $(
                    $call;
                    if !$compiler.panic {
                        break true;
                    }
                    $compiler.panic = false;
                    $compiler.current_token = token_length;
                    let thrown_errors = $compiler.errors.len() - num_errors - 1;
                    stored_errors.extend($compiler.errors.split_off(thrown_errors));
                    $block.ops.truncate(block_length);
                )*
                break false;
            };

            if !success {
                $compiler.errors.extend(stored_errors);
            }
            success
        }

    };

    ($compiler:expr, $block:expr, $call:expr) => {
        {
            let block_length = $block.ops.len();
            let token_length = $compiler.current_token;
            let num_errors = $compiler.errors.len();
            let mut stored_errors = Vec::new();
            // Closures for early return on success.
            loop {
                // We risk getting a lot of errors if we are in an invalid state
                // when we start the parse.
                if $compiler.panic {
                    break false;
                }
                $call;
                if !$compiler.panic {
                    break true;
                }
                $compiler.panic = false;
                $compiler.current_token = token_length;
                let thrown_errors = $compiler.errors.len() - num_errors - 1;
                stored_errors.extend($compiler.errors.split_off(thrown_errors));
                $block.ops.truncate(block_length);
                break false;
            }
        }
    };
}

macro_rules! push_frame {
    ($compiler:expr, $block:expr, $code:tt) => {
        {
            $compiler.frames_mut().push(Frame::new());

            // Return value stored as a variable
            let var = Variable::new("", true, Type::Unknown);
            $compiler.define(var).unwrap();

            $code

            let frame = $compiler.frames_mut().pop().unwrap();
            // 0-th slot is the function itself.
            for var in frame.stack.iter().skip(1) {
                if !(var.read || var.upvalue) {
                    let e = ErrorKind::SyntaxError(
                        var.line,
                        Token::Identifier(var.name.clone()
                    ));
                    $compiler.error_on_line(
                        e,
                        var.line,
                        Some(format!("Unused value '{}'.", var.name))
                    );
                }
                $compiler.panic = false;
            }
            // The 0th slot is the return value, which is passed out
            // from functions, and should not be popped.
            0
        }
    };
}

macro_rules! push_scope {
    ($compiler:expr, $block:expr, $code:tt) => {
        let ss = $compiler.stack().len();
        $compiler.frame_mut().scope += 1;

        $code;

        $compiler.frame_mut().scope -= 1;

        let mut errors = Vec::new();
        for var in $compiler.frame().stack.iter().skip(ss).rev() {
            if !(var.read || var.upvalue) {
                let e = ErrorKind::SyntaxError(
                    var.line,
                    Token::Identifier(var.name.clone()
                ));
                errors.push((
                    e,
                    var.line,
                    format!("Usage of undefined value: '{}'.", var.name),)
                );
            }
            if var.captured {
                add_op($compiler, $block, Op::PopUpvalue);
            } else {
                add_op($compiler, $block, Op::Pop);
            }
        }

        for (e, l, m) in errors.iter() {
            $compiler.error_on_line(e.clone(), *l, Some(m.clone()));
            $compiler.panic = false;
        }
        $compiler.stack_mut().truncate(ss);
    };
}

nextable_enum!(Prec {
    No,
    Assert,
    BoolOr,
    BoolAnd,
    Comp,
    Term,
    Factor,
    Index,
});

#[derive(Clone, Debug)]
struct Variable {
    name: String,
    typ: Type,
    scope: usize,
    slot: usize,
    line: usize,

    outer_slot: usize,
    outer_upvalue: bool,

    active: bool,
    upvalue: bool,
    captured: bool,
    mutable: bool,
    read: bool,
}

impl Variable {
    fn new(name: &str, mutable: bool, typ: Type) -> Self {
        Self {
            name: String::from(name),
            typ,
            scope: 0,
            slot: 0,
            line: 0,

            outer_slot: 0,
            outer_upvalue: false,

            active: false,
            upvalue: false,
            captured: false,
            mutable,
            read: false,
        }
    }
}

#[derive(Debug)]
enum LoopOp {
    Continue,
    Break,
}

#[derive(Debug)]
struct Frame {
    loops: Vec<Vec<(usize, usize, LoopOp)>>,
    stack: Vec<Variable>,
    upvalues: Vec<Variable>,
    scope: usize,
}

impl Frame {
    fn new() -> Self {
        Self {
            loops: Vec::new(),
            stack: Vec::new(),
            upvalues: Vec::new(),
            scope: 0,
        }
    }

    fn push_loop(&mut self) {
        self.loops.push(Vec::new());
    }

    fn pop_loop(&mut self, block: &mut Block, stacktarget: usize, start: usize, end: usize) {
        // Compiler error if this fails
        for (addr, stacksize, op) in self.loops.pop().unwrap().iter() {
            let to_pop = stacksize - stacktarget;
            let op = match op {
                LoopOp::Continue => Op::JmpNPop(start, to_pop),
                LoopOp::Break => Op::JmpNPop(end, to_pop),
            };
            block.patch(op, *addr);
        }
    }

    fn add_continue(&mut self, addr: usize, stacksize: usize) -> Result<(), ()> {
        if let Some(top) = self.loops.last_mut() {
            top.push((addr, stacksize, LoopOp::Continue));
            Ok(())
        } else {
            Err(())
        }
    }

    fn add_break(&mut self, addr: usize, stacksize: usize) -> Result<(), ()> {
        if let Some(top) = self.loops.last_mut() {
            top.push((addr, stacksize, LoopOp::Break));
            Ok(())
        } else {
            Err(())
        }
    }

    fn find_outer(&self, name: &str) -> Option<Variable> {
        // Only really makes sense in the outermost frame
        // where declaration order doesn't matter
        for var in self.stack.iter().rev() {
            if var.name == name {
                return Some(var.clone());
            }
        }
        None
    }

    fn find_local(&self, name: &str) -> Option<Variable> {
        for var in self.stack.iter().rev() {
            if var.name == name && var.active {
                return Some(var.clone());
            }
        }
        None
    }

    fn find_upvalue(&self, name: &str) -> Option<Variable> {
        for var in self.upvalues.iter().rev() {
            if var.name == name && var.active {
                return Some(var.clone());
            }
        }
        None
    }

    fn add_upvalue(&mut self, variable: Variable) -> Variable {
        let new_variable = Variable {
            outer_upvalue: variable.upvalue,
            outer_slot: variable.slot,
            slot: self.upvalues.len(),
            active: true,
            upvalue: true,
            ..variable
        };
        self.upvalues.push(new_variable.clone());
        new_variable
    }
}

type Namespace = HashMap<String, Name>;

struct CompilerContext {
    frames: Vec<Frame>,
    namespace: Namespace,
}

impl CompilerContext {
    fn new() -> Self {
        Self {
            frames: vec![Frame::new()],
            namespace: Namespace::new(),
        }
    }
}

#[derive(Debug, Clone)]
enum Name {
    Slot(usize, usize),
    Unknown(usize, usize),
    Namespace(PathBuf),
}

pub(crate) struct Compiler {
    current_token: usize,
    current_section: usize,
    sections: Vec<Section>,

    contextes: HashMap<PathBuf, CompilerContext>,

    panic: bool,
    errors: Vec<Error>,

    blocks: Vec<Rc<RefCell<Block>>>,
    blob_id: usize,

    functions: HashMap<String, (usize, RustFunction)>,

    strings: Vec<String>,

    constants: Vec<Value>,
    values: HashMap<Value, usize>,
}

/// Helper function for adding operations to the given block.
fn add_op(compiler: &Compiler, block: &mut Block, op: Op) -> usize {
    block.add(op, compiler.line())
}

impl Compiler {
    pub(crate) fn new(sections: Vec<Section>) -> Self {
        let contextes = sections
            .iter()
            .map(|section| (section.path.to_path_buf(), CompilerContext::new()))
            .collect();

        Self {
            current_token: 0,
            current_section: 0,
            sections,

            contextes,

            panic: false,
            errors: vec![],

            blocks: Vec::new(),
            blob_id: 0,

            functions: HashMap::new(),

            strings: Vec::new(),

            constants: vec![],
            values: HashMap::new(),
        }
    }

    fn new_blob_id(&mut self) -> usize {
        let id = self.blob_id;
        self.blob_id += 1;
        id
    }

    fn add_namespace(&mut self, name: String) {
        let path = Path::new(&format!("{}.sy", name)).to_path_buf();
        match self.names_mut().entry(name.clone()) {
            Entry::Vacant(v) => {
                v.insert(Name::Namespace(path));
            }
            Entry::Occupied(_) => {
                error!(self, format!("Namespace {} already present.", name));
            }
        }
    }

    fn add_constant(&mut self, value: Value) -> usize {
        if matches!(value, Value::Float(_)
                         | Value::Int(_)
                         | Value::Bool(_)
                         | Value::String(_)
                         | Value::Tuple(_)
                         | Value::Nil)
        {
            let entry = self.values.entry(value.clone());
            if let Entry::Occupied(entry) = entry {
                *entry.get()
            } else {
                let slot = self.constants.len();
                self.constants.push(value);
                entry.or_insert(slot);
                slot
            }
        } else {
            self.constants.push(value);
            self.constants.len() - 1
        }
    }

    fn intern_string(&mut self, string: String) -> usize {
        self.strings.push(string);
        self.strings.len() - 1
    }

    fn section(&self) -> &Section {
        &self.sections[self.current_section]
    }

    fn current_file(&self) -> &Path {
        &self.section().path
    }

    fn current_context(&self) -> &CompilerContext {
        self.contextes.get(self.current_file()).unwrap()
    }

    fn current_context_mut(&mut self) -> &mut CompilerContext {
        let file = self.current_file().to_path_buf();
        self.contextes.get_mut(&file).unwrap()
    }

    fn frame(&self) -> &Frame {
        self.current_context().frames.last().unwrap()
    }

    fn frame_mut(&mut self) -> &mut Frame {
        self.current_context_mut().frames.last_mut().unwrap()
    }

    fn frames(&self) -> &[Frame] {
        &self.current_context().frames
    }

    fn frames_mut(&mut self) -> &mut Vec<Frame> {
        &mut self.current_context_mut().frames
    }

    fn names(&self) -> &Namespace {
        &self.current_context().namespace
    }

    fn names_mut(&mut self) -> &mut Namespace {
        &mut self.current_context_mut().namespace
    }

    /// Marks a variable as read. Also marks upvalues.
    fn mark_read(&mut self, frame_id: usize, var: &Variable) {
        // Early out
        if var.read {
            return;
        }

        match self.frames()[frame_id].upvalues.get(var.slot) {
            Some(up) if up.name == var.name => {
                let mut inner_var = self.frames()[frame_id].upvalues[var.slot].clone();
                inner_var.slot = inner_var.outer_slot;
                self.mark_read(frame_id - 1, &inner_var);
                self.frames_mut()[frame_id].upvalues[var.slot].read = true;
            }
            _ => {
                self.frames_mut()[frame_id].stack[var.slot].read = true;
            }
        }
    }

    fn stack(&self) -> &[Variable] {
        &self.frame().stack.as_ref()
    }

    fn stack_mut(&mut self) -> &mut Vec<Variable> {
        &mut self.frame_mut().stack
    }

    /// Used to recover from a panic so the rest of the code can be parsed.
    fn clear_panic(&mut self) {
        if self.panic {
            self.panic = false;

            while match self.peek() {
                Token::EOF | Token::Newline => false,
                _ => true,
            } {
                self.eat();
            }
            self.eat();
        }
    }

    fn error(&mut self, kind: ErrorKind, message: Option<String>) {
        self.error_on_line(kind, self.line(), message);
    }

    fn error_on_line(&mut self, kind: ErrorKind, line: usize, message: Option<String>) {
        if self.panic { return }
        self.panic = true;
        self.errors.push(Error {
            kind,
            file: self.current_file().to_path_buf(),
            line,
            message,
        });
    }

    fn init_section(&mut self, section: usize) {
        self.current_token = 0;
        self.current_section = section;
    }

    fn peek(&self) -> Token {
        self.peek_at(0)
    }

    fn peek_at(&self, at: usize) -> Token {
        if self.section().tokens.len() <= self.current_token + at {
            crate::tokenizer::Token::EOF
        } else {
            self.section().tokens[self.current_token + at].0.clone()
        }
    }

    // TODO(ed): Const generics
    fn peek_four(&self) -> (Token, Token, Token, Token) {
        (self.peek_at(0), self.peek_at(1), self.peek_at(2), self.peek_at(3))
    }

    fn eat(&mut self) -> Token {
        let t = self.peek();
        self.current_token += 1;
        match t {
            Token::GitConflictBegin => {
                self.current_token -= 1;
                let start = self.line();
                self.current_token += 1;
                while !matches!(self.eat(), Token::GitConflictEnd) {}
                self.panic = false;
                self.error_on_line(ErrorKind::GitConflictError(start, self.line()), start, None);
                self.panic = true;
            }
            _ => {}
        }
        t
    }

    /// The line of the current token.
    fn line(&self) -> usize {
        if self.section().tokens.len() == 0 {
            // unreachable!("An error occured without a section.");
            666666
        } else {
            self.section().tokens[std::cmp::min(self.current_token, self.section().tokens.len() - 1)].1
        }
    }

    fn precedence(&self, token: Token) -> Prec {
        match token {
            Token::LeftBracket => Prec::Index,

            Token::Star | Token::Slash => Prec::Factor,

            Token::Minus | Token::Plus => Prec::Term,

            Token::EqualEqual
                | Token::Greater
                | Token::GreaterEqual
                | Token::Less
                | Token::LessEqual
                | Token::NotEqual
                => Prec::Comp,

            Token::And => Prec::BoolAnd,
            Token::Or => Prec::BoolOr,

            Token::AssertEqual => Prec::Assert,

            _ => Prec::No,
        }
    }

    fn prefix(&mut self, token: Token, block: &mut Block) -> bool {
        match token {
            Token::Identifier(_) => self.variable_expression(block),
            Token::LeftParen => self.grouping_or_tuple(block),
            Token::Minus => self.unary(block),

            Token::Float(_) => self.value(block),
            Token::Int(_) => self.value(block),
            Token::Bool(_) => self.value(block),
            Token::String(_) => self.value(block),

            Token::Bang => self.unary(block),

            _ => { return false; },
        }
        return true;
    }

    fn infix(&mut self, token: Token, block: &mut Block) -> bool {
        match token {
            Token::Minus
                | Token::Plus
                | Token::Slash
                | Token::Star
                | Token::AssertEqual
                | Token::EqualEqual
                | Token::Greater
                | Token::GreaterEqual
                | Token::Less
                | Token::LessEqual
                | Token::NotEqual
                => self.binary(block),

            Token::And | Token::Or
                => self.binary_bool(block),

            Token::LeftBracket => self.index(block),

            _ => { return false; },
        }
        return true;
    }

    fn value(&mut self, block: &mut Block) {
        let value = match self.eat() {
            Token::Float(f) => { Value::Float(f) },
            Token::Int(i) => { Value::Int(i) }
            Token::Bool(b) => { Value::Bool(b) }
            Token::String(s) => { Value::String(Rc::from(s)) }
            _ => { error!(self, "Cannot parse value."); Value::Bool(false) }
        };
        let constant = self.add_constant(value);
        add_op(self, block, Op::Constant(constant));
    }

    fn grouping_or_tuple(&mut self, block: &mut Block) {
        parse_branch!(self, block, [self.tuple(block), self.grouping(block)]);
    }

    fn tuple(&mut self, block: &mut Block) {
        expect!(self, Token::LeftParen, "Expected '(' at start of tuple.");

        let mut num_args = 0;
        let trailing_comma = loop {
            match self.peek() {
                Token::RightParen | Token::EOF => {
                    break false;
                }
                Token::Newline => {
                    self.eat();
                }
                Token::Comma => {
                    //TODO(gu): This creates a lot of syntax errors since the compiler panic is
                    // ignored and the statement is tried as a grouping instead, even though we
                    // _know_ that this can't be parsed as a grouping either.
                    // Tracked in #100.
                    error!(self, "Tuples must begin with an element or ')'.");
                    return;
                }
                _ => {
                    self.expression(block);
                    num_args += 1;
                    match self.peek() {
                        Token::Comma => {
                            self.eat();
                            if matches!(self.peek(), Token::RightParen) {
                                break true;
                            }
                        },
                        Token::RightParen => {},
                        _ => {
                            error!(self, "Expected ',' or ')' after tuple element.");
                            return;
                        },
                    }
                }
            }
        };
        if num_args == 1 && !trailing_comma {
            error!(self, "A tuple with 1 element must end with a trailing comma.");
            return;
        }

        expect!(self, Token::RightParen, "Expected ')' after tuple.");
        add_op(self, block, Op::Tuple(num_args));
    }

    fn grouping(&mut self, block: &mut Block) {
        expect!(self, Token::LeftParen, "Expected '(' around expression.");

        self.expression(block);

        expect!(self, Token::RightParen, "Expected ')' around expression.");
    }

    fn index(&mut self, block: &mut Block) {
        expect!(self, Token::LeftBracket, "Expected '[' around index.");

        self.expression(block);
        add_op(self, block, Op::Index);

        expect!(self, Token::RightBracket, "Expected ']' around index.");
    }

    fn unary(&mut self, block: &mut Block) {
        let op = match self.eat() {
            Token::Minus => Op::Neg,
            Token::Bang => Op::Not,
            _ => { error!(self, "Invalid unary operator"); Op::Neg },
        };
        self.parse_precedence(block, Prec::Factor);
        add_op(self, block, op);
    }

    fn binary_bool(&mut self, block: &mut Block) {
        let op = self.eat();

        match op {
            Token::And => {
                add_op(self, block, Op::Copy);
                let jump = add_op(self, block, Op::Illegal);

                self.parse_precedence(block, self.precedence(op.clone()).next());

                block.patch(Op::JmpFalse(block.curr()), jump);
            }

            Token::Or => {
                add_op(self, block, Op::Copy);
                let skipp = add_op(self, block, Op::Illegal);
                let jump = add_op(self, block, Op::Illegal);
                block.patch(Op::JmpFalse(block.curr()), skipp);

                self.parse_precedence(block, self.precedence(op.clone()).next());

                block.patch(Op::Jmp(block.curr()), jump);
            }

            _ => { error!(self, "Illegal operator"); }
        }
    }

    fn binary(&mut self, block: &mut Block) {
        let op = self.eat();

        self.parse_precedence(block, self.precedence(op.clone()).next());

        let op: &[Op] = match op {
            Token::Plus => &[Op::Add],
            Token::Minus => &[Op::Sub],
            Token::Star => &[Op::Mul],
            Token::Slash => &[Op::Div],
            Token::AssertEqual => &[Op::Equal, Op::Assert],
            Token::EqualEqual => &[Op::Equal],
            Token::Less => &[Op::Less],
            Token::Greater => &[Op::Greater],
            Token::NotEqual => &[Op::Equal, Op::Not],
            Token::LessEqual => &[Op::Greater, Op::Not],
            Token::GreaterEqual => &[Op::Less, Op::Not],
            _ => { error!(self, "Illegal operator"); &[] }
        };
        block.add_from(op, self.line());
    }

    /// Entry point for all expression parsing.
    fn expression(&mut self, block: &mut Block) {
        match self.peek_four() {
            (Token::Fn, ..) => { self.function(block, None); },
            _ => self.parse_precedence(block, Prec::No),
        }
    }

    fn parse_precedence(&mut self, block: &mut Block, precedence: Prec) {
        if !self.prefix(self.peek(), block) {
            error!(self, "Invalid expression.");
        }

        while precedence <= self.precedence(self.peek()) {
            if !self.infix(self.peek(), block) {
                break;
            }
        }
    }

    fn find_namespace(&self, name: &str) -> Option<&Namespace> {
        match self.names().get(name) {
            Some(Name::Namespace(path)) => Some(&self.contextes.get(path).unwrap().namespace),
            _ => None,
        }
    }

    fn find_and_capture_variable<'i, I>(name: &str, mut iterator: I) -> Option<Variable>
    where I: Iterator<Item = &'i mut Frame> {
        if let Some(frame) = iterator.next() {
            if let Some(res) = frame.find_local(name) {
                frame.stack[res.slot].captured = true;
                return Some(res);
            }
            if let Some(res) = frame.find_upvalue(name) {
                return Some(res);
            }

            if let Some(res) = Self::find_and_capture_variable(name, iterator) {
                return Some(frame.add_upvalue(res));
            }
        }
        None
    }

    fn find_extern_function(&self, name: &str) -> Option<usize> {
        self.functions.get(name).map(|(i, _)| *i)
    }

    fn find_variable(&mut self, name: &str) -> Option<Variable> {
        if let Some(res) = self.frame().find_local(name) {
            return Some(res);
        }

        if let Some(res) = self.frame().find_upvalue(name) {
            return Some(res);
        }

        Self::find_and_capture_variable(name, self.frames_mut().iter_mut().rev())
    }

    fn find_constant(&mut self, name: &str) -> usize {
        match self.names_mut().entry(name.to_string()) {
            Entry::Occupied(entry) => {
                match entry.get() {
                    Name::Slot(i, _) => { return *i; },
                    Name::Unknown(i, _) => { return *i; },
                    _ => {
                        error!(self, format!("Tried to find constant '{}' but it was a namespace.", name));
                        return 0;
                    }
                }
            },
            Entry::Vacant(_) => {},
        };

        let slot = self.add_constant(Value::Unknown);
        let line = self.line();
        self.names_mut().insert(name.to_string(), Name::Unknown(slot, line));
        slot
    }

    fn named_constant(&mut self, name: String, value: Value) -> usize {
        let line = self.line();
        match self.names_mut().entry(name.clone()) {
            Entry::Occupied(mut entry) => {
                let slot = if let Name::Unknown(slot, _) = entry.get() {
                    *slot
                } else {
                    error!(self, format!("Constant named \"{}\" already has a value.", name));
                    return 0;
                };
                entry.insert(Name::Slot(slot, line));
                self.constants[slot] = value;
                return slot;
            },
            Entry::Vacant(_) => {},
        }
        let slot = self.add_constant(value);
        self.names_mut().insert(name, Name::Slot(slot, line));
        slot
    }

    fn forward_constant(&mut self, name: String) -> usize {
        let line = self.line();
        let slot = self.add_constant(Value::Unknown);
        match self.names_mut().entry(name.clone()) {
            Entry::Occupied(_) => {
                error!(self, format!("Constant named \"{}\" already has a value.", name));
                0
            },
            Entry::Vacant(entry) => {
                entry.insert(Name::Unknown(slot, line));
                slot
            },
        }
    }

    fn call_maybe(&mut self, block: &mut Block) -> bool {
        if matches!(self.peek(), Token::Bang | Token::LeftParen) {
            self.call(block);
            true
        } else {
            false
        }
    }

    fn call(&mut self, block: &mut Block) {
        let mut arity = 0;
        match self.peek() {
            Token::LeftParen => {
                self.eat();
                loop {
                    match self.peek() {
                        Token::EOF => {
                            error!(self, "Unexpected EOF in function call.");
                            break;
                        }
                        Token::RightParen => {
                            self.eat();
                            break;
                        }
                        _ => {
                            self.expression(block);
                            arity += 1;
                            if !matches!(self.peek(), Token::RightParen) {
                                expect!(self, Token::Comma, "Expected ',' after argument.");
                            }
                        }
                    }
                    if self.panic {
                        break;
                    }
                }
            },

            Token::Bang => {
                self.eat();
                loop {
                    match self.peek() {
                        Token::EOF => {
                            error!(self, "Unexpected EOF in function call.");
                            break;
                        }
                        Token::Newline => {
                            break;
                        }
                        _ => {
                            if !parse_branch!(self, block, self.expression(block)) {
                                break;
                            }
                            arity += 1;
                            if matches!(self.peek(), Token::Comma) {
                                self.eat();
                            }
                        }
                    }
                    if self.panic {
                        break;
                    }
                }
            }

            _ => {
                error!(self, "Invalid function call. Expected '!' or '('.");
            }
        }

        add_op(self, block, Op::Call(arity));
    }

    // TODO(ed): de-complexify
    fn function(&mut self, block: &mut Block, in_name: Option<&str>) {
        expect!(self, Token::Fn, "Expected 'fn' at start of function.");

        let name = if let Some(name) = in_name {
            String::from(name)
        } else {
            format!("λ {}@{:03}", self.current_file().display(), self.line())
        };

        let mut args = Vec::new();
        let mut return_type = Type::Void;
        let mut function_block = Block::new(&name, self.current_file());

        let block_id = self.blocks.len();
        let temp_block = Block::new(&name, self.current_file());
        self.blocks.push(Rc::new(RefCell::new(temp_block)));

        let _ret = push_frame!(self, function_block, {
            loop {
                match self.peek() {
                    Token::Identifier(name) => {
                        self.eat();
                        expect!(self, Token::Colon, "Expected ':' after parameter name.");
                        if let Ok(typ) = self.parse_type() {
                            args.push(typ.clone());
                            let mut var = Variable::new(&name, true, typ);
                            var.read = true;
                            if let Ok(slot) = self.define(var) {
                                self.stack_mut()[slot].active = true;
                            }
                        } else {
                            error!(self, "Failed to parse parameter type.");
                        }
                        if !matches!(self.peek(), Token::Arrow | Token::LeftBrace) {
                            expect!(self, Token::Comma, "Expected ',' after parameter.");
                        }
                    }
                    Token::LeftBrace => {
                        break;
                    }
                    Token::Arrow => {
                        self.eat();
                        if let Ok(typ) = self.parse_type() {
                            return_type = typ;
                        } else {
                            error!(self, "Failed to parse return type.");
                        }
                        break;
                    }
                    _ => {
                        error!(self, "Expected '->' or more paramters in function definition.");
                        break;
                    }
                }
            }

            self.scope(&mut function_block);

            for var in self.frame().upvalues.iter() {
                function_block.upvalues.push((var.outer_slot, var.outer_upvalue, var.typ.clone()));
            }
        });

        let nil = self.add_constant(Value::Nil);
        for op in function_block.ops.iter().rev() {
            match op {
                Op::Pop | Op::PopUpvalue => {}
                Op::Return => { break; } ,
                _ => {
                    add_op(self, &mut function_block, Op::Constant(nil));
                    add_op(self, &mut function_block, Op::Return);
                    break;
                }
            }
        }

        if function_block.ops.is_empty() {
            add_op(self, &mut function_block, Op::Constant(nil));
            add_op(self, &mut function_block, Op::Return);
        }

        function_block.ty = Type::Function(args, Box::new(return_type));
        let function_block = Rc::new(RefCell::new(function_block));

        // Note(ed): We deliberately add the constant as late as possible.
        // This behaviour is used in `constant_statement`.
        let function = Value::Function(Vec::new(), Rc::clone(&function_block));
        self.blocks[block_id] = function_block;
        let constant = if in_name.is_some() {
            self.named_constant(name, function)
        } else {
            self.add_constant(function)
        };
        add_op(self, block, Op::Constant(constant));
    }

    fn variable_expression(&mut self, block: &mut Block) {
        let name = match self.peek() {
            Token::Identifier(name) => name,
            _ => unreachable!(),
        };

        if let Some(_) = self.find_namespace(&name) {
            self.eat();
            // TODO(ed): This is a clone I would love to get rid of...
            let mut namespace = self.find_namespace(&name).unwrap().clone();
            loop {
                if self.eat() != Token::Dot {
                    error!(self, "Expect '.' after namespace.");
                    return;
                }
                if let Token::Identifier(field) = self.eat() {
                    match namespace.get(&field) {
                        Some(Name::Slot(slot, _)) | Some(Name::Unknown(slot, _)) => {
                            add_op(self, block, Op::Constant(*slot));
                            self.call_maybe(block);
                            return;
                        }
                        Some(Name::Namespace(inner_name)) => {
                            namespace = self.contextes
                                .get(inner_name)
                                .unwrap().namespace
                                .clone();
                        }
                        _ => {
                            error!(self, "Invalid namespace field.");
                        }
                    }
                } else {
                    error!(self, "Expected fieldname after '.'.");
                }
            }
        }

        self.eat();

        // Global functions take precedence
        if let Some(slot) = self.find_extern_function(&name) {
            let string = self.add_constant(Value::ExternFunction(slot));
            add_op(self, block, Op::Constant(string));
            self.call(block);
            return;
        }

        // Variables
        if let Some(var) = self.find_variable(&name) {
            self.mark_read(self.frames().len() - 1, &var);
            if var.upvalue {
                add_op(self, block, Op::ReadUpvalue(var.slot));
            } else {
                add_op(self, block, Op::ReadLocal(var.slot));
            }
            loop {
                match self.peek() {
                    Token::Dot => {
                        self.eat();
                        if let Token::Identifier(field) = self.eat() {
                            let string = self.intern_string(String::from(field));
                            add_op(self, block, Op::Get(string));
                        } else {
                            error!(self, "Expected fieldname after '.'.");
                            return;
                        }
                    }
                    _ => {
                        if !self.call_maybe(block) {
                            return;
                        }
                    }
                }
            }
        }

        // Blobs - Always returns a blob since it's filled in if it isn't used.
        let con = self.find_constant(&name);
        add_op(self, block, Op::Constant(con));
        self.call_maybe(block);
    }

    fn define(&mut self, mut var: Variable) -> Result<usize, ()> {
        let frame = self.frame();

        if let Some(res) = frame.find_local(&var.name).or(frame.find_upvalue(&var.name)) {
            if res.scope == frame.scope {
                error!(self, format!("Multiple definitions of '{}' in this block.",
                                     res.name));
                return Err(());
            }
        }

        let slot = self.stack().len();
        var.slot = slot;
        var.scope = frame.scope;
        var.line = self.line();
        self.stack_mut().push(var);
        Ok(slot)
    }

    fn definition_statement(&mut self, name: &str, typ: Type, block: &mut Block) {
        if self.frames().len() <= 1 {
            // Global
            let var = self.frame().find_outer(name)
                .expect(&format!("Couldn't find variable '{}' during prepass.", name));
            assert!(var.mutable);

            self.expression(block);
            self.stack_mut()[var.slot].active = true;
        } else {
            // Local
            let var = Variable::new(name, true, typ.clone());
            let slot = self.define(var);
            self.expression(block);
            let constant = self.add_constant(Value::Ty(typ));
            add_op(self, block, Op::Define(constant));

            if let Ok(slot) = slot {
                self.stack_mut()[slot].active = true;
            }
        }
    }

    fn constant_statement(&mut self, name: &str, typ: Type, block: &mut Block) {
        // Magical global constants
        if self.frames().len() <= 1 && self.peek() == Token::Fn {
            self.function(block, Some(name));
            // Remove the function, since it's a constant and we already
            // added it.
            block.ops.pop().unwrap();
            let slot = self.find_constant(name);
            add_op(self, block, Op::Link(slot));
            if let Value::Function(_, block) = &self.constants[slot] {
                block.borrow_mut().mark_constant();
            } else {
                unreachable!();
            }
            return;
        }

        if self.frames().len() <= 1 {
            // Global
            let var = self.frame().find_outer(name)
                .expect(&format!("Couldn't find constant '{}' during prepass.", name));
            assert!(!var.mutable);

            self.expression(block);
            self.stack_mut()[var.slot].active = true;
        } else {
            // Local
            let var = Variable::new(name, false, typ);
            let slot = self.define(var);
            self.expression(block);

            if let Ok(slot) = slot {
                self.stack_mut()[slot].active = true;
            }
        }
    }

    fn assign(&mut self, block: &mut Block) {
        let name = match self.eat() {
            Token::Identifier(name) => name,
            _ => {
                error!(self, format!("Expected identifier in assignment"));
                return;
            }
        };

        let op = match self.eat() {
            Token::Equal => None,

            Token::PlusEqual => Some(Op::Add),
            Token::MinusEqual => Some(Op::Sub),
            Token::StarEqual => Some(Op::Mul),
            Token::SlashEqual => Some(Op::Div),

            _ => {
                error!(self, format!("Expected '=' in assignment"));
                return;
            }
        };

        if let Some(var) = self.find_variable(&name) {
            if !var.mutable {
                // TODO(ed): Maybe a better error than "SyntaxError".
                error!(self, format!("Cannot assign to constant '{}'", var.name));
            }
            if let Some(op) = op {
                if var.upvalue {
                    add_op(self, block, Op::ReadUpvalue(var.slot));
                } else {
                    add_op(self, block, Op::ReadLocal(var.slot));
                }
                self.expression(block);
                add_op(self, block, op);
            } else {
                self.expression(block);
            }

            if var.upvalue {
                add_op(self, block, Op::AssignUpvalue(var.slot));
            } else {
                add_op(self, block, Op::AssignLocal(var.slot));
            }
        } else {
            error!(self, format!("Using undefined variable {}.", name));
        }
    }

    fn scope(&mut self, block: &mut Block) {
        if !expect!(self, Token::LeftBrace, "Expected '{' at start of block.") {
            return;
        }

        push_scope!(self, block, {
            while !matches!(self.peek(), Token::RightBrace | Token::EOF) {
                self.statement(block);
                match self.peek() {
                    Token::Newline => { self.eat(); },
                    Token::RightBrace => { break; },
                    _ => { error!(self, "Expect newline after statement."); },
                }
            }
        });

        expect!(self, Token::RightBrace, "Expected '}' at end of block.");
    }

    fn if_statment(&mut self, block: &mut Block) {
        expect!(self, Token::If, "Expected 'if' at start of if-statement.");
        self.expression(block);
        let jump = add_op(self, block, Op::Illegal);
        self.scope(block);

        if Token::Else == self.peek() {
            self.eat();

            let else_jmp = add_op(self, block, Op::Illegal);
            block.patch(Op::JmpFalse(block.curr()), jump);

            match self.peek() {
                Token::If => self.if_statment(block),
                Token::LeftBrace => self.scope(block),
                _ => error!(self, "Epected 'if' or '{' after else."),
            }
            block.patch(Op::Jmp(block.curr()), else_jmp);
        } else {
            block.patch(Op::JmpFalse(block.curr()), jump);
        }
    }

    //TODO de-complexify
    fn for_loop(&mut self, block: &mut Block) {
        expect!(self, Token::For, "Expected 'for' at start of for-loop.");

        push_scope!(self, block, {
            self.frame_mut().push_loop();
            // Definition
            match self.peek_four() {
                // TODO(ed): Typed definitions aswell!
                (Token::Identifier(name), Token::ColonEqual, ..) => {
                    self.eat();
                    self.eat();
                    self.definition_statement(&name, Type::Unknown, block);
                }

                (Token::Comma, ..) => {}

                _ => { error!(self, "Expected definition at start of for-loop."); }
            }

            expect!(self, Token::Comma, "Expect ',' between initalizer and loop expression.");

            let cond = block.curr();
            self.expression(block);
            let cond_out = add_op(self, block, Op::Illegal);
            let cond_cont = add_op(self, block, Op::Illegal);
            expect!(self, Token::Comma, "Expect ',' between initalizer and loop expression.");

            let inc = block.curr();
            push_scope!(self, block, {
                self.statement(block);
            });
            add_op(self, block, Op::Jmp(cond));

            // patch_jmp!(Op::Jmp, cond_cont => block.curr());
            block.patch(Op::Jmp(block.curr()), cond_cont);
            self.scope(block);
            add_op(self, block, Op::Jmp(inc));

            block.patch(Op::JmpFalse(block.curr()), cond_out);

            let stacksize = self.frame().stack.len();
            self.frame_mut().pop_loop(block, stacksize, inc, block.curr());
        });
    }

    fn parse_type(&mut self) -> Result<Type, ()> {
        let ty = self.parse_simple_type();
        if self.peek() == Token::Questionmark {
            self.eat();
            ty.map(|x| Type::Union(vec![x, Type::Void]))
        } else {
            ty
        }
    }

    fn parse_simple_type(&mut self) -> Result<Type, ()> {
        match self.peek() {
            Token::Fn => {
                self.eat();
                let mut params = Vec::new();
                let return_type = loop {
                    match self.peek() {
                        Token::Identifier(_) | Token::Fn => {
                            if let Ok(ty) = self.parse_type() {
                                params.push(ty);
                                if self.peek() == Token::Comma {
                                    self.eat();
                                }
                            } else {
                                error!(self, format!("Function type signature contains non-type {:?}.", self.peek()));
                                return Err(());
                            }
                        }
                        Token::Arrow => {
                            self.eat();
                            break self.parse_type().unwrap_or(Type::Void);
                        }
                        Token::Comma | Token::Equal => {
                            break Type::Void;
                        }
                        token => {
                            error!(self, format!("Function type signature contains non-type {:?}.", token));
                            return Err(());
                        }
                    }
                };
                let f = Type::Function(params, Box::new(return_type));
                Ok(f)
            }

            Token::LeftParen => {
                self.eat();
                let mut element = Vec::new();
                loop {
                    element.push(self.parse_type()?);
                    if self.peek() == Token::RightParen {
                        self.eat();
                        return Ok(Type::Tuple(element));
                    }
                    if !expect!(self,
                                Token::Comma,
                                "Expect comma efter element in tuple.") {
                        return Err(());
                    }
                }
            }

            Token::Identifier(x) => {
                self.eat();
                match x.as_str() {
                    "int" => Ok(Type::Int),
                    "float" => Ok(Type::Float),
                    "bool" => Ok(Type::Bool),
                    "str" => Ok(Type::String),
                    x => {
                        let blob = self.find_constant(x);
                        if let Value::Blob(blob) = &self.constants[blob] {
                            Ok(Type::Instance(Rc::clone(blob)))
                        } else {
                            // TODO(ed): This is kinda bad. If the type cannot
                            // be found it tries to infer it during runtime
                            // and doesn't verify it.
                            Ok(Type::Unknown)
                        }
                    }
                }
            }
            _ => Err(()),
        }
    }

    fn blob_statement(&mut self, _block: &mut Block) {
        expect!(self, Token::Blob, "Expected blob when declaring a blob");
        let name = if let Token::Identifier(name) = self.eat() {
            name
        } else {
            error!(self, "Expected identifier after 'blob'.");
            return;
        };

        expect!(self, Token::LeftBrace, "Expected 'blob' body. AKA '{'.");

        let mut blob = Blob::new(self.new_blob_id(), &name);
        loop {
            if matches!(self.peek(), Token::EOF | Token::RightBrace) { break; }
            if matches!(self.peek(), Token::Newline) { self.eat(); continue; }

            let name = if let Token::Identifier(name) = self.eat() {
                name
            } else {
                error!(self, "Expected identifier for field.");
                continue;
            };

            expect!(self, Token::Colon, "Expected ':' after field name.");

            let ty = if let Ok(ty) = self.parse_type() {
                ty
            } else {
                error!(self, "Failed to parse blob-field type.");
                continue;
            };

            if let Err(_) = blob.add_field(&name, ty) {
                error!(self, format!("A field named '{}' is defined twice for '{}'", name, blob.name));
            }
        }

        expect!(self, Token::RightBrace, "Expected '}' after 'blob' body. AKA '}'.");

        let blob = Value::Blob(Rc::new(blob));
        self.named_constant(name, blob);
    }

    fn access_dotted(&mut self, block: &mut Block) {
        let name = match self.peek() {
            Token::Identifier(name) => name,
            _ => unreachable!(),
        };
        if let Some(_) = self.find_namespace(&name) {
            self.expression(block);
        } else {
            parse_branch!(self, block, [self.blob_field(block), self.expression(block)]);
        }
    }

    //TODO rename
    fn blob_field(&mut self, block: &mut Block) {
        let name = match self.eat() {
            Token::Identifier(name) => name,
            _ => unreachable!(),
        };

        if let Some(var) = self.find_variable(&name) {
            self.mark_read(self.frames().len() - 1, &var);
            if var.upvalue {
                add_op(self, block, Op::ReadUpvalue(var.slot));
            } else {
                add_op(self, block, Op::ReadLocal(var.slot));
            }
            loop {
                match self.peek() {
                    Token::Dot => {
                        self.eat();
                        let field = if let Token::Identifier(field) = self.eat() {
                            String::from(field)
                        } else {
                            error!(self, "Expected fieldname after '.'.");
                            return;
                        };

                        let field = self.intern_string(field);
                        let op = match self.peek() {
                            Token::Equal => {
                                self.eat();
                                self.expression(block);
                                add_op(self, block, Op::Set(field));
                                return;
                            }

                            Token::PlusEqual => Op::Add,
                            Token::MinusEqual => Op::Sub,
                            Token::StarEqual => Op::Mul,
                            Token::SlashEqual => Op::Div,

                            _ => {
                                add_op(self, block, Op::Get(field));
                                continue;
                            }
                        };
                        add_op(self, block, Op::Copy);
                        add_op(self, block, Op::Get(field));
                        self.eat();
                        self.expression(block);
                        add_op(self, block, op);
                        add_op(self, block, Op::Set(field));
                        return;
                    }
                    Token::Newline => {
                        return;
                    }
                    _ => {
                        if !self.call_maybe(block) {
                            error!(self, "Unexpected token when parsing blob-field.");
                            return;
                        }
                    }
                }
            }
        } else {
            error!(self, format!("Cannot find variable '{}'.", name));
            return;
        }
    }

    fn outer_statement(&mut self, block: &mut Block) {
        self.clear_panic();
        match self.peek_four() {
            (Token::Identifier(name), Token::ColonEqual, ..) => {
                self.eat();
                self.eat();
                self.definition_statement(&name, Type::Unknown, block);
            },

            (Token::Identifier(name), Token::ColonColon, ..) => {
                self.eat();
                self.eat();
                self.constant_statement(&name, Type::Unknown, block);
            },

            (Token::Blob, Token::Identifier(_), ..) => {
                self.blob_statement(block);
            },

            (Token::Identifier(name), Token::Colon, ..) => {
                self.eat();
                self.eat();
                if let Ok(typ) = self.parse_type() {
                    expect!(self, Token::Equal, "Expected assignment.");
                    self.definition_statement(&name, typ, block);
                } else {
                    error!(self, format!("Expected type found '{:?}'.", self.peek()));
                }
            }

            (Token::Newline, ..) => {}

            (a, b, c, d) => {
                error!(self, format!("Unknown outer token sequence: {:?} {:?} {:?} {:?}.", a, b, c, d))
            }
        }
    }

    fn statement(&mut self, block: &mut Block) {
        self.clear_panic();

        match self.peek_four() {
            (Token::Print, ..) => {
                self.eat();
                self.expression(block);
                add_op(self, block, Op::Print);
            }

            (Token::Identifier(_), Token::Equal, ..) |
            (Token::Identifier(_), Token::PlusEqual, ..) |
            (Token::Identifier(_), Token::MinusEqual, ..) |
            (Token::Identifier(_), Token::SlashEqual, ..) |
            (Token::Identifier(_), Token::StarEqual, ..)

                => {
                self.assign(block);
            }

            (Token::Identifier(_), Token::Dot, ..) => {
                self.access_dotted(block);
            }

            (Token::Identifier(name), Token::Colon, ..) => {
                self.eat();
                self.eat();
                if let Ok(typ) = self.parse_type() {
                    expect!(self, Token::Equal, "Expected assignment.");
                    self.definition_statement(&name, typ, block);
                } else {
                    error!(self, format!("Expected type found '{:?}'.", self.peek()));
                }
            }

            (Token::Yield, ..) => {
                self.eat();
                add_op(self, block, Op::Yield);
            }

            (Token::Identifier(name), Token::ColonEqual, ..) => {
                self.eat();
                self.eat();
                self.definition_statement(&name, Type::Unknown, block);
            }

            (Token::Identifier(name), Token::ColonColon, ..) => {
                self.eat();
                self.eat();
                self.constant_statement(&name, Type::Unknown, block);
            }

            (Token::Blob, Token::Identifier(_), ..) => {
                self.blob_statement(block);
            }

            (Token::If, ..) => {
                self.if_statment(block);
            }

            (Token::For, ..) => {
                self.for_loop(block);
            }

            (Token::Break, ..) => {
                self.eat();
                let addr = add_op(self, block, Op::Illegal);
                let stack_size = self.frame().stack.len();
                if self.frame_mut().add_break(addr, stack_size).is_err() {
                    error!(self, "Cannot place 'break' outside of loop.");
                }
            }

            (Token::Continue, ..) => {
                self.eat();
                let addr = add_op(self, block, Op::Illegal);
                let stack_size = self.frame().stack.len();
                if self.frame_mut().add_continue(addr, stack_size).is_err() {
                    error!(self, "Cannot place 'continue' outside of loop.");
                }
            }

            (Token::Ret, ..) => {
                self.eat();
                self.expression(block);
                add_op(self, block, Op::Return);
            }

            (Token::Unreachable, ..) => {
                self.eat();
                add_op(self, block, Op::Unreachable);
            }

            (Token::LeftBrace, ..) => {
                self.scope(block);
            }

            (Token::Newline, ..) => {}

            _ => {
                self.expression(block);
                add_op(self, block, Op::Pop);
            }
        }
    }

    pub(crate) fn compile(&mut self, name: &str, file: &Path, functions: &[(String, RustFunction)]) -> Result<Prog, Vec<Error>> {
        let main = Variable::new("/main/", false, Type::Void);
        let slot = self.define(main).unwrap();
        self.frame_mut().stack[slot].read = true;

        for section in 0..self.sections.len() {
            self.init_section(section);
            let section = &mut self.sections[section];
            match (section.tokens.get(0), section.tokens.get(1), section.tokens.get(2))  {
                (Some((Token::Use, _)),
                 Some((Token::Identifier(name), _)), ..) => {
                    let name = name.to_string();
                    self.add_namespace(name);
                }

                (Some((Token::Identifier(name), _)),
                 Some((Token::ColonColon, _)),
                 Some((Token::Fn, _))) => {
                    let name = name.to_string();
                    self.forward_constant(name);
                }

                (Some((Token::Blob, _)),
                 Some((Token::Identifier(name), _)), ..) => {
                    let name = name.to_string();
                    self.forward_constant(name);
                }

                (Some((Token::Identifier(name), _)),
                 Some((Token::Colon, _)), ..) => {
                    let name = name.to_string();
                    self.eat();
                    self.eat();
                    if let Ok(ty) = self.parse_type() {
                        let is_mut = self.peek() == Token::Equal;
                        let var = Variable::new(&name, is_mut, ty);
                        let _ = self.define(var).unwrap();
                    } else {
                        error!(self, format!("Failed to parse type global '{}'.", name));
                    }
                }

                (Some((Token::Identifier(name), _)),
                 Some((Token::ColonColon, _)), ..) => {
                    let var = Variable::new(name, false, Type::Unknown);
                    let _ = self.define(var).unwrap();
                }

                (Some((Token::Identifier(name), _)),
                 Some((Token::ColonEqual, _)), ..) => {
                    let var = Variable::new(name, true, Type::Unknown);
                    let _ = self.define(var).unwrap();
                }


                (None, ..) => {}

                (a, b, c) => {
                    section.faulty = true;
                    let msg = format!("Unknown outer token sequence: {:?} {:?} {:?}. Expected 'use', function, blob or variable.", a, b, c);
                    error!(self, msg);
                }
            }
        }

        self.functions = functions
            .to_vec()
            .into_iter()
            .enumerate()
            .map(|(i, (s, f))| (s, (i, f)))
            .collect();
        let mut block = Block::new(name, file);
        for section in 0..self.sections.len() {
            self.init_section(section);
            if self.sections[section].faulty {
                continue;
            }
            while !matches!(self.peek(), Token::EOF | Token::Use) {
                self.outer_statement(&mut block);
                expect!(self, Token::Newline | Token::EOF,
                        "Expect newline or EOF after expression.");
            }
        }
        block.ty = Type::Function(Vec::new(), Box::new(Type::Void));

        if self.names().len() != 0 {
            let errors: Vec<_> = self.names().iter().filter_map(|(name, kind)|
                if let Name::Unknown(_, line) = kind {
                    Some((ErrorKind::SyntaxError(*line, Token::Identifier(name.clone())),
                    *line,
                    format!("Usage of undefined value: '{}'.", name,)))
                } else {
                    None
                }) .collect();
            for (e, l, m) in errors.iter() {
                self.error_on_line(e.clone(), *l, Some(m.clone()));
            }
        }

        self.init_section(0);
        let constant = self.find_constant("start");
        add_op(self, &mut block, Op::Constant(constant));
        add_op(self, &mut block, Op::Call(0));

        let tmp = self.add_constant(Value::Unknown);
        add_op(self, &mut block, Op::Constant(tmp));
        add_op(self, &mut block, Op::Return);

        for var in self.frames_mut().pop().unwrap().stack.iter().skip(1) {
            if !(var.read || var.upvalue) {
                let e = ErrorKind::SyntaxError(var.line, Token::Identifier(var.name.clone()));
                let m = format!("Unused value '{}'.", var.name);
                self.error_on_line(e, var.line, Some(m));
            }
            self.panic = false;
        }

        self.blocks.insert(0, Rc::new(RefCell::new(block)));

        if self.errors.is_empty() {
            Ok(Prog {
                blocks: self.blocks.clone(),
                functions: functions.iter().map(|(_, f)| *f).collect(),
                constants: self.constants.clone(),
                strings: self.strings.clone(),
            })
        } else {
            Err(self.errors.clone())
        }
    }
}
