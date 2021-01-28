use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::hash_map::Entry;

use crate::error::{Error, ErrorKind};
use crate::tokenizer::{Token, TokenStream};
use crate::vm::{Value, Block, Op};

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

nextable_enum!(Prec {
    No,
    Assert,
    Bool,
    Comp,
    Term,
    Factor,
});


#[derive(Debug, Clone)]
pub struct Prog {
    pub blocks: Vec<Rc<RefCell<Block>>>,
    pub blobs: Vec<Rc<Blob>>,
}

#[derive(Debug, Clone)]
pub enum Type {
    Void,
    UnknownType,
    Int,
    Float,
    Bool,
    String,
    Function(Vec<Type>, Box<Type>),
    Blob(usize),
    BlobInstance(usize),
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Void, Type::Void) => true,
            (Type::BlobInstance(a), Type::BlobInstance(b)) => a == b,
            (Type::Blob(a), Type::Blob(b)) => a == b,
            (Type::Int, Type::Int) => true,
            (Type::Float, Type::Float) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::String, Type::String) => true,
            (Type::Function(a_args, a_ret), Type::Function(b_args, b_ret)) =>
                a_args == b_args && a_ret == b_ret,
            _ => false,
        }
    }
}

impl From<&Value> for Type {
    fn from(value: &Value) -> Type {
        match value {
            Value::BlobInstance(i, _) => Type::BlobInstance(*i),
            Value::Blob(i) => Type::Blob(*i),
            Value::Int(_) => Type::Int,
            Value::Float(_) => Type::Float,
            Value::Bool(_) => Type::Bool,
            Value::String(_) => Type::String,
            Value::Function(_, block) => block.borrow().ty.clone(),
            _ => Type::Void,
        }
    }
}

impl Type {
    pub fn is_unkown(&self) -> bool {
        match self {
            Type::UnknownType => true,
            _ => false,
        }
    }

    pub fn as_value(&self) -> Value {
        match self {
            Type::Void => Value::Nil,
            Type::Blob(i) => Value::Blob(*i),
            Type::BlobInstance(i) => Value::BlobInstance(*i, Vec::new()),
            Type::UnknownType => Value::Unkown,
            Type::Int => Value::Int(1),
            Type::Float => Value::Float(1.0),
            Type::Bool => Value::Bool(true),
            Type::String => Value::String(Rc::new("".to_string())),
            Type::Function(_, _) => Value::Function(
                Vec::new(),
                Rc::new(RefCell::new(Block::from_type(self)))),
        }
    }
}

#[derive(Clone)]
struct Variable {
    name: String,
    typ: Type,
    scope: usize,
    slot: usize,

    outer_slot: usize,
    outer_upvalue: bool,

    active: bool,
    upvalue: bool,
    captured: bool,
}

struct Frame {
    stack: Vec<Variable>,
    upvalues: Vec<Variable>,
    scope: usize,
    variables_below: usize,
}

impl Frame {
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

#[derive(Debug, Clone)]
pub struct Blob {
    pub name: String,

    pub name_to_field: HashMap<String, (usize, Type)>,
}

impl Blob {
    pub fn new(name: &str) -> Self {
        Self {
            name: String::from(name),
            name_to_field: HashMap::new(),
        }
    }

    pub fn add_field(&mut self, name: &str, ty: Type) -> Result<(), ()> {
        let size = self.name_to_field.len();
        let entry = self.name_to_field.entry(String::from(name));
        if matches!(entry, Entry::Occupied(_)) {
            Err(())
        } else {
            entry.or_insert((size, ty));
            Ok(())
        }
    }
}

struct Compiler {
    curr: usize,
    tokens: TokenStream,
    current_file: PathBuf,

    frames: Vec<Frame>,

    panic: bool,
    errors: Vec<Error>,

    blocks: Vec<Rc<RefCell<Block>>>,
    blobs: Vec<Blob>,
}

macro_rules! push_frame {
    ($compiler:expr, $block:expr, $code:tt) => {
        {
            $compiler.frames.push(Frame {
                stack: Vec::new(),
                upvalues: Vec::new(),
                scope: 0,
                variables_below: $compiler.frame().variables_below + $compiler.stack().len(),
            });

            // Return value stored as a variable
            $compiler.define_variable("", Type::UnknownType, &mut $block).unwrap();
            $code

            $compiler.frames.pop().unwrap();
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

        for var in $compiler.frame().stack[ss..$compiler.stack().len()].iter().rev() {
            if var.captured {
                $block.add(Op::PopUpvalue, $compiler.line());
            } else {
                $block.add(Op::Pop, $compiler.line());
            }
        }
        $compiler.stack_mut().truncate(ss);
    };
}

impl Compiler {
    pub fn new(current_file: &Path, tokens: TokenStream) -> Self {
        Self {
            curr: 0,
            tokens,
            current_file: PathBuf::from(current_file),

            frames: vec![Frame {
                stack: Vec::new(),
                upvalues: Vec::new(),
                scope: 0,
                variables_below: 0,
            }],

            panic: false,
            errors: vec![],

            blocks: Vec::new(),
            blobs: Vec::new(),
        }
    }

    fn frame(&self) -> &Frame {
        let last = self.frames.len() - 1;
        &self.frames[last]
    }

    fn frame_mut(&mut self) -> &mut Frame {
        let last = self.frames.len() - 1;
        &mut self.frames[last]
    }

    fn stack(&self) -> &[Variable] {
        &self.frame().stack.as_ref()
    }

    fn stack_mut(&mut self) -> &mut Vec<Variable> {
        &mut self.frame_mut().stack
    }

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
        if self.panic { return }
        self.panic = true;
        self.errors.push(Error {
            kind,
            file: self.current_file.clone(),
            line: self.line(),
            message,
        });
    }

    fn peek(&self) -> Token {
        self.peek_at(0)
    }

    fn peek_at(&self, at: usize) -> Token {
        if self.tokens.len() <= self.curr + at {
            crate::tokenizer::Token::EOF
        } else {
            self.tokens[self.curr + at].0.clone()
        }
    }

    // TODO(ed): Const generics
    fn peek_four(&self) -> (Token, Token, Token, Token) {
        (self.peek_at(0), self.peek_at(1), self.peek_at(2), self.peek_at(3))
    }

    fn eat(&mut self) -> Token {
        let t = self.peek();
        self.curr += 1;
        t
    }

    fn precedence(&self, token: Token) -> Prec {
        match token {
            Token::Star | Token::Slash => Prec::Factor,

            Token::Minus | Token::Plus => Prec::Term,

            Token::EqualEqual
                | Token::Greater
                | Token::GreaterEqual
                | Token::Less
                | Token::LessEqual
                | Token::NotEqual
                => Prec::Comp,

            Token::And | Token::Or => Prec::Bool,

            Token::AssertEqual => Prec::Assert,

            _ => Prec::No,
        }
    }

    fn line(&self) -> usize {
        if self.curr < self.tokens.len() {
            self.tokens[self.curr].1
        } else {
            self.tokens[self.tokens.len() - 1].1
        }
    }

    fn prefix(&mut self, token: Token, block: &mut Block) -> bool {
        match token {
            Token::Identifier(_) => self.variable_expression(block),
            Token::LeftParen => self.grouping(block),
            Token::Minus => self.unary(block),

            Token::Float(_) => self.value(block),
            Token::Int(_) => self.value(block),
            Token::Bool(_) => self.value(block),
            Token::String(_) => self.value(block),

            Token::Not => self.unary(block),

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
        block.add(Op::Constant(value), self.line());
    }

    fn grouping(&mut self, block: &mut Block) {
        expect!(self, Token::LeftParen, "Expected '(' around expression.");

        self.expression(block);

        expect!(self, Token::RightParen, "Expected ')' around expression.");
    }

    fn unary(&mut self, block: &mut Block) {
        let op = match self.eat() {
            Token::Minus => Op::Neg,
            Token::Not => Op::Not,
            _ => { error!(self, "Invalid unary operator"); Op::Neg },
        };
        self.parse_precedence(block, Prec::Factor);
        block.add(op, self.line());
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

    fn expression(&mut self, block: &mut Block) {
        match self.peek_four() {
            (Token::Fn, ..) => self.function(block),
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

    fn find_and_capture_variable<'a, I>(name: &str, mut iterator: I) -> Option<Variable>
    where I: Iterator<Item = &'a mut Frame> {
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

    fn find_variable(&mut self, name: &str) -> Option<Variable> {
        if let Some(res) = self.frame().find_local(name) {
            return Some(res);
        }

        if let Some(res) = self.frame().find_upvalue(name) {
            return Some(res);
        }

        return Self::find_and_capture_variable(name, self.frames.iter_mut().rev());
    }

    fn find_blob(&self, name: &str) -> Option<usize> {
        self.blobs.iter().enumerate()
            .find(|(_, x)| x.name == name)
            .map(|(i, _)| i)
    }

    fn call(&mut self, block: &mut Block) {
        expect!(self, Token::LeftParen, "Expected '(' at start of function call.");

        let mut arity = 0;
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
        }

        block.add(Op::Call(arity), self.line());
    }

    fn function(&mut self, block: &mut Block) {
        expect!(self, Token::Fn, "Expected 'fn' at start of function.");

        let top = self.stack().len() - 1;
        let name = if !self.stack()[top].active {
            self.stack_mut()[top].active = true;
            &self.stack()[top].name
        } else {
            "anonumus function"
        };

        let mut args = Vec::new();
        let mut return_type = Type::Void;
        let mut function_block = Block::new(name, &self.current_file, self.line());

        let _ret = push_frame!(self, function_block, {
            loop {
                match self.peek() {
                    Token::Identifier(name) => {
                        self.eat();
                        expect!(self, Token::Colon, "Expected ':' after parameter name.");
                        if let Ok(typ) = self.parse_type() {
                            args.push(typ.clone());
                            if let Ok(slot) = self.define_variable(&name, typ, &mut function_block) {
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
                function_block.ups.push((var.outer_slot, var.outer_upvalue, var.typ.clone()));
            }
        });

        for op in function_block.ops.iter().rev() {
            match op {
                Op::Pop | Op::PopUpvalue => {}
                Op::Return => { break; } ,
                _ => {
                    function_block.add(Op::Constant(Value::Nil), self.line());
                    function_block.add(Op::Return, self.line());
                    break;
                }
            }
        }

        if function_block.ops.is_empty() {
            function_block.add(Op::Constant(Value::Nil), self.line());
            function_block.add(Op::Return, self.line());
        }

        function_block.ty = Type::Function(args, Box::new(return_type));
        let function_block = Rc::new(RefCell::new(function_block));


        let func = Op::Constant(Value::Function(Vec::new(), Rc::clone(&function_block)));
        block.add(func, self.line());
        self.blocks.push(function_block);
    }

    fn variable_expression(&mut self, block: &mut Block) {
        let name = match self.eat() {
            Token::Identifier(name) => name,
            _ => unreachable!(),
        };
        if let Some(var) = self.find_variable(&name) {
            if var.upvalue {
                block.add(Op::ReadUpvalue(var.slot), self.line());
            } else {
                block.add(Op::ReadLocal(var.slot), self.line());
            }
            if self.peek() == Token::LeftParen {
                self.call(block);
            }
        } else if let Some(blob) = self.find_blob(&name) {
            block.add(Op::Constant(Value::Blob(blob)), self.line());
            if self.peek() == Token::LeftParen {
                self.call(block);
            }
        } else {
            error!(self, format!("Using undefined variable {}.", name));
        }
    }

    fn define_variable(&mut self, name: &str, typ: Type, _block: &mut Block) -> Result<usize, ()> {
        if let Some(var) = self.find_variable(&name) {
            if var.scope == self.frame().scope {
                error!(self, format!("Multiple definitions of {} in this block.", name));
                return Err(());
            }
        }

        let slot = self.stack().len();
        let scope = self.frame().scope;
        self.stack_mut().push(Variable {
            name: String::from(name),
            captured: false,
            outer_upvalue: false,
            outer_slot: 0,
            slot,
            typ,
            scope,
            active: false,
            upvalue: false,
        });
        Ok(slot)
    }

    fn definition_statement(&mut self, name: &str, typ: Type, block: &mut Block) {
        let slot = self.define_variable(name, typ.clone(), block);
        self.expression(block);
        block.add(Op::Define(typ), self.line());

        if let Ok(slot) = slot {
            self.stack_mut()[slot].active = true;
        }
    }

    fn assign(&mut self, name: &str, block: &mut Block) {
        if let Some(var) = self.find_variable(&name) {
            self.expression(block);
            if var.upvalue {
                block.add(Op::AssignUpvalue(var.slot), self.line());
            } else {
                block.add(Op::AssignLocal(var.slot), self.line());
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
        let jump = block.add(Op::Illegal, self.line());
        self.scope(block);

        if Token::Else == self.peek() {
            self.eat();

            let else_jmp = block.add(Op::Illegal, self.line());
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
            // Definition
            match self.peek_four() {
                // TODO(ed): Typed definitions aswell!
                (Token::Identifier(name), Token::ColonEqual, ..) => {
                    self.eat();
                    self.eat();
                    self.definition_statement(&name, Type::UnknownType, block);
                }

                (Token::Comma, ..) => {}

                _ => { error!(self, "Expected definition at start of for-loop."); }
            }

            expect!(self, Token::Comma, "Expect ',' between initalizer and loop expression.");

            let cond = block.curr();
            self.expression(block);
            let cond_out = block.add(Op::Illegal, self.line());
            let cond_cont = block.add(Op::Illegal, self.line());
            expect!(self, Token::Comma, "Expect ',' between initalizer and loop expression.");

            let inc = block.curr();
            push_scope!(self, block, {
                self.statement(block);
            });
            block.add(Op::Jmp(cond), self.line());

            // patch_jmp!(Op::Jmp, cond_cont => block.curr());
            block.patch(Op::Jmp(block.curr()), cond_cont);
            self.scope(block);
            block.add(Op::Jmp(inc), self.line());

            block.patch(Op::JmpFalse(block.curr()), cond_out);

        });
    }

    fn parse_type(&mut self) -> Result<Type, ()> {
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
            Token::Identifier(x) => {
                self.eat();
                match x.as_str() {
                    "int" => Ok(Type::Int),
                    "float" => Ok(Type::Float),
                    "bool" => Ok(Type::Bool),
                    "str" => Ok(Type::String),
                    _ => Err(()),
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

        let mut blob = Blob::new(&name);
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

        self.blobs.push(blob);
    }

    fn statement(&mut self, block: &mut Block) {
        self.clear_panic();

        match self.peek_four() {
            (Token::Print, ..) => {
                self.eat();
                self.expression(block);
                block.add(Op::Print, self.line());
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

            (Token::Identifier(name), Token::ColonEqual, ..) => {
                self.eat();
                self.eat();
                self.definition_statement(&name, Type::UnknownType, block);
            }

            (Token::Identifier(name), Token::Equal, ..) => {
                self.eat();
                self.eat();
                self.assign(&name, block);
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

            (Token::Ret, ..) => {
                self.eat();
                self.expression(block);
                block.add(Op::Return, self.line());
            }

            (Token::Unreachable, ..) => {
                self.eat();
                block.add(Op::Unreachable, self.line());
            }

            (Token::LeftBrace, ..) => {
                self.scope(block);
            }

            (Token::Newline, ..) => {}

            _ => {
                self.expression(block);
                block.add(Op::Pop, self.line());
            }
        }

    }

    pub fn compile(&mut self, name: &str, file: &Path) -> Result<Prog, Vec<Error>> {
        println!("=== START COMPILATION ===");
        self.stack_mut().push(Variable {
            name: String::from("/main/"),
            typ: Type::Void,
            outer_upvalue: false,
            outer_slot: 0,
            slot: 0,
            scope: 0,
            active: false,
            captured: false,
            upvalue: false,
        });

        let mut block = Block::new(name, file, 0);
        while self.peek() != Token::EOF {
            self.statement(&mut block);
            expect!(self, Token::Newline | Token::EOF, "Expect newline or EOF after expression.");
        }
        block.add(Op::Constant(Value::Nil), self.line());
        block.add(Op::Return, self.line());
        block.ty = Type::Function(Vec::new(), Box::new(Type::Void));

        self.blocks.insert(0, Rc::new(RefCell::new(block)));

        println!("=== END COMPILATION ===");
        if self.errors.is_empty() {
            Ok(Prog {
                blocks: self.blocks.clone(),
                blobs: self.blobs.iter().map(|x| Rc::new(x.clone())).collect(),
            })
        } else {
            Err(self.errors.clone())
        }
    }
}

pub fn compile(name: &str, file: &Path, tokens: TokenStream) -> Result<Prog, Vec<Error>> {
    Compiler::new(file, tokens).compile(name, file)
}
