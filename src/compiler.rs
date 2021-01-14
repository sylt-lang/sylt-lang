use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::convert::TryFrom;

use crate::tokenizer::{Token, TokenStream};
use crate::vm::{Value, Block, Op};
use crate::error::{Error, ErrorKind};

macro_rules! nextable_enum {
    ( $name:ident { $( $thing:ident ),* } ) => {
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
    ($thing:expr, $exp:pat, $msg:expr) => {
        match $thing.peek() {
            $exp => { $thing.eat(); true },
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
    Factor
});

#[derive(Debug, Clone)]
pub enum Type {
    NoType,
    UnkownType,
    Int,
    Float,
    Bool,
    String,
    Function(Rc<Block>),
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::NoType, Type::NoType) => true,
            (Type::Int, Type::Int) => true,
            (Type::Float, Type::Float) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::String, Type::String) => true,
            (Type::Function(a), Type::Function(b)) => {
                a.args == b.args && a.ret == b.ret
            },
            _ => false,
        }
    }
}

impl From<&Value> for Type {

    fn from(value: &Value) -> Type {
        match value {
            Value::Int(_) => Type::Int,
            Value::Float(_) => Type::Float,
            Value::Bool(_) => Type::Bool,
            Value::String(_) => Type::String,
            Value::Function(_, block) => {
                Type::Function(Rc::clone(block))
            },
            _ => Type::NoType,
        }
    }
}

struct Variable {
    name: String,
    typ: Type,
    scope: usize,
    active: bool,
}

struct Frame {
    stack: Vec<Variable>,
    scope: usize,
    variables_below: usize,
}

struct Compiler {
    curr: usize,
    tokens: TokenStream,
    current_file: PathBuf,

    frames: Vec<Frame>,

    panic: bool,
    errors: Vec<Error>,
}

macro_rules! push_frame {
    ($compiler:expr, $block:expr, $code:tt) => {
        {
            $compiler.frames.push(Frame {
                stack: Vec::new(),
                scope: 0,
                variables_below: $compiler.frame().variables_below + $compiler.stack().len(),
            });

            // Return value stored as a variable
            $compiler.define_variable("", Type::UnkownType, &mut $block).unwrap();
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
        for _ in ss..$compiler.stack().len() {
            $block.add(Op::Pop, $compiler.line());
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
                scope: 0,
                variables_below: 0,
            }],

            panic: false,
            errors: vec![],
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

            Token::LeftParen => self.call(block),

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

    fn find_local(&self, name: &str, _block: &Block) -> Option<(usize, Type, usize)> {
        let frame = self.frame();
        for (slot, var) in frame.stack.iter().enumerate().rev() {
            if var.name == name && var.active {
                return Some((slot, var.typ.clone(), var.scope));
            }
        }
        None
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

        for _ in 0..arity {
            block.add(Op::Pop, self.line());
        }
    }

    fn function(&mut self, block: &mut Block) {
        expect!(self, Token::Fn, "Expected 'fn' at start of function.");

        let name = if !self.stack()[self.stack().len() - 1].active {
            &self.stack()[self.stack().len() - 1].name
        } else {
            "anonumus function"
        };

        let mut return_type = None;
        let mut function_block = Block::new(name, &self.current_file, self.line());
        let arity;
        let _ret = push_frame!(self, function_block, {
            loop {
                match self.peek() {
                    Token::Identifier(name) => {
                        self.eat();
                        expect!(self, Token::Colon, "Expected ':' after parameter name.");
                        if let Ok(typ) = self.type_ident() {
                            function_block.args.push(typ.clone());
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
                        return_type = Some(Type::NoType);
                        break;
                    }
                    Token::Arrow => {
                        self.eat();
                        if let Ok(typ) = self.type_ident() {
                            return_type = Some(typ);
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
            arity = self.frame().stack.len() - 1;

            self.scope(&mut function_block);
        });

        match return_type {
            Some(typ) => function_block.ret = typ,
            None => error!(self, "No returntype secified!"),
        }

        function_block.add(Op::Return, self.line());

        block.add(Op::Constant(Value::Function(arity, Rc::new(function_block))), self.line());
    }

    fn variable_expression(&mut self, block: &mut Block) {
        let name = match self.eat() {
            Token::Identifier(name) => name,
            __ => unreachable!(),
        };
        if let Some((slot, _, _)) = self.find_local(&name, block) {
            block.add(Op::ReadLocal(slot), self.line());
        } else {
            error!(self, format!("Using undefined variable {}.", name));
        }
    }

    fn define_variable(&mut self, name: &str, typ: Type, block: &mut Block) -> Result<usize, ()> {
        if let Some((_, _, level)) = self.find_local(&name, block) {
            if level == self.frame().scope {
                error!(self, format!("Multiple definitions of {} in this block.", name));
                return Err(());
            }
        }

        let slot = self.stack().len();
        let scope = self.frame().scope;
        self.stack_mut().push(Variable {
            name: String::from(name),
            typ,
            scope,
            active: false
        });
        Ok(slot)
    }

    fn definition_statement(&mut self, name: &str, typ: Type, block: &mut Block) {
        let slot = self.define_variable(name, typ, block);
        self.expression(block);

        if let Ok(slot) = slot {
            self.stack_mut()[slot].active = true;
        }
    }

    fn assign(&mut self, name: &str, block: &mut Block) {
        if let Some((slot, _, _)) = self.find_local(&name, block) {
            self.expression(block);
            block.add(Op::Assign(slot), self.line());
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
                    self.definition_statement(&name, Type::UnkownType, block);
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

    fn type_ident(&mut self) -> Result<Type, ()> {
        match self.eat() {
            Token::Identifier(x) => {
                match x.as_str() {
                    "int" => Ok(Type::Int),
                    "float" => Ok(Type::Float),
                    "bool" => Ok(Type::Bool),
                    "str" => Ok(Type::String),
                    _ => Err(()),
                }
            },
            _ => Err(()),

        }
    }

    fn statement(&mut self, block: &mut Block) {
        self.clear_panic();

        macro_rules! tokens {
            ($( $token:pat ),*) => {
                ($( $token , )* ..)
            };
        }

        match self.peek_four() {
            tokens!(Token::Print) => {
                self.eat();
                self.expression(block);
                block.add(Op::Print, self.line());
            },

            tokens!(Token::Identifier(name), Token::Colon) => {
                self.eat();
                self.eat();
                if let Ok(typ) = self.type_ident() {
                    expect!(self, Token::Equal, "Expected assignment.");
                    self.definition_statement(&name, typ, block);
                } else {
                    error!(self, format!("Expected type found '{:?}'.", self.peek()));
                }
            }

            tokens!(Token::Identifier(name), Token::ColonEqual) => {
                self.eat();
                self.eat();
                self.definition_statement(&name, Type::UnkownType, block);
            }

            tokens!(Token::Identifier(name), Token::Equal) => {
                self.eat();
                self.eat();
                self.assign(&name, block);
            }

            tokens!(Token::If) => {
                self.if_statment(block);
            }

            tokens!(Token::For) => {
                self.for_loop(block);
            }

            tokens!(Token::Ret) => {
                self.eat();
                self.expression(block);
                block.add(Op::Return, self.line());
            }

            tokens!(Token::Unreachable) => {
                self.eat();
                block.add(Op::Unreachable, self.line());
            }

            tokens!(Token::LeftBrace) => {
                self.scope(block);
            }

            tokens!(Token::Newline) => {}

            _ => {
                self.expression(block);
                block.add(Op::Pop, self.line());
            }
        }

    }

    pub fn compile(&mut self, name: &str, file: &Path) -> Result<Block, Vec<Error>> {
        let mut block = Block::new(name, file, 0);

        while self.peek() != Token::EOF {
            self.statement(&mut block);
            expect!(self, Token::Newline, "Expect newline after expression.");
        }
        block.add(Op::Return, self.line());
        block.ret = Type::NoType;

        if self.errors.is_empty() {
            Ok(block)
        } else {
            Err(self.errors.clone())
        }
    }
}

pub fn compile(name: &str, file: &Path, tokens: TokenStream) -> Result<Block, Vec<Error>> {
    Compiler::new(file, tokens).compile(name, file)
}
