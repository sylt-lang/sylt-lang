use std::path::Path;

use crate::tokenizer::{Token, TokenStream};
use crate::vm::{Value, Block, Op};

struct Compiler {
    curr: usize,
    tokens: TokenStream,
}

macro_rules! nextable_enum {
    ( $name:ident, $( $thing:ident ),* ) => {
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

nextable_enum!(Prec,
    No,
    Assert,
    Bool,
    Comp,
    Term,
    Factor
);

impl Compiler {
    pub fn new(tokens: TokenStream) -> Self {
        Self {
            curr: 0,
            tokens,
        }
    }

    fn error(&self, msg: &str) -> ! {
        println!("ERROR: {} line {:?}", msg, self.line());
        panic!();
    }

    fn peek(&self) -> Token {
        if self.tokens.len() <= self.curr {
            crate::tokenizer::Token::EOF
        } else {
            self.tokens[self.curr].0.clone()
        }
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

    fn line(&self) -> Option<usize> {
        match self.tokens.get(self.curr) {
            Some((_, line)) => Some(*line),
            None => None,
        }
    }

    fn prefix(&mut self, token: Token, block: &mut Block) -> bool {
        match token {
            Token::LeftParen => self.grouping(block),
            Token::Minus => self.unary(block),

            Token::Float(_) => self.value(block),
            Token::Int(_) => self.value(block),
            Token::Bool(_) => self.value(block),

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
            _ => { self.error("Invalid value.") }
        };
        block.add(Op::Constant(value), self.line());
    }

    fn grouping(&mut self, block: &mut Block) {
        if Token::LeftParen != self.eat() {
            self.error("Expected left parenthesis around expression.");
        }

        self.expression(block);

        if Token::RightParen != self.eat() {
            self.error("Expected closing parenthesis after expression.");
        }
    }

    fn unary(&mut self, block: &mut Block) {
        let op = match self.eat() {
            Token::Minus => Op::Neg,
            Token::Not => Op::Not,
            _ => self.error("Invalid unary operator"),
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
            Token::AssertEqual => &[Op::AssertEqual],
            Token::EqualEqual => &[Op::Equal],
            Token::Less => &[Op::Less],
            Token::Greater => &[Op::Greater],
            Token::NotEqual => &[Op::Equal, Op::Not],
            Token::LessEqual => &[Op::Greater, Op::Not],
            Token::GreaterEqual => &[Op::Less, Op::Not],
            _ => { self.error("Illegal operator"); }
        };
        block.add_from(op, self.line());
    }

    fn expression(&mut self, block: &mut Block) {
        self.parse_precedence(block, Prec::No);
    }

    fn parse_precedence(&mut self, block: &mut Block, precedence: Prec) {
        println!("-- {:?}", self.peek());
        if !self.prefix(self.peek(), block) {
            self.error("Expected expression.");
        }

        while precedence <= self.precedence(self.peek()) {
            if !self.infix(self.peek(), block) {
                break;
            }
        }
    }

    pub fn compile(&mut self, name: &str, file: &Path) -> Block {
        let mut block = Block::new(name, file);

        loop {
            if self.peek() == Token::EOF {
                break;
            }

            self.expression(&mut block);
            block.add(Op::Print, self.line());

            if self.eat() != Token::Newline {
                self.error("Invalid expression");
            }
        }
        block.add(Op::Return, self.line());

        block
    }
}

pub fn compile(name: &str, file: &Path, tokens: TokenStream) -> Block {
    Compiler::new(tokens).compile(name, file)
}
