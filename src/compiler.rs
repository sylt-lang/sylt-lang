use crate::tokenizer::{Token, TokenStream};
use crate::vm::{Value, Block, Op};

struct Compiler {
    curr: usize,
    tokens: TokenStream,
}

//TODO rustify
const PREC_NO: u64 = 0;
const PREC_ASSERT: u64 = 1;
const PREC_BOOL: u64 = 2;
const PREC_COMP: u64 = 3;
const PREC_TERM: u64 = 4;
const PREC_FACTOR: u64 = 5;

impl Compiler {
    pub fn new(tokens: TokenStream) -> Self {
        Self {
            curr: 0,
            tokens,
        }
    }

    fn error(&self, msg: &str) -> ! {
        println!("ERROR: {} range {:?}", msg, self.tokens[self.curr].1);
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

    fn precedence(&self, token: Token) -> u64 {
        match token {
            Token::Star | Token::Slash => PREC_FACTOR,

            Token::Minus | Token::Plus => PREC_TERM,

            Token::EqualEqual
                | Token::Greater
                | Token::GreaterEqual
                | Token::Less
                | Token::LessEqual
                | Token::NotEqual
                => PREC_COMP,

            Token::And | Token::Or => PREC_BOOL,

            Token::AssertEqual => PREC_ASSERT,

            _ => PREC_NO,
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
                => self.binary(block),

            Token::EqualEqual
                | Token::Greater
                | Token::GreaterEqual
                | Token::Less
                | Token::LessEqual
                | Token::NotEqual
                => self.comparison(block),

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
        block.add(Op::Constant(value));
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
        self.value(block);
        block.add(op);
    }

    fn binary(&mut self, block: &mut Block) {
        let op = self.eat();

        self.parse_precedence(block, self.precedence(op.clone()) + 1);

        let op = match op {
            Token::Plus => Op::Add,
            Token::Minus => Op::Sub,
            Token::Star => Op::Mul,
            Token::Slash => Op::Div,
            Token::AssertEqual => Op::AssertEqual,
            _ => { self.error("Illegal operator"); }
        };
        block.add(op);
    }

    fn comparison(&mut self, block: &mut Block) {
        let op = self.eat();
        self.parse_precedence(block, self.precedence(op.clone()) + 1);

        let op: &[Op] = match op {
            Token::EqualEqual => &[Op::Equal],
            Token::Less => &[Op::Less],
            Token::Greater => &[Op::Greater],
            Token::NotEqual => &[Op::Equal, Op::Not],
            Token::LessEqual => &[Op::Greater, Op::Not],
            Token::GreaterEqual => &[Op::Less, Op::Not],
            _ => { self.error("Illegal comparison operator"); }
        };
        block.add_from(op);
    }

    fn expression(&mut self, block: &mut Block) {
        self.parse_precedence(block, PREC_NO);
    }

    fn parse_precedence(&mut self, block: &mut Block, precedence: u64) {
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

    pub fn compile(&mut self, name: &str, filename: &str) -> Block {
        let mut block = Block::new(name, filename);

        loop {
            if self.peek() == Token::EOF {
                break;
            }

            self.expression(&mut block);
            block.add(Op::Print);

            if self.eat() != Token::Newline {
                self.error("Invalid expression");
            }
        }
        block.add(Op::Return);

        block
    }
}

pub fn compile(name: &str, filename: &str, tokens: TokenStream) -> Block {
    Compiler::new(tokens).compile(name, filename)
}
