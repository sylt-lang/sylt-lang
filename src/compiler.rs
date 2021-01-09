use crate::tokenizer::{Token, TokenStream};
use crate::vm::{Value, Block, Op};

struct Compiler {
    curr: usize,
    tokens: TokenStream,
}

//TODO rustify
const PREC_NO: u64 = 0;
const PREC_COMP: u64 = 1;
const PREC_TERM: u64 = 2;
const PREC_FACTOR: u64 = 3;

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
            Token::Minus => PREC_TERM,
            Token::Plus => PREC_TERM,

            Token::Star => PREC_FACTOR,
            Token::Slash => PREC_FACTOR,

            Token::EqualEqual => PREC_COMP,

            _ => PREC_NO,
        }
    }

    fn prefix(&mut self, token: Token, block: &mut Block) -> bool {
        match token {
            Token::LeftParen => self.grouping(block),
            Token::Minus => self.unary(block),

            Token::Float(_) => self.value(block),
            Token::Int(_) => self.value(block),

            _ => { return false; },
        }
        return true;
    }


    fn infix(&mut self, token: Token, block: &mut Block) -> bool {
        match token {
            Token::Minus => self.binary(block),
            Token::Plus  => self.binary(block),

            Token::Slash => self.binary(block),
            Token::Star  => self.binary(block),

            Token::EqualEqual => self.binary(block),

            _ => { return false; },
        }
        return true;
    }

    fn value(&mut self, block: &mut Block) {
        let value = match self.eat() {
            Token::Float(f) => { Value::Float(f) },
            Token::Int(f) => { Value::Int(f) }
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
        if Token::Minus != self.eat() {
            self.error("Expected minus at start of negation.");
        }
        self.value(block);
        block.add(Op::Neg);
    }

    fn binary(&mut self, block: &mut Block) {
        let op = self.eat();

        self.parse_precedence(block, self.precedence(op.clone()) + 1);

        let op = match op {
            Token::Plus => Op::Add,
            Token::Minus => Op::Sub,
            Token::Star => Op::Mul,
            Token::Slash => Op::Div,
            Token::EqualEqual => Op::CompEq,
            _ => { self.error("Illegal operator"); }
        };
        block.add(op);
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

    pub fn compile(&mut self, name: &str) -> Block {
        let mut block = Block::new(name);

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

pub fn compile(name: &str, tokens: TokenStream) -> Block {
    Compiler::new(tokens).compile(name)
}
