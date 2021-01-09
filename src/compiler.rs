use crate::tokenizer::{Token, TokenStream};
use crate::vm::{Value, Block, Op};

struct Compiler {
    curr: usize,
    tokens: TokenStream,
}

impl Compiler {
    pub fn new(tokens: TokenStream) -> Self {
        Self {
            curr: 0,
            tokens,
        }
    }

    fn error(&self, msg: &str) -> ! {
        println!("ERROR: {}", msg);
        panic!();
    }

    fn peek(&self) -> Token {
        if self.tokens.len() < self.curr {
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

    fn value(&mut self) -> Value {
        match self.eat() {
            Token::Float(f) => { Value::Float(f) },
            Token::Int(f) => { Value::Int(f) }
            _ => { self.error("Invalid value.") }
        }
    }

    fn expression(&mut self, block: &mut Block) {
        let a = self.value();
        block.add(Op::Constant(a));

        loop {
            println!("{:?}", self.peek());
            let op = match self.eat() {
                Token::Plus => Op::Add,
                Token::Minus => Op::Sub,
                Token::Star => Op::Mul,
                Token::Slash => Op::Div,
                _ => { break; }
            };

            let b = self.value();
            block.add(Op::Constant(b));
            block.add(op);
        }
    }

    pub fn compile(&mut self, name: &str) -> Block {
        let mut block = Block::new(name);

        self.expression(&mut block);
        block.add(Op::Print);
        block.add(Op::Return);

        block
    }
}

pub fn compile(name: &str, tokens: TokenStream) -> Block {
    Compiler::new(tokens).compile(name)
}
