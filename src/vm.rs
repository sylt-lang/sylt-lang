
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum Value {
    Float(f64),
    Int(i64),
    Bool(bool),
}

#[derive(Debug, Clone, Copy)]
pub enum Op {
    Pop,
    Constant(Value),

    Add,
    Sub,
    Mul,
    Div,
    Neg,

    And,
    Or,
    Not,

    Equal,   // ==
    Less,    // <
    Greater, // >

    AssertEqual,

    Print,
    Return,
}

#[derive(Debug)]
pub struct Block {
    name: String,
    ops: Vec<Op>,
}

impl Block {
    pub fn new(name: &str) -> Self {
        Self {
            name: String::from(name),
            ops: Vec::new(),
        }
    }

    pub fn add(&mut self, op: Op) -> usize {
        let len = self.ops.len();
        self.ops.push(op);
        len
    }

    pub fn add_from(&mut self, ops: &[Op]) -> usize {
        let len = self.ops.len();
        for op in ops {
            self.add(*op);
        }
        len
    }
}

#[derive(Debug)]
pub struct VM {
    stack: Vec<Value>,

    block: Block,
    ip: usize,
}

pub fn run_block(block: Block) {
    let mut vm = VM {
        stack: Vec::new(),

        block,
        ip: 0,
    };

    vm.run();
}

impl VM {
    fn pop_twice(&mut self) -> (Value, Value) {
        let (a, b) = (self.stack.pop().unwrap(), self.stack.pop().unwrap());
        (b, a)
    }

    fn _peek_up(&self, amount: usize) -> Option<&Value> {
        self.stack.get(self.stack.len() - amount)
    }

    pub fn run(&mut self) {
        const PRINT_WHILE_RUNNING: bool = true;
        const PRINT_BLOCK: bool = true;

        if PRINT_BLOCK {
            println!(" === {} ===", self.block.name);
            for s in self.block.ops.iter() {
                println!("| {:?}", s);
            }
            println!("");
        }

        loop {
            if PRINT_WHILE_RUNNING {
                print!("    [");
                for s in self.stack.iter() {
                    print!("{:?} ", s);
                }
                println!("]");

                println!("{:?}", self.block.ops[self.ip]);
            }

            match self.block.ops[self.ip] {
                Op::Pop => {
                    self.stack.pop();
                }

                Op::Constant(value) => {
                    self.stack.push(value);
                }

                Op::Neg => {
                    let a = self.stack.pop().unwrap();
                    match a {
                        Value::Float(a) => self.stack.push(Value::Float(-a)),
                        Value::Int(a) => self.stack.push(Value::Int(-a)),
                        _ => unimplemented!("Cannot negate '{:?}'.", a),
                    }
                }

                Op::Add => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(b + a)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(b + a)),
                        (a, b) => unimplemented!("Cannot add '{:?}' and '{:?}'.", a, b),
                    }
                }

                Op::Sub => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(b - a)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(b - a)),
                        (a, b) => unimplemented!("Cannot sub '{:?}' and '{:?}'.", a, b),
                    }
                }

                Op::Mul => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(b * a)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(b * a)),
                        (a, b) => unimplemented!("Cannot mul '{:?}' and '{:?}'.", a, b),
                    }
                }

                Op::Div => {
                    match self.pop_twice() {
                        (Value::Float(a), Value::Float(b)) => self.stack.push(Value::Float(b / a)),
                        (Value::Int(a), Value::Int(b)) => self.stack.push(Value::Int(b / a)),
                        (a, b) => unimplemented!("Cannot mul '{:?}' and '{:?}'.", a, b),
                    }
                }

                Op::Equal => {
                    let (a, b) = self.pop_twice();
                    self.stack.push(Value::Bool(a == b));
                }

                Op::Less => {
                    let (a, b) = self.pop_twice();
                    self.stack.push(Value::Bool(a < b));
                }

                Op::Greater => {
                    let (a, b) = self.pop_twice();
                    self.stack.push(Value::Bool(a > b));
                }

                Op::And => {
                    match self.pop_twice() {
                        (Value::Bool(a), Value::Bool(b)) => self.stack.push(Value::Bool(a && b)),
                        (a, b) => unimplemented!("Cannot 'and' {:?} and {:?}", a, b),
                    }
                }

                Op::Or => {
                    match self.pop_twice() {
                        (Value::Bool(a), Value::Bool(b)) => self.stack.push(Value::Bool(a || b)),
                        (a, b) => unimplemented!("Cannot 'or' {:?} and {:?}", a, b),
                    }
                }

                Op::Not => {
                    match self.stack.pop().unwrap() {
                        Value::Bool(a) => self.stack.push(Value::Bool(!a)),
                        a => unimplemented!("Cannot 'not' {:?}", a),
                    }
                }

                Op::AssertEqual => {
                    let (a, b) = self.pop_twice();
                    if a != b {
                        println!("Assert failed for '{:?}' and '{:?}'", a, b);
                    }
                    self.stack.push(Value::Bool(a == b));
                }

                Op::Print => {
                    println!("PRINT: {:?}", self.stack.pop());
                }

                Op::Return => {
                    return;
                }
            }
            self.ip += 1;
        }
    }
}
