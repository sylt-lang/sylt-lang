
#[derive(Debug, Clone, Copy)]
pub enum Value {
    Float(f64),
    Int(i64),
    Bool(bool),
}

#[derive(Debug)]
pub enum Op {
    Pop,
    Constant(Value),
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
        self.ops.push(op);
        self.ops.len()
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

                Op::Print => {
                    println!("PRINT: {:?}", self.stack[0]);
                }

                Op::Return => {
                    return;
                }
            }

            self.ip += 1;
        }
    }
}
