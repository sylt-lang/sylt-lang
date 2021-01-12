
#[derive(Debug)]
pub struct TypeVM {
    stack: Vec<Type>,

    block: Block,
    ip: usize,
}

impl TypeVM {
    fn pop_twice(&mut self) -> (Value, Value) {
        let (a, b) = (self.stack.pop().unwrap(), self.stack.pop().unwrap());
        (b, a)
    }

    fn error(&self, kind: ErrorKind, message: Option<String>) -> Error {
        Error {
            kind,
            file: self.block.file.clone(),
            line: self.block.line(self.ip),
            message,
        }
    }

    pub fn run(&mut self) -> Result<(), Error> {
    }
}
