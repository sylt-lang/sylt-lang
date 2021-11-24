use colored::Colorize;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

use crate::{Op, Value};

#[derive(Debug)]
pub enum BlockLinkState {
    Linked,
    Nothing,
}

#[derive(Debug)]
pub struct Block {
    pub upvalues: Vec<(usize, bool)>,
    pub linking: BlockLinkState,

    pub namespace: usize,

    pub name: String,
    pub file: PathBuf,
    pub ops: Vec<Op>,
    pub last_line_offset: usize,
    pub line_offsets: HashMap<usize, usize>,
}

impl Block {
    pub fn new(name: &str, namespace: usize, file: &Path) -> Self {
        Self {
            upvalues: Vec::new(),
            linking: BlockLinkState::Nothing,

            namespace,

            name: String::from(name),
            file: file.to_owned(),
            ops: Vec::new(),
            last_line_offset: 0,
            line_offsets: HashMap::new(),
        }
    }

    pub fn add_line(&mut self, token_position: usize) {
        if token_position != self.last_line_offset {
            self.line_offsets.insert(self.curr(), token_position);
            self.last_line_offset = token_position;
        }
    }

    pub fn line(&self, ip: usize) -> usize {
        for i in (0..=ip).rev() {
            if let Some(line) = self.line_offsets.get(&i) {
                return *line;
            }
        }
        0
    }

    pub fn debug_print(&self, constants: Option<&[Value]>) {
        println!("     === {} ===", self.name.blue());
        for (i, s) in self.ops.iter().enumerate() {
            #[rustfmt::skip]
            println!(
                "{}{:05} {:?}{}",
                if self.line_offsets.contains_key(&i) {
                    format!("{:5} ", self.line_offsets[&i].to_string().blue())
                } else {
                    format!("    {} ", "|".blue())
                },
                i.to_string().red(),
                s,
                match (s, constants) {
                    (Op::Constant(c), Some(constants))
                    | (Op::Link(c), Some(constants))
                      => format!("    => {:?}", &constants[*c]),
                    _ => "".to_string(),
                }
            );
        }
        println!();
    }

    pub fn add(&mut self, op: Op, token_position: usize) -> usize {
        let len = self.curr();
        self.add_line(token_position);
        self.ops.push(op);
        len
    }

    pub fn curr(&self) -> usize {
        self.ops.len()
    }
}
