use std::path::{Path, PathBuf};

mod error;
mod tokenizer;
mod vm;
mod compiler;

use error::Error;

fn main() {
    let file = file_from_args().unwrap_or_else(|| Path::new("tests/simple.tdy").to_owned());
    if let Err(errs) = run_file(&file) {
        for err in errs.iter() {
            println!("{}", err);
        }
        println!(" {} errors occured.", errs.len());
    }
}

fn file_from_args() -> Option<PathBuf> {
    std::env::args().skip(1).map(|s| Path::new(&s).to_owned()).find(|p| p.is_file())
}

fn run_file(path: &Path) -> Result<(), Vec<Error>> {
    let tokens = tokenizer::file_to_tokens(path);
    match compiler::compile("main", path, tokens) {
        Ok(block) => vm::run_block(block).or_else(|e| Err(vec![e])),
        Err(errors) => Err(errors),
    }

}

#[cfg(test)]
mod tests {
    use super::run_file;
    use std::path::Path;

    #[test]
    fn order_of_operations() {
        let file = Path::new("tests/order-of-operations.tdy");
        assert!(run_file(&file).is_ok());
    }
}
