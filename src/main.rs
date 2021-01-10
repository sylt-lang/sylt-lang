use std::path::{Path, PathBuf};

mod tokenizer;
mod vm;
mod compiler;

fn main() {
    let file = file_from_args().unwrap_or_else(|| Path::new("tests/simple.tdy").to_owned());
    if let Err(err) = run_file(&file) {
        println!("{}", err);
    }
}

fn file_from_args() -> Option<PathBuf> {
    std::env::args().skip(1).map(|s| Path::new(&s).to_owned()).find(|p| p.is_file())
}

fn run_file(path: &Path) -> Result<(), vm::Error> {
    let tokens = tokenizer::file_to_tokens(path);
    let block = compiler::compile("main", path, tokens);  // path -> str might fail
    vm::run_block(block)
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
