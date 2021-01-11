use std::path::{Path, PathBuf};

mod error;
mod tokenizer;
mod vm;
mod compiler;

use error::Error;
use tokenizer::TokenStream;

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
    run(tokenizer::file_to_tokens(path), path)
}

fn run_string(s: &str) -> Result<(), Vec<Error>> {
    run(tokenizer::string_to_tokens(s), Path::new("builtin"))
}

fn run(tokens: TokenStream, path: &Path) -> Result<(), Vec<Error>> {
    match compiler::compile("main", path, tokens) {
        Ok(block) => vm::run_block(block).or_else(|e| Err(vec![e])),
        Err(errors) => Err(errors),
    }
}

#[cfg(test)]
mod tests {
    use super::{run_file, run_string};
    use crate::error::{Error, ErrorKind};
    use std::path::Path;

    macro_rules! assert_errs {
        ($result:expr, [ $( $kind:pat ),* ]) => {
            println!("{} => {:?}", stringify!($result), $result);
            assert!(matches!(
                $result.unwrap_err().as_slice(),
                &[$(Error {
                    kind: $kind,
                    file: _,
                    line: _,
                    message: _,
                },
                )*]
            ))
        };
    }

    #[test]
    fn unreachable_token() {
        assert_errs!(run_string("<!>\n"), [ErrorKind::Unreachable]);
    }

    macro_rules! test_file {
        ($fn:ident, $path:literal) => {
            #[test]
            fn $fn() {
                let file = Path::new($path);
                assert!(run_file(&file).is_ok());
            }
        };
    }
    test_file!(order_of_operations, "tests/order-of-operations.tdy");
    test_file!(variables, "tests/variables.tdy");
    test_file!(scoping, "tests/scoping.tdy");
}
