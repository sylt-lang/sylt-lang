use std::path::{Path, PathBuf};

use tihdy::run_file;

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
