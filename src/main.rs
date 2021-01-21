use std::path::{Path, PathBuf};

use tihdy::run_file;
use tihdy::vm::Value;

struct Args {
    file: Option<PathBuf>,
    print: bool,
}

fn main() {
    let args = parse_args();
    let file = args.file.unwrap_or_else(|| Path::new("tests/simple.tdy").to_owned());
    if let Err(errs) = run_file(&file, args.print, vec![(String::from("hello"), hello)]) {
        for err in errs.iter() {
            println!("{}", err);
        }
        println!(" {} errors occured.", errs.len());
    }
}

fn parse_args() -> Args {
    let mut args = Args {
        file: None,
        print: false,
    };

    for s in std::env::args().skip(1) {
        let path = Path::new(&s).to_owned();
        if path.is_file() {
            args.file = Some(path);
        } else if "-p" == s {
            args.print = true;
        } else {
            eprintln!("Invalid argument {}.", s);
        }
    };
    args
}

pub fn hello(parameters: &[Value]) -> Value {
    match parameters {
        [Value::String(s)] => {
            println!("{}", s);
        }
        _ => {
            println!("Bad parameters");
        }
    }
    Value::Nil
}
