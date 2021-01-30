use std::path::{Path, PathBuf};

use tihdy::run_file;

struct Args {
    file: Option<PathBuf>,
    print: bool,
}

fn main() {
    let args = parse_args();
    let file = args.file.unwrap_or_else(|| Path::new("tests/simple.tdy").to_owned());
    let errs = match run_file(&file, args.print, vec![(String::from("extern_test"), extern_test)]) {
        Err(it) => it,
        _ => return,
    };
    for err in errs.iter() {
        println!("{}", err);
    }
    println!(" {} errors occured.", errs.len());
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

tihdy_derive::extern_function!(
    extern_test
    [tihdy::vm::Value::Float(x), tihdy::vm::Value::Float(y)] -> tihdy::vm::Type::Float => {
        Ok(tihdy::vm::Value::Float(x + y))
    },
    [tihdy::vm::Value::Float(x)] -> tihdy::vm::Type::Float => {
        Ok(tihdy::vm::Value::Float(*x))
    },
);
