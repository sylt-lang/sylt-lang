use std::path::{Path, PathBuf};

use sylt::run_file;

struct Args {
    file: Option<PathBuf>,
    print: bool,
}

fn main() {
    let args = parse_args();
    let file = args.file.unwrap_or_else(|| Path::new("progs/tests/simple.sy").to_owned());
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

sylt_macro::extern_function!(
    extern_test
    [sylt::Value::Float(x), sylt::Value::Float(y)] -> sylt::Type::Float => {
        Ok(sylt::Value::Float(x + y))
    },
    [sylt::Value::Float(x)] -> sylt::Type::Float => {
        Ok(sylt::Value::Float(*x))
    },
);
