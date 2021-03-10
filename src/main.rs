use std::path::Path;

use sylt::{run_file, Args};

fn main() {
    let args = parse_args();
    let errs = match run_file(args, sylt_macro::link!(extern_test as test)) {
        Err(it) => it,
        _ => return,
    };
    for err in errs.iter() {
        println!("{}", err);
    }
    println!(" {} errors occured.", errs.len());
}

fn parse_args() -> Args {
    let mut args = Args::default();

    for s in std::env::args().skip(1) {
        let path = Path::new(&s).to_owned();
        if path.is_file() {
            args.file = Some(path);
        } else if s == "-v" {
            args.print_exec = true;
        } else if s == "-vv" {
            args.print_exec = true;
            args.print_bytecode = true;
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
