use std::path::Path;

use sylt::{run_file, Args};

fn main() -> Result<(), String> {
    let args = parse_args();
    if args.file.is_none() {
        return Err("No file to run".to_string());
    }
    let errs = match run_file(args, sylt_macro::link!(extern_test as test)) {
        Err(it) => it,
        _ => return Ok(()),
    };
    for err in errs.iter() {
        println!("{}", err);
    }
    Err(format!("{} errors occured.", errs.len()))
}

fn parse_args() -> Args {
    let mut args = Args::default();

    for s in std::env::args().skip(1) {
        let path = Path::new(&s).to_owned();
        if path.is_file() {
            args.file = Some(path);
        } else if s == "-v" {
            args.print_bytecode = true;
        } else if s == "-vv" {
            args.print_bytecode = true;
            args.print_exec = true;
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
