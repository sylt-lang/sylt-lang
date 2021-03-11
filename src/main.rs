use std::path::Path;

use sylt::{run_file, Args};

fn main() -> Result<(), String> {
    let args = parse_args();
    let errs = match run_file(args, sylt_macro::link!(
        sylt::dbg as dbg,
        sylt::push as push,
        sylt::len as len,
    )) {
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

