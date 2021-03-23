use gumdrop::Options;
use std::io::Write;

use sylt::{Args, RustFunction};

fn main() -> Result<(), String> {
    let args = Args::parse_args_default_or_exit();
    if args.help {
        println!("{}", Args::usage());
        return Ok(());
    }

    if args.file.is_none() {
        return Err("No file to run".to_string());
    }

    let functions: Vec<(String, RustFunction)> = sylt_macro::link!(sylt::dbg as dbg, sylt::push as push, sylt::len as len);

    let res = if args.is_binary {
        match sylt::deserialize(std::fs::read(args.file.clone().unwrap()).unwrap()) {
            Ok(prog) => sylt::run(&prog, &args),
            Err(e) => Err(e)
        }
    } else if let Some(compile_target) = &args.compile_target {
        match sylt::serialize(&args, functions) {
            Ok(bytes) => {
                let mut dest = std::fs::File::create(compile_target).unwrap();
                dest.write_all(&bytes).unwrap();
                Ok(())
            }
            Err(e) => Err(e),
        }
    } else {
        sylt::run_file(&args, functions)
    };


    if let Err(errs) = res {
        for err in errs.iter() {
            println!("{}", err);
        }
        return Err(format!("{} errors occured.", errs.len()));
    }
    Ok(())
}
