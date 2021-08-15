use sylt::{lib_bindings, Args, Options};

fn main() -> Result<(), String> {
    let args = Args::parse_args_default_or_exit();
    if args.help {
        println!("{}", Args::usage());
        return Ok(());
    }

    let res = if args.format {
        sylt::formatter::format(&args)
    } else {
        sylt::run_file(&args, lib_bindings())
    };

    if let Err(errs) = res {
        for err in errs.iter() {
            println!("{}", err);
        }
        return Err(format!("{} errors occured.", errs.len()));
    }
    Ok(())
}
