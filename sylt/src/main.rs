use sylt::{lib_bindings, Args, Options};

fn main() -> Result<(), String> {
    let args = Args::parse_args_default_or_exit();
    if args.help {
        println!("{}", Args::usage());
        return Ok(());
    }

    let functions = lib_bindings();
    let res = sylt::run_file(&args, functions);

    if let Err(errs) = res {
        for err in errs.iter() {
            println!("{}", err);
        }
        return Err(format!("{} errors occured.", errs.len()));
    }
    Ok(())
}
