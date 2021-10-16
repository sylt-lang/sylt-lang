use sylt::{lib_bindings, Args, Options};

fn main() -> Result<(), String> {
    let args = Args::parse_args_default_or_exit();
    if args.args.len() == 0 {
        println!("{}", Args::usage());
        return Err("No file to run".into());
    }
    if args.help {
        println!("{}", Args::usage());
        return Ok(());
    }

    let errs = if args.format {
        match sylt::formatter::format(&args) {
            Ok(formatted) => {
                print!("{}", formatted);
                Vec::new()
            }
            Err(errs) => errs,
        }
    } else {
        sylt::run_file(&args, lib_bindings()).err().unwrap_or_else(Vec::new)
    };

    if errs.is_empty() {
        Ok(())
    } else {
        for err in errs.iter() {
            println!("{}", err);
        }
        Err(format!("{} errors occured.", errs.len()))
    }
}
