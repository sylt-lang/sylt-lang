use sylt::{Args, Options};

fn main() -> Result<(), String> {
    let args = Args::parse_args_default_or_exit();
    if args.help {
        println!("{}", Args::usage());
        return Ok(());
    }
    if args.args.len() == 0 {
        println!("{}", Args::usage());
        return Err("No file to run".into());
    }

    let errs = sylt::run_file(&args).err().unwrap_or_else(Vec::new);

    if errs.is_empty() {
        Ok(())
    } else {
        for err in errs.iter() {
            println!("{}", err);
        }
        Err(format!("{} errors occured.", errs.len()))
    }
}
