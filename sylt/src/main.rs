use std::path::PathBuf;
use sylt::{Args, Options};

sylt_macro::timed_init!();

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

    sylt_macro::timed_set_t0!();

    let errs = if args.format {
        match sylt::formatter::format(&PathBuf::from(args.args.first().unwrap())) {
            Ok(formatted) => {
                print!("{}", formatted);
                Vec::new()
            }
            Err(errs) => errs,
        }
    } else {
        sylt::run_file(&args).err().unwrap_or_else(Vec::new)
    };

    #[cfg(feature = "timed")]
    if let Some(outfile) = &args.trace_output {
        let output = sylt_macro::timed_trace!(sylt, sylt_compiler, sylt_parser);

        if outfile == &std::path::Path::new("-") {
            eprintln!("{}", output,);
        } else {
            if let Err(e) = std::fs::write(outfile, output)
                .map_err(|e| format!("failed to write trace to file: {}", e))
            {
                eprintln!("{}", e);
            }
        };
    }

    if errs.is_empty() {
        Ok(())
    } else {
        for err in errs.iter() {
            println!("{}", err);
        }
        Err(format!("{} errors occured.", errs.len()))
    }
}
