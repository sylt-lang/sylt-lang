use gumdrop::Options;
use std::path::PathBuf;
use std::time::Instant;

#[derive(Default, Debug, Options)]
pub struct Args {
    #[options(free, required, help = "The file to run")]
    pub run_file: PathBuf,

    #[options(short = "r", long = "runs", help = "If set, how many times the program should be run at most")]
    pub max_runs: Option<usize>,

    #[options(short = "t", long = "time", help = "If set, stop running when this amount of seconds have passed")]
    pub max_time: Option<u64>,

    #[options(help = "Print this help")]
    pub help: bool,
}

fn main() -> std::io::Result<()> {
    let args = Args::parse_args_default_or_exit();
    if args.help {
        eprintln!("{}", Args::usage());
        return Ok(());
    }

    let sylt_args = sylt::Args {
        file: Some(args.run_file),
        is_binary: false,
        compile_target: None,
        verbosity: 0,
        help: false,
        ..Default::default()
    };

    eprintln!("Compiling");
    let functions = sylt::lib_bindings();
    let prog = match sylt::compile(&sylt_args, functions) {
        Ok(prog) => prog,
        Err(errs) => {
            for err in errs {
                eprintln!("{}", err);
            }
            return Ok(());
        }
    };

    eprintln!("Running once");
    // Run once and report any errors
    match sylt::run(&prog, &sylt_args) {
        Ok(_) => (),
        Err(errs) => {
            eprintln!("Runtime error(s):");
            for err in errs {
                eprintln!("{}", err);
            }
            return Ok(());
        }
    }
    let mut runtimes = Vec::new();

    eprintln!("Starting runs");
    let outer_start = Instant::now();
    loop {
        if let Some(max_runs) = args.max_runs {
            if runtimes.len() >= max_runs {
                break;
            }
        }
        if let Some(max_time) = args.max_time {
            if (Instant::now() - outer_start).as_secs() >= max_time {
                break;
            }
        }

        let start = Instant::now();
        let _ = sylt::run(&prog, &sylt_args).unwrap();
        let runtime = Instant::now() - start;
        runtimes.push(runtime.as_micros());
    }

    for runtime in runtimes {
        println!("{}", runtime);
    }
    Ok(())
}
