use gumdrop::Options;

use sylt::{run_file, Args};

fn main() -> Result<(), String> {
    let args = Args::parse_args_default_or_exit();
    if args.file.is_none() {
        return Err("No file to run".to_string());
    }

    // let prog = sylt::deserialize(std::fs::read(args.file.clone().unwrap()).unwrap()).unwrap();
    // sylt::run(prog, &args).unwrap();

    // let bytes = sylt::serialize(&args).unwrap();
    // let mut dest = std::fs::File::create("game.bin").unwrap();
    // dest.write_all(&bytes).unwrap();

    let errs = match run_file(
        &args,
        sylt_macro::link!(sylt::dbg as dbg, sylt::push as push, sylt::len as len,),
    ) {
        Err(it) => it,
        _ => return Ok(()),
    };
    for err in errs.iter() {
        println!("{}", err);
    }
    Err(format!("{} errors occured.", errs.len()))
}
