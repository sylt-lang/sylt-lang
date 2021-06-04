use sylt::{Args, Options, lib_bindings};

fn main() -> Result<(), String> {
    let args = Args::parse_args_default_or_exit();
    if args.help {
        println!("{}", Args::usage());
        return Ok(());
    }

    if args.file.is_none() {
        return Err("No file to run".to_string());
    }

    let functions = lib_bindings();
    if args.tree_mode {
        match sylt::tree_compile(&args) {
            Err(errs) => {
                for err in errs.iter() {
                    println!("{}", err);
                }
                Err(format!("{} errors occured.", errs.len()))
            }
            Ok(prog) => {
                for block in prog.blocks {
                    block.borrow().debug_print(Some(&prog.constants));
                }
                Ok(())
            }
        }
    } else {
        let res = sylt::run_file(&args, functions);

        if let Err(errs) = res {
            for err in errs.iter() {
                println!("{}", err);
            }
            return Err(format!("{} errors occured.", errs.len()));
        }
        Ok(())
    }
}
