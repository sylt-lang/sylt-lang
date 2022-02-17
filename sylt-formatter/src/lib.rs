use gumdrop::Options;

#[derive(Default, Debug, Options)]
pub struct Args {
    #[options(free)]
    pub args: Vec<String>,
}

impl Args {
    /// Wraps the function with the same name from [gumdrop] for convenience.
    pub fn parse_args_default_or_exit() -> Args {
        <Args as Options>::parse_args_default_or_exit()
    }
}
