# How to Contribute to Sylt-lang
First of all - nice to see you here! It's always nice
to get more people to help out with Sylt-lang.

## Prerequisites
Sylt is built with Rust. You'll need a Rust-compiler
to work on sylt. You'll also need to install Lua,
since Sylt compiles to Lua.

## Some useful commands
If you're a command line wizard, nothing here will be new. If you're more
comfortable working in an editor or IDE, feel free to set them up, but
instructions for that aren't listed here.

### Clone the repository
```sh
git clone https://github.com/sylt-lang/sylt-lang.git
```

### Building the Sylt-compiler
```sh
cargo build
```

### Running the test-suite
```sh
cargo test
```

### Running a specific sylt command
```sh
cargo run -- my_sylt_program.sy
```

For all the possible flags that can be given to the
compiler, consult:
```sh
cargo run -- --help
```

## Making edits and merging code
Start by finding an issue. It's the easiest way to make sure
work isn't wasted.

When you have something that works, put up a pull request,
then people can look at it and you can get feedback so you
don't do more than you should.

When you get a passing review you can merge the code.

You'll probably get some feedback in your review which you can
respond to and fix. We iterate until we're all happy with the code.
