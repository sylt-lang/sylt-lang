# Sylt-lang
-----------
Sylt is a statically checked and dynamically typed reference counted programming
language made for game jams.


## Why does this exist? Why use this instead of language X?
Pfft! Why not?
    

## Getting started
Sylt is written entirely in Rust. Pointing to this Git-repo 
in your Cargo.toml is the easiest way. Alternatively you can
build the interpreter and run your own programs from there.

```
git clone git@github.com:FredTheDino/sylt-lang.git
cargo build --release
```
This will build `target/release/sylt`, wich is the interpreter.
If you want to install it, do so.


## Basic Usage
Currently, Sylt can only run single files. The last filename given is
run.

The `-p` flag also lets you see alot of debug output, if you want
to debug the program this might be helpfull.

## Endgame
A language that has some form of static typechecking, is easy and fast to work
in. Performance should be good enought that you don't really have to worry
about it.

Dreams also exist of automatically updating the game when files are changed.
