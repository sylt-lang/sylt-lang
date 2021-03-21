# Sylt-lang

![The Sylt mascot](res/sylt.png)

Sylt is a statically checked and dynamically typed reference counted programming
language made for game jams.

## Why does this exist? Why use this instead of language X?

Pfft! We objectively have the best logo.

## Getting started

Sylt is written entirely in Rust. There are two main ways of using it.

1. Depend on this repository in your Cargo.toml.
2. Clone this repository and cargo build. You can then pass .sy-files to the
   resulting binary. Currently this way won't give you any kind of game.

## Basic Usage

Currently, Sylt can only run single files. The last filename given is
run.

The `-v` flag also lets you see some debug output. If you want
to debug the compiler and runtime this might be helpful.

The `-vv` flag gives even more debug output. Don't count on seeing anything
from your own program!

## Endgame

A language that has some form of static typechecking, is easy and fast to work
in. Performance should be good enough that you don't really have to worry about
it.

Dreams exist of automatically recompiling and updating the game while the game is running.
