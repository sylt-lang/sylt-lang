# Sylt-lang

![The Sylt mascot](res/sylt.png)

Sylt is a statically checked and dynamically typed reference counted programming
language made for game jams.

## Why does this exist? Why use this instead of language X?

Pfft! We objectively have the best logo.

## Getting started

Sylt is written entirely in Rust. There are two main ways of using it.

### New repository

1. `$ cargo new <game name>`
2. Add this to your Cargo.toml:
```toml
[dependencies.sylt]
git = "https://github.com/FredTheDino/sylt-lang.git"
branch = "main"
features = [ "lingon" ]
```
3. Add something like this to your `src/main.rs`:
```rust
use std::path::Path;

fn main() {
    let args = sylt::Args {
        file: Some(Path::new("game.sy").to_path_buf()),  // or read from args
        is_binary: false,
        compile_target: None,
        verbosity: 0,
        help: false,
    };

    sylt::run_file(&args, sylt::lib_bindings()).unwrap();
}
```
4. Write your game! Here's an example to get you started:
```
x := 0.0
y := 0.0

init :: fn {
    l_bind_key("w", "up")
    l_bind_key("a", "left")
    l_bind_key("s", "down")
    l_bind_key("d", "right")

    l_bind_quit("quit")
    l_bind_key("ESCAPE", "quit")
}

update :: fn delta: float -> void {
    x += (l_input_value("right") - l_input_value("left")) * delta
    y += (l_input_value("up") - l_input_value("down")) * delta
}

draw :: fn {
    rgb :: (sin(l_time()), cos(l_time()), 0.0)
    l_gfx_rect! x, y, 1.0, 1.0, rgb
}

start :: fn {
    init!
    for _ in inf(0) {
        _
        if l_input_down("quit") {
            break
        }
        l_update!
        update! l_delta!
        draw!
        l_render!
    }
}
```
5. `$ cargo run` to your heart's content.

### Fork

Forking sylt and hacking away makes it easy to do changes to the language, the
standard library and the bindings to Lingon, of which the latter two are
probably more interesting.

0. Setup a fork. (Optional)
1. Clone the repository.
2. `$ cargo run <your-game.sy>`

## Basic Usage

The `-v` flag also lets you see some debug output. If you want
to debug the compiler and runtime this might be helpful.

The `-vv` flag gives even more debug output. Don't count on seeing anything
from your own program!

## Endgame

A language that has some form of static typechecking, is easy and fast to work
in. Performance should be good enough that you don't really have to worry about
it.

Dreams exist of automatically recompiling and updating the game while the game is running.
