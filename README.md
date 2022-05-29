# Sylt-lang

![The Sylt mascot](res/sylt.png)
[![codecov](https://codecov.io/gh/sylt-lang/sylt-lang/branch/main/graph/badge.svg?token=3utRo8mH04)](https://codecov.io/gh/sylt-lang/sylt-lang)

Sylt is a statically typed dynamic programming language that compiles to Lua.

For information about how to use the language and get started with writing games
in it, check out our language documentation at https://sylt.rs.

# What makes Sylt unique?

The short version:
 - Strict typechecking that doesn't forces you to specify types
 - High levels of abstractions
 - Fast recompiles
 - Fast runtime
 - Fast iteration times
 - Simplicity in the syntax
 - C-style syntax with the taste of functional

Sylt has become a mix of functional-programming concepts
mixed with more procedural code. The language itself is very small
but still expressive. The typechecker is what sets it apart from
Python and Lua, which usually end up being used for similar use-cases.

The Sylt typechecker is meant to not get in your way, so there's no need to
write types anywhere in your code. If your program is correct
the typechecker will be all fine with it.

This is meant to give the same rapid iteration speed as working in something
like Python or Lua, but with the added peace of mind a strict static
typechecker gives you.

# Sylt and game jams
The language is made for game jams, and has been used in multiple. Unfortunately
the language has been rewritten multiple times between each jam, and since
there's no goal of making Sylt backwards compatible it means there are (currently) no
games made in the most recent verision of the language.

# Some cool small programs
```sylt
fib :: fn a ->
    if a < 2 do
        a
    else
        fib(a - 1) + fib(a - 2)
    end
end

start :: fn do
    fib(23) <=> 28657
end
```
