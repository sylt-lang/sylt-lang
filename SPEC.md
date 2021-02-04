# Sylt-lang
-----------
The language specification, also known as "the less fun" document.

For goals and the like, see the README.md file.

## The syntax by example

I choose to include programs here, that should be valid
in Sylt programs if all goes to plan.

```sylt
a := 1
b : int = a
print(b)  // 1
```
Here we can see variable declaration, types and
the calling of simple functions.

### Definition statement
```sylt
a := 1         // Define a to be 1, automatically infers int as type.
b : int = 1    // Define b to be 1, explicitly as int.
c : int = 0.4  // A compilation error, since types don't match.

// The definition of a function, that takes
// one argument and returns an integer value.
d := fn a: int -> int {
    ret a + 1
}

// Constant
a :: 1
a = 2  // This is illegal

// Destructuring a tuple is allowed, after the definiton
// e = 1, f = 2, g = 3.
// If the number of variables doesn't match the length
// of the tuple, that would raise a compilation error.
e, f, g := (1, 2, 3)

q := 1
q := 1  // You are not allowed to re-declare variables

z := 1
{
    z := z  // This is allowed since this inner z is a differnt variable.
}
```

### If-statements
```sylt
// Basic if-statements
if some_boolean_value {
    do_on_true()
}

// With else statement
if some_boolean_value {
    do_on_true()
} else {
    do_on_false()
}

// If-else statements
if some_boolean_value {
    do_on_true()
} else if some_other_value {
    do_on_second_true()
}
```

### For-loops
```sylt
// 'Normal' For-loop
// Would print numbers 0-9
for i := 0, i < 10, i++ {
    print(i)
}

// 'Enhanced' For-loop
// Would print the numbers 1, 2, 3 and 4
// More precisely, all in the collection
// specified after the 'in' keyword.
for i in (1, 2, 3, 4) {
    print(i)
}

// 'Infinite' For-loop
// The loop would run forever, or until
// a piece of control flow causes it to jump
// out of the loop. Here we use 'break'.
for {
    print(1)
    break;
}

```

### Functions
All functions are values.
```sylt
// Declare and create the function
f :: fn {
    print "A"
}
// Semantically equivalent
f()
f!

// Declare and create the function
f :: fn a:int -> int {
    print a
    ret a + 1
}
// Semantically equivalent
f 1
f(1)

// Closures exist
q := 1
g :: fn -> int {
    ret q  // Here the variable 'q' is captured
}
q = 2
print g!  // prints 2

// Supports heigher order functions
h :: fn -> fn -> int {
    ret fn -> int { ret 2 }
}
print h()()  // prints 2
```

### Special syntax
```sylt
<!>      // The unreachable statement, it should never be executed
1 <=> 1  // Asserts equality, so the program crashes if 1 != 1
```
