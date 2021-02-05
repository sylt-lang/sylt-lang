# Sylt-lang

The language specification, also known as the "less fun" document.

For goals and the like, see the README.md.

## The syntax by example

We choose to include programs here. They should be valid Sylt programs if all
goes to plan.

```sylt
a := 1
b : int = a
print(b)  // 1
```

Here we can see variable declaration, types and calling of simple functions.

### Definition statement

```sylt
a := 1         // Define a to be 1. automatically infers int as type.
b : int = 1    // Define b to be 1, explicitly as int
c : int = 0.4  // Invalid: Types don't match

// The definition of a function that takes
// one argument and returns an integer value.
d := fn a: int -> int {
    ret a + 1
}

// Constant
a :: 1
a = 2  // Invalid

// Destructuring a tuple is allowed. After the definiton we have:
// e = 1, f = 2, g = 3.
//
// The number of variables need to match the length of the tuple.
e, f, g := (1, 2, 3)
h, i := (1, 2, 3)  // Invalid

q := 1
q := 1  // Invalid: You are not allowed to re-declare variables

z := 1
{
    z := z  // Valid: The inner z is a different variable
}
```

### If-statements

```sylt
// Basic if-statement
if some_boolean_value {
    do_on_true()
}

// With else-statement
if some_boolean_value {
    do_on_true()
} else {
    do_on_false()
}

// If-else-statements
if some_boolean_value {
    do_on_true()
} else if some_other_value {
    do_on_second_true()
}
```

### For-loops

```sylt
// 'Normal' for-loop
// Prints the numbers 0-9
for i := 0, i < 10, i++ {
    print(i)
}

// 'Enhanced' for-loop
// Iterates over the collection after 'in'.
// This example prints the numbers 1, 2, 3 and 4 in order.
for i in (1, 2, 3, 4) {
    print(i)
}

// 'Infinite' for-loop
// The loop will run forever, or until
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
// Declare and create a function
f :: fn {
    print "A"
}
// These are semantically equivalent
f()
f!

// Declare and create a function
f :: fn a: int -> int {
    print a
    ret a + 1
}
// These are semantically equivalent
f 1
f(1)

// Closures exist
q := 1
g :: fn -> int {
    ret q  // Here the variable 'q' is captured
}
q = 2
print g!  // prints 2

// Supports higher-order-functions
h :: fn -> fn -> int {
    ret fn -> int { ret 2 }
}
print h()()  // prints 2
```

### Special syntax

```sylt
<!>      // The unreachable statement. If it is executed the program halts.
1 <=> 1  // Asserts equality. If the assert fails the program halts.
```
