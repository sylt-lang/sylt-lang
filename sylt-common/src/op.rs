/// Ops are operations that the virtual
/// machine carries out when running the
/// "byte-code".
///
#[derive(Debug, Copy, Clone)]
pub enum Op {
    /// This instruction should never be run.
    /// Finding it in a program is a critical error.
    Illegal,

    /// Pops one value from the stack.
    ///
    /// {A, B} - Pop - {A}
    Pop,
    /// Assumes the value on the top of the
    /// stack has an upvalue, and closes that
    /// upvalue.
    ///
    /// {A, B} - Pop - {A}
    PopUpvalue,
    /// Copies the N values on the top of the stack
    /// and puts them on top of the stack.
    ///
    /// {A, B} - Copy(2) - {A, B, A, B}
    Copy(usize),
    /// Swaps the two top stack elements.
    ///
    /// {A, B} - Swap(2) - {B, A}
    Swap,
    /// Adds the value indexed in the `constants-vector` to the top of the stack.
    /// Also links upvalues if the value is a function.
    ///
    /// {A} - Constant(B) - {A, B}
    Constant(usize),

    /// Creates a new [Value::Tuple] with the given size and place it on the top
    /// of the stack.
    ///
    /// {A, B, C} - Tuple(3) - {D(A, B, C)}
    Tuple(usize),
    /// Creates a new [Value::List] with the given size and place it on the top
    /// of the stack.
    ///
    /// {A, B, C} - List(3) - {D(A, B, C)}
    List(usize),
    /// Creates a new [Value::Set] with the given elements and place it on the top
    /// of the stack.
    ///
    /// {A, B, A} - Set(3) - {D(A, B)}
    Set(usize),
    /// Creates a new [Value::Dict] with the given elements and place it on the top
    /// of the stack.
    ///
    /// {A, B, C, D, A, E} - Dict(6) - {D(A:E, C:D)}
    Dict(usize),

    /// Indexes something indexable,
    /// and adds that element to the stack.
    ///
    /// {T, I} - Index - {T[I]}
    GetIndex,
    /// Indexes something indexable with a constant integer,
    /// and adds that element to the stack.
    ///
    /// {T} - Index(I) - {T[I]}
    GetConstIndex(i64),
    /// Assigns the indexes of something indexable.
    /// T[I] = V
    ///
    /// {T, I, V} - Index - {}
    AssignIndex,
    /// Looks up a field by the given name
    /// and replaces the parent with it.
    /// Currently only expects [Value::Blob].
    /// (name is looked up in the internal string-list)
    ///
    /// {O} - Get(F) - {O.F}
    Contains,
    /// Checks if the given value is inside the container.
    /// Pushes a bool to the stack.
    ///
    /// {I, A} - Contains - {I in A}
    GetField(usize),
    /// Looks up a field by the given name
    /// and replaces the current value in the object.
    /// Currently only expects [Value::Blob].
    /// (name is looked up in the internal string-list)
    ///
    /// {O} - Set(F) - {}
    AssignField(usize),

    /// Adds the two top elements on the stack,
    /// using the function [op::add]. The result
    /// is the pushed.
    ///
    /// {A, B} - Add - {A + B}
    Add,
    /// Sub the two top elements on the stack,
    /// using the function [op::sub]. The result
    /// is the pushed.
    ///
    /// {A, B} - Sub - {A - B}
    Sub,
    /// Multiples the two top elements on the stack,
    /// using the function [op::mul]. The result
    /// is the pushed.
    ///
    /// {A, B} - Mul - {A - B}
    Mul,
    /// Divides the two top elements on the stack,
    /// using the function [op::div]. The result
    /// is the pushed.
    ///
    /// {A, B} - Div - {A / B}
    Div,
    /// Negates the top element on the stack.
    ///
    /// {A} - Neg - {-A}
    Neg,

    /// Performs a boolean and on the
    /// top 2 stack elements using [op::and].
    ///
    /// {A, B} - And - {A && B}
    And,
    /// Performs a boolean or on the
    /// top 2 stack elements using [op::or].
    ///
    /// {A, B} - Or - {A || B}
    Or,
    /// Performs a boolean not on the
    /// top stack element using [op::not].
    ///
    /// {A} - Not - {!A}
    Not,

    /// Checks if the type of the value on the left
    /// is the type on the right.
    ///
    /// {A, B} - Is - {A is B}
    Is,

    /// Sets the instruction pointer
    /// to the given value.
    ///
    /// Does not affect the stack.
    Jmp(usize),
    /// Sets the instruction pointer
    /// to the given value, if the
    /// topmost value is false, also
    /// pops this value.
    ///
    /// {A} - JmpFalse(n) - {}
    JmpFalse(usize),
    /// Sets the instruction pointer
    /// to the given value and pops
    /// the given amount of values.
    ///
    /// Used for 'break' and 'continue'.
    ///
    /// {A, B, C} - JmpNPop(n, 2) - {A}
    JmpNPop(usize, usize),

    /// Compares the two topmost elements
    /// on the stack for equality, and pushes
    /// the result. Compares using [op::eq].
    ///
    /// {A, B} - Equal - {A == B}
    Equal,
    /// Compares the two topmost elements
    /// on the stack for order, and pushes the result.
    /// Compares using [op::less].
    ///
    /// {A, B} - Less - {A < B}
    Less,
    /// Compares the two topmost elements
    /// on the stack for order, and pushes the result.
    /// Compares using [op::less].
    ///
    /// {A, B} - Greater - {B < A}
    Greater,

    /// Pops the top value of the stack, and
    /// crashes the program if it is false.
    ///
    /// {A} - Assert - {}
    Assert,
    /// This instruction should not be executed.
    /// If it is the program crashes.
    ///
    /// Does not affect the stack.
    Unreachable,

    /// Reads the value counted from the
    /// bottom of the stack and adds it
    /// to the top.
    ///
    /// {A, B} - ReadLocal(0) - {A, B, A}
    ReadLocal(usize),
    /// Sets the value at the given index
    /// of the stack, to the topmost value.
    /// Pops the topsmost element.
    ///
    /// {A, B} - AssignLocal(0) - {B}
    AssignLocal(usize),

    /// Reads the upvalue, and adds it
    /// to the top of the stack.
    ///
    /// {} - ReadUpvalue(0) - {A}
    ReadUpvalue(usize),
    /// Sets the given upvalue, and pops
    /// the topmost element.
    ///
    /// {A} - AssignUpvalue(0) - {}
    AssignUpvalue(usize),

    /// Reads the global, and adds it
    /// to the top of the stack.
    ///
    /// Globals are stored at the bottom
    /// of the stack and initalized when
    /// the program starts.
    ///
    /// {} - ReadGlobal(0) - {C}
    ReadGlobal(usize),
    /// Sets the given constant, and pops
    /// the topmost element.
    ///
    /// {A} - AssignGlobal(0) - {}
    AssignGlobal(usize),

    /// A helper instruction for the type checker.
    /// *Makes sure* that the top value on the stack
    /// is of the given type, and is meant to signal
    /// that the "variable" is added.
    /// (The type is looked up in the constants vector.)
    ///
    /// Does not affect the stack.
    Define(usize),
    /// A helper instruction for the typechecker,
    /// *assumes* top value on the stack
    /// is of the given type. Usefull for helping the
    /// type system where it just can't do it.
    /// (The type is looked up in the constants vector)
    ///
    /// Does not affect the stack.
    Force(usize),
    /// A helper instruction for the typechecker,
    /// *combines* the two top value on the stack
    /// into a union type.
    ///
    /// Skipped in the runtime.
    /// In the typechecker:
    /// {A, B} - Union - {A | B}
    Union,

    /// Links the upvalues for the given constant
    /// function. This updates the constant stack.
    ///
    /// Does not affect the stack.
    Link(usize),

    /// Calls "something" with the given number
    /// of arguments. The callable value is
    /// then replaced with the result.
    ///
    /// Callable things are: [Value::Blob], [Value::Function],
    /// and [Value::ExternFunction].
    ///
    /// {F, A, B} - Call(2) - {F(A, B)}
    Call(usize),

    /// Prints and pops the top value on the stack.
    ///
    /// {A} - Print - {}
    Print,

    /// Pops the current stackframe and replaces
    /// slot 0 with the top value. Also pops
    /// upvalues.
    ///
    /// {F, A, B} - Return - {..., B}
    Return,

    /// Temporarily stops execution and returns
    /// to the call site.
    ///
    /// Does not affect the stack.
    Yield,
}

#[derive(Eq, PartialEq)]
pub enum OpResult {
    Yield,
    Done,

    // Will never be returned.
    #[doc(hidden)]
    Continue,
}

