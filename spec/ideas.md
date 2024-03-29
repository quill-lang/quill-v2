# Requirements

Quill should be, first and foremost, a functional efficient programming language.
That definition necessitates the following list of requirements.
Note that any requirement placed higher up on the list supercedes those lower down, if they conflict.

## High priority

Functional programming paradigms should be idiomatic.
The list of absolute requirements includes:

1. a strict type system, including
   1. higher-order functions, and functions as first-class objects
   2. functors, monads, and other higher-kinded types
2. an immutability-by-default paradigm, including
   1. pure-by-default functions
   2. referential transparency by default
   3. recursion to be favoured over iteration

Quill is also an efficient programming language.
Here, "efficient" refers to performance and reliability, both at runtime and while programming.
It aims to occupy a similar space to Rust or Zig, but in the space of functional languages.
Therefore, we also require:

1. reliability of performance, including
   1. absence of a thunk-based computation model
   2. no garbage collector, favouring an ownership model of memory management
   3. no runtime at all
2. speed, in particular
   1. ahead-of-time compilation
   2. heavy compile-time optimisation, with the aim to match the performance of C/Zig
   3. zero-cost abstractions, such as conversion of higher-kinded functions to regular functions where values are known at compile-time, or translations of monadic effect systems into impure functions
   4. eager evaluation by default

## Useful features

1. arbitrary compile-time calculation in Quill itself, including a "must evaluate at compile time" keyword
2. a type system potentially based on [homotopy type theory](https://homotopytypetheory.org/book/)
3. a compile-time analogue of Julia's multiple dispatch, similar to Rust's specialisation but generalisable

# Modular design

The Quill compiler and standard library should be split into four hierarchical levels:

1. the compiler itself, and then
2. `lang`
3. `core`
4. `std`

## Compiler

The compiler is the lowest level of the chain, and may be written in an arbitrary language, such as Rust, or even Quill itself.
Its objectives are

1. convert streams of Unicode code points into streams of tokens
2. convert streams of tokens into untyped syntax trees, taking into account operator precedence, which itself must be an input to the program
3. manage file systems and module hierarchies, and resolve names to unique identifiers
4. deduce and check consistency of types on untyped syntax trees, which may contain type hints
5. process type-checked syntax trees into Feather IL
6. execute arbitrary Feather code without compilation
7. translate arbitrary Feather code into LLVM IR or other IRs

These objectives need not be part of the same program, they should be designed to work independently.

## `lang`

Much of Quill should be based around the idea of convenient syntax extensions for accomplishing specific common tasks.
In an important way, the language itself is directly manipulable, down to the syntax level.
Of course, there is a requirement that a certain base syntax exists for the purpose of creating a springboard from which more complicated syntax can be formed.
In particular, any syntax extensions should be written inside the `lang` module.

For example, closures and lambdas are not core parts of the language.
They are implemented as a syntax extension which is enabled by default in any Quill project, like most of the features in the `lang` module.

## `core`

This module should essentially be a prelude; containing useful types and functions used in almost all Quill programs.
Examples include `Maybe` types, functor utilities such as `map`, and syntax extensions for monadic blocks.

# Feather

The Feather IL is a strongly-typed functional intermediate language.
It is minimal, yet contains all necessary features for implementing a robust programming language.

## The type system

What are all of the things you can do to a type?
If you know the fields in a type, you can

- construct an element of that type, given fields of relevant types
- deconstruct an object of that type, returning a tuple of fields of relevant types
- borrow fields of an object of that type, returning a field of relevant type, with a lifetime equivalent to the length of the borrow

Even if you do not know the fields, you can also

- pass it around into functions, which could be generic functions or even type constructors
- compare equality of types

## Creating types

Equality is defined to be true if the types were generated by the same parameters to a function call that called `make_type`.
In some respects, a type's 'name' is essentially the name of the function that called `make_type`.
However, this glosses over an important subtlety - a function may make a type, use it, and not return it.
So we must not only keep track of which parameters were used in the function call, but also where in the function it was created.
This definition is sufficient, since functions may not in principle depend on anything outside their function scope and their parameter list, so this is a complete description of the type.
Static variables are an important exception, but their values only exist at runtime, so since types are compile-time constructs, and so static variables cannot be accessed at compile-time, this should not matter.

## Types in data structures

Generalisations of traits, as seen in Rust, can be implemented directly with no further machinery.
Examples (written in a Rust-style pseudocode) are as follows.
```
data Magma {
    T: Type,
    op: T -> T -> T,
}
```
We aim to give data types and functions the ability to have codified laws; that is, logical invariants the programmer must prove are upheld.
Such laws may be useful in other aspects of Quill, such as `map f (map g x) = map (f . g) x`.

Some data structures require more flexibility in the way they utilise the type system.
In particular, their members need not be variables with a specific concrete value.
They can, for example, be higher rank functions, such as
```
data Monad {
    M: Type -> Type,
    return: (A: Type) -> A -> M A,
    bind: (A: Type) -> (B: Type) -> M A -> (A -> M B) -> M B
}
```
Such data structures are tagged such that their non-runtime-compatible values are only computed at compile time.
Any fields whose values are statically known can be elided from the final build in the same way.
```
compose_three (T: Type, i: Magma[T], a: T, b: T, c: T): T = (
    i.op (i.op a b) c
)
```
The parameter `T` applied to argument `i` is implicitly assumed to refer to the first field in the data type.
Any data type may be constrained in this way.
Note that the value of `op` as a member of `i` is accessed through `i.op`.
This is an implicit destructuring of `i`.
Note further that `i.op` is used twice, something which is typically a violation of an ownership-based memory model.
However, there are two mitigating factors at play.

- The copy will in fact never be executed, it will be elided at compile time, presuming that the implementation of `Magma` is known statically.
- The function data type `* -> *` is copyable. This means that it can be copied transparently; no explicit `copy` keyword or the like is required.

More explicitly, we might write the body of the function as
```
let { T, op } = i in op (op a b) c
```
As another example of constraining data types, consider
```
data Array {
    T: Type,
    n: Int,
    value: if n == 0 then nil else T
    tail: if n == 0 then nil else Array[T, n - 1]
}

cons (T: Type, implicit n: Int, a: T, array: Array[T, n]): Array[T, n + 1] = (
    Array { T, n = n + 1, value = T, tail = array }
)

empty (T: Type): Array[T, 0] = (
    Array { T, n = 0, value = nil, tail = nil }
)

three_elements: Array[Int, 3] = cons 1 (cons 2 (cons 3 empty))
```
Notice that types have just as much semantic complexity as values.
This is consistent with the types-as-values approach taken by Quill and Feather.
Here, some parameters are marked `implicit`.
They are to be deduced from context.
They can be made explicit by using square brackets: `cons[_, 0] 1 empty`, for example.
Certain types are marked by Quill as implicit-by-default, such as `Type`.
Implicitness is not a concept in Feather.

# Documentation

With sufficient modularity and expression-orientatedness, we can have a program itself be automatically documented.
This documentation can be mathematical; generating LaTeX documentation code for a Quill project, where functions are written in math environments not code environments, is not an unreasonable target.
This is a step towards the `literate programming' paradigm.

Feather could also potentially have plugins for things like tactics, allowing "implicit" keywords and such. This is a step towards a full automated theorem proof assistant.

# TODO

Make the use of past/present tense and active/passive voice consistent within the compiler's messages.
Also, we could make the use of "parameter" and "argument" more consistent?
