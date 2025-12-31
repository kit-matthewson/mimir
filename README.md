# Mimir

> Mimir is a figure from Norse mythology renowned for his wisdom and knowledge. After being beheaded during the Aesir-Vanir war, Odin preserves his head and consults it for advice.

This project is a Rust implementation of Mini-Prolog, completed for a Computer Science dissertation at the University of Exeter. Project documentation is hosted [here](https://kit-matthewson.github.io/mimir).

## Scope
Mimir implements Mini-Prolog, a simplified version of Prolog from [Kyle Dewey and Ben Hardekopf](https://kyledewey.github.io/cs162w15/handouts/handout7-miniprolog.pdf).

It simplifies Prolog by:
- Omitting features including cut and database modification operators (assert/retract).
- Removing any built-in predicates.
- Using a simplified internal representation of Prolog for execution.

Mimir executes Mini-Prolog programs by:
1. Parsing Prolog source code into an Abstract Syntax Tree (AST).
2. Converting the AST into an internal representation suitable for execution.
3. Executing queries against the internal representation using a backtracking algorithm.

## Building and Running
To use Mimir, ensure you have Rust installed. Then, clone the repository and use Cargo to build and run the project:

```
cargo run
```

### Testing
Mimir includes a thorough test suite of unit and integration tests, as well as [documentation tests](https://doc.rust-lang.org/rustdoc/write-documentation/documentation-tests.html) to verify examples in the documentation.

To run the complete test suite, use:

```
cargo test
```
