# Mimir

> Mimir is a figure from Norse mythology renowned for his wisdom and knowledge. After being beheaded during the Aesir-Vanir war, Odin preserves his head and consults it for advice.

This project is a Rust implementation of Mini-Prolog, completed for a Computer Science dissertation at the University of Exeter. Project documentation is hosted [here](https://kit-matthewson.github.io/mimir).

This repository also includes, under the `report` directory, the project report written in [Typst](https://typst.app/).

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

### Justfile
This project also includes a `justfile` (similar to a Makefile). Just can be installed with Cargo:

```
cargo install just
```

Then, you can run the tasks defined in the `justfile`:
- `just run` - Runs the main program.
- `just check` - Runs all code checks including formatting and linting.
- `just make-pdfs` - Generate PDFs for the project report, logbook, and poster.

## Example
A program such as:
```
trapezoidal(X, A, _, _, _, Y) :-
    X < A,
    Y = 0.
trapezoidal(X, A, B, _, _, Y) :-
    X >= A,
    X <= B,
    Y = (X - A) / (B - A).
trapezoidal(X, _, B, C, _, Y) :-
    X > B,
    X < C,
    Y = 1.
trapezoidal(X, _, _, C, D, Y) :-
    X >= C,
    X <= D,
    Y = (D - X) / (D - C).
trapezoidal(X, _, _, _, D, Y) :-
    X > D,
    Y = 0.
warm(X) :~
    trapezoidal(X, 15, 20, 25, 30, Y),
    Y.
```
Would allow you to query `warm(18)` and receive a truth value of `0.60`, indicating that 18 degrees is somewhat warm according to the defined trapezoidal function.
