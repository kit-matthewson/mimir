#import "template.typ": *

#codly(display-icon: false, display-name: false)

#let todos = true

#set text(lang: "en")

#show: template.with(
  title: [A Rust Implementation of Mini-Prolog],
  author: "Kit Matthewson",
  date: datetime.today(),
  abstract: [],
  bibliography: bibliography("refs.bib"),
)

#let appendix(body) = heading(
  numbering: "1.A",
  supplement: "Appendix",
  level: 2,
)[#body]

#outline()

#pagebreak(weak: true)

#if todos [
  - #sym.ballot Gantt chart
  - #sym.ballot Project plan
]

= Introduction
== Motivation

#if todos [
  - #sym.ballot.check.heavy Use of Prolog in AI
  - #sym.ballot Personal interest in logic programming
  - #sym.ballot Rust as a modern systems language
  - #sym.ballot Examine the target user
]

The rise in LLMs has led to the acceptance of results from models consisting of billions to trillions of parameters. To attempt to interogate one of these models as to why it has produced a given output is practically impossible. It is not unlikely that such models will, or already are, being used in applications where safety and correctness are paramount @bommasani_opportunities_2022. In such situations, it is desireable to instead use systems which can provide formal guarantees and explanations for their outputs. These systems are referred to as explainable AI, or XAI @dwivedi_explainable_2023.

Prolog can be used to create an XAI system, normally in the form of an expert system (ES). An ES consists of a knowledge base and an inference engine which applies logical reasoning to the knowledge base to derive new facts or make decisions @griffin_fuzzy_2024. Enhancing Prolog with fuzzy logic capabilities might allow it to handle the uncertainty and imprecision inherent in many real-world applications @kosko_fuzzy_1993.

== Aims and Objectives
#if todos [
  - #sym.ballot.check.heavy Mini-Prolog interpreter in Rust
    - #sym.ballot.check.heavy Parse Mini-Prolog syntax
    - #sym.ballot.check.heavy Implement evaluation of Prolog queries
  - #sym.ballot Stretch: Fuzzy logic support
]

The aim of this project is to use Rust to implement a Mini-Prolog interpreter capable of parsing and evaluating Prolog queries. This will involve two parts: creating a parser to read Mini-Prolog syntax and convert it into an internal representation, and implementing an evaluation engine to answer Prolog queries based on this representation.

As a stretch goal, the interpreter will be extended to support fuzzy logic...

== Success Criteria
#if todos [
  - #sym.ballot User
  - #sym.ballot Execution of Prolog queries
  - #sym.ballot All fully justified
]

The parser will be considered succesful if it:
- Correctly reads valid Mini-Prolog syntax and converts it into an internal representation. The parser would be useless if it could not handle valid input.
- Provides meaningful error messages for invalid syntax. Producing helpful feedback to users is important for usability and debugging.

The evaluation engine will be considered succesful if it:
- Correctly evaluates Prolog queries based on the internal representation.
- Produces correct results for a set of predefined test cases. A set of test cases will be created to cover various Prolog constructs and scenarios. These will be used to ensure the evaluation engine produces the expected results.

= Background
== Prolog
#if todos [
  - #sym.ballot.check.heavy History
  - #sym.ballot Use in AI and NLP
  - #sym.ballot.check.heavy Syntax and semantics
  - #sym.ballot.check.heavy Unification algorithm
  - #sym.ballot Mini-Prolog subset
]

Prolog was first developed in the early 1970s by Alain Colmerauer and Philippe Roussel in the artificial intelligence group at Aix-Marseille II University, France. Its original intention was to process natural language in an attempt to create a ‘man-machine communication system in natural language’ @colmerauer_birth_1992.

Since then, Prolog has found applications in various domains, including mathematical logic, relational databases, symbolic equation solving, natural language processing, and artificial intelligence @clocksin_programming_2003.

Unlike most imperative programming languages, Prolog is a _declarative_ language, where a program describes _what_ should be accomplished, rather than _how_.

A Prolog program consists of a database of _clauses_, which can be facts or rules. Facts are unconditional statements about the world, while rules define relationships between facts using logical implications. For example, consider @lst:prolog[listing].

#figure(
  listing(header: [*Family Tree*], width: 75%)[
    ```pl
    parent(alice, bob).
    parent(bob, charlie).

    child(X, Y) :- parent(Y, X).

    ancestor(X, Y) :- parent(X, Y).
    ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
    ```
  ],
  caption: [A simple Prolog program defining family relationships.],
) <lst:prolog>

Here we:
- Define two facts: Alice is Bob's parent, and Bob is Charlie's parent.
- Define a rule stating that _X_ is a child of _Y_ if (and only if) _Y_ is a parent of _X_.
- Define a recursive rule stating the base case, that _X_ is an ancestor of _Y_ if _X_ is a parent of _Y_; and the recursive case, that _X_ is an ancestor of _Y_ if _X_ is a parent of some _Z_, and _Z_ is an ancestor of _Y_.
Because Prolog attempts clauses in the order they are defined, the base case will always be checked first.

This program can be queried to find relationships. For example, the query `ancestor(alice, charlie).` would return true, as Alice is an ancestor of Charlie through Bob. We can also ask Prolog to find all ancestors of Charlie with the query `ancestor(X, charlie).`, which would yield `X = bob; X = alice;` @clocksin_programming_2003.

Prolog uses a process called _unification_ to answer queries. Unification is an algorithm that attempts to make two terms identical by finding a substitution for variables. Two terms can be unified if @clocksin_programming_2003:
- They are identical atoms or numbers.
- One is a variable, which can be unified with any term.
- Both are compound terms with the same functor and arity, and their corresponding arguments can be unified recursively.
The 'execution' of a Prolog query works by attempting to unify the query with a stack of goals created from the program's clauses. This process is discussed further in @sec:unification[section].

=== Mini-Prolog
For this project, a subset of Prolog will be used that we will call _Mini-Prolog_ based on the design given by Dewey and Hardekopf @dewey_mini. Mini-Prolog simplifies the implementation of a Prolog engine in two ways: by removing features from Prolog, and introducing an internal syntax.

The features removed are:
+ The backtracking control operators _cut_, `!`, and _not_.
+ Clause management predicates, such as `assert/1` and `retract/1`.
+ Meta-programming operators, such as `forall/2`, `bagof/3`, and `findall/3`.
+ Built-in predicates, such as `append/3` and `member/2`. These can still be implemented by the user.
Most Prolog programs do not rely on these features, and those that do not can be executed by a Mini-Prolog engine.

The user-facing syntax can be translated into a simpler internal syntax for execution. The internal syntax:
+ Replaces lists and list operations with `./1` structures. For example the user-facing syntax `[1, 2, 3]` becomes `.(1, .(2, .(3, nil)))`.
+ Hoists the declaration of all variables to a list of local variables at the head the clause.
+ Translates pattern-matching to unification.
+ Translates unification between arbritrary values to a series of variable bindings and unifications on variables. This simplifies unification by only allowing it between variables.
See @lst:syntax_comparison for an example of translated clauses.

#figure(
  grid(
    columns: (40%, 50%),
    listing(header: [*User-Facing Syntax*])[
      // #codly(highlights: (
      //   (line: 1, end: 14, fill: red.lighten(50%)),
      //   (line: 3, end: 24, fill: blue.lighten(50%)),
      // ))
      ```pl
      allLess(_, []).

      allLess(V1, [V2 | Rest]) :-
          V2 < V1,
          allLess(V1, Rest).
      ```
    ],
    listing(header: [*Internal Syntax*])[
      // #codly(highlights: (
      //   (line: 1, end: 15, fill: red.lighten(50%)),
      //   (line: 5, end: 15, fill: blue.lighten(50%)),
      // ))
      ```pl
      allLess(T1, T2) {T3} :-
        T3 ← nil(),
        T2 ≡ T3.

      allLess(V1, T1) {V2, Rest, T2} :-
        T2 ← cons(V2, Rest),
        T1 ≡ T2,
        V2 < V1,
        allLess(V1, Rest).
      ```
    ],
  ),
  caption: [Comparison betwen user-facing and internal syntax for an `allLess/2` predicate, from Dewey and Hardekopf @dewey_mini.],
) <lst:syntax_comparison>

== Rust
#if todos [
  - #sym.ballot.check.heavy History and uses
  - #sym.ballot.check.heavy Key features
    - #sym.ballot.check.heavy Compare to C/C++
  - #sym.ballot Why Rust for this project?
    - #sym.ballot.check.heavy Performance
    - #sym.ballot.check.heavy Safety
    - #sym.ballot.check.heavy Modern tooling
]

Rust is a modern systems programming language first released in 2010 by Mozilla. The main focus of Rust is memory safety whilst maintaining high performance, making it a popular choice for tasks traditionally handled by C or C++ @bugden_rust_2022. As a major example, Rust has been adopted as one of the languages accepted into the Linux kernel @nichols_rust_2024.

Anyone who has written C or C++ will be familiar with issues such as buffer overflows, memory leaks, and use-after-free errors. Rust uses an ownership model, where there is always exactly one owner of memory at any given time, to prevent these issues. When sharing data#footnote[For instance by passing arguments to a function.], the user can choose to transfer ownership (moving), create an immutable reference (borrowing), or clone the data. The memory is automatically freed when its owner goes out of scope, preventing the need to manually manage memory @bugden_rust_2022. It should be noted that these restrictions can be escaped using `unsafe` blocks, allowing the user to manually manage memory if absolutely necessary, whilst making these regions of code explicit and easily identifiable @rust-lang.

As well as safety, Rust has modern features such as options and pattern matching, a powerful macro system, and a rich type system with generics and traits. It manages to provide these features whilst still being a compiled language with performance comparable to C and C++ @bugden_rust_2022.

Rust also has excellent tooling, with `cargo` as its built-in package manager and build system. It provides utilities such as:
- `cargo run` to resolve dependencies, compile, and run the program.
- `cargo test` to run unit tests.
- `cargo clippy` to provide linting and code quality suggestions.
- `cargo fmt` to automatically format code according to style guidelines.
These tools help streamline development and maintain code quality @rust-lang. Their simplicity also makes continuous integration (CI) straightforward to set up.

The language also has good documentation features, with `rustdoc` able to generate HTML documentation from documentation comments in the source code. If these comments contain example code, `cargo test` will include them in the test suite to ensure they remain correct @rust-lang.

== Fuzzy Logic (Stretch)
#if todos [
  - #sym.ballot Overview: @zadeh_fuzzy_1988 @kosko_fuzzy_1993 @zadeh_need_2008
  - #sym.ballot How it would integrate with Prolog
  - #sym.ballot Extra use it would provide
]

= Design
== High-Level Architecture
#if todos [
  - #sym.ballot `nom` parser
  - #sym.ballot AST representation
  - #sym.ballot Engine structure as defined by Dewey @dewey_mini
  - #sym.ballot User requirements
]

The design consists of three parts:
+ A parser which takes Mini-Prolog syntax as input and returns an abstract syntax tree (AST) representing it.
+ A translator that translates the Mini-Prolog AST into an internal syntax AST.
+ An engine that executes the program using the internal syntax AST.

== Rationale
#if todos [
  - #sym.ballot Justify all design and development choices
]

= Implementation
== Development
#if todos [
  - #sym.ballot Git and GitHub for version control and project management
  - #sym.ballot Continuous integration with GitHub Actions
  - #sym.ballot Rust toolchain:
    - #sym.ballot `cargo` for testing, run on CI
    - #sym.ballot `clippy` and `rustfmt` for code quality as commit hooks
    - #sym.ballot Documentation generation with `rustdoc`, hosted on GitHub Pages
]

== Parser
#if todos [
  - #sym.ballot Using `nom` library
  - #sym.ballot Grammar taken from Mini-Prolog definition
  - #sym.ballot Error handling
]

== Abstract Syntax Tree
#if todos [
  - #sym.ballot Representation of Prolog constructs
  - #sym.ballot Design choices, difference between `enum`s and `struct`s
]

== The Unification Algorithm <sec:unification>
#if todos [
  - #sym.ballot Implementation details
  - #sym.ballot Comments on Dewey's version
]

== Handling Fuzzy Logic (Stretch)

= Results
== Correctness
#if todos [
  - #sym.ballot Test cases
  - #sym.ballot Running examples
]

== Performance
#if todos [
  - #sym.ballot Benchmark against other implementations
  - #sym.ballot NREV: https://www.cs.cmu.edu/afs/cs.cmu.edu/project/ai-repository/ai/lang/prolog/code/bench/0.html
]

== Evaluation
#if todos [
  - #sym.ballot Comparison with other Prolog implementations
  - #sym.ballot User feedback?
]

= Conclusion
== Reflection
== Future Work
== Summary

= Appendix
#appendix[Prolog features removed from Mini-Prolog]
The _cut_ operator allows the programmer to instruct the Prolog engine not to attempt further backtracking. This can be used to make programs more efficient, for instance if two clauses are mutually exclusive then we can cut if the first succeeds because we now know the second will fail.
