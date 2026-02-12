#import "template.typ": *
#import "@preview/timeliney:0.4.0"

#codly(display-icon: false, display-name: false)

#let todos = true
#let hide-done-todos = false

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

#let todo(done: false, body) = if todos and (not hide-done-todos or not done) [ #list.item(
  if done [#sym.ballot.check.heavy #body] else [#sym.ballot #body],
) ]

#outline()

#pagebreak(weak: true)

#todo(done: true)[Gantt chart]

= Introduction
== Motivation
#todo(done: true)[Use of Prolog in AI]
#todo[Personal interest in logic programming]
#todo[Rust as a modern systems language]
#todo[Examine the target user]

The rise in LLMs has led to the acceptance of results from models consisting of billions to trillions of parameters. To attempt to interogate one of these models as to why it has produced a given output is practically impossible. It is not unlikely that such models will, or already are, being used in applications where safety and correctness are paramount @bommasani_opportunities_2022. In such situations, it is desireable to instead use systems which can provide formal guarantees and explanations for their outputs. These systems are referred to as explainable AI, or XAI @dwivedi_explainable_2023.

Prolog can be used to create an XAI system, normally in the form of an expert system (ES). An ES consists of a knowledge base and an inference engine which applies logical reasoning to the knowledge base to derive new facts or make decisions @griffin_fuzzy_2024. Enhancing Prolog with fuzzy logic capabilities might allow it to handle the uncertainty and imprecision inherent in many real-world applications @kosko_fuzzy_1993.

== Aims and Objectives
#todo(done: true)[Mini-Prolog interpreter in Rust]
#todo(done: true)[Parse Mini-Prolog syntax]
#todo(done: true)[Implement evaluation of Prolog queries]
#todo[Stretch: Fuzzy logic support]

The aim of this project is to use Rust to implement a Mini-Prolog interpreter capable of parsing and evaluating Prolog queries. This will involve two parts: creating a parser to read Mini-Prolog syntax and convert it into an internal representation, and implementing an evaluation engine to answer Prolog queries based on this representation.

As a stretch goal, the interpreter will be extended to support fuzzy logic...

== Prolog
#todo(done: true)[History]
#todo[Use in AI and NLP]
#todo(done: true)[Syntax and semantics]
#todo(done: true)[Unification algorithm]
#todo(done: true)[Mini-Prolog subset]

Prolog was first developed in the early 1970s by Alain Colmerauer and Philippe Roussel in the artificial intelligence group at Aix-Marseille II University, France. Its original intention was to process natural language in an attempt to create a ‘man-machine communication system in natural language’ @colmerauer_birth_1992.

Since then, Prolog has found applications in various domains, including mathematical logic, relational databases, symbolic equation solving, natural language processing, and artificial intelligence @clocksin_programming_2003.

Unlike most imperative programming languages, Prolog is a _declarative_ language, where a program describes _what_ should be accomplished, rather than _how_.

A Prolog program consists of a database of _clauses_, which can be facts or rules. Facts are unconditional statements about the world, while rules define relationships between facts using logical implications. For example, consider @lst:prolog[listing].

#figure(
  placement: auto,
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
  placement: auto,
  grid(
    columns: (45%, 45%),
    column-gutter: 10pt,
    listing(header: [*User-Facing Syntax*])[
      ```pl
      allLess(_, []).

      allLess(V1, [V2 | Rest]) :-
          V2 < V1,
          allLess(V1, Rest).
      ```
    ],
    listing(header: [*Internal Syntax*])[
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
  caption: [Comparison between user-facing and internal syntax for an `allLess/2` predicate, from Dewey and Hardekopf @dewey_mini.],
) <lst:syntax_comparison>

== Rust
#todo(done: true)[History and uses]
#todo(done: true)[Key features]
#todo(done: true)[Compare to C/C++]
#todo[Why Rust for this project?]
#todo(done: true)[Performance]
#todo(done: true)[Safety]
#todo(done: true)[Modern tooling]

Rust is a modern systems programming language first released in 2010 by Mozilla. The main focus of Rust is memory safety whilst maintaining high performance, making it a popular choice for tasks traditionally handled by C or C++ @bugden_rust_2022. As a major example, Rust has been adopted as one of the languages accepted into the Linux kernel @nichols_rust_2024.

Anyone who has written C or C++ will be familiar with issues such as buffer overflows, memory leaks, and use-after-free errors. Rust uses an ownership model, where there is always exactly one owner of memory at any given time, to prevent these issues. When sharing data#footnote[For instance, by passing arguments to a function.], the user can choose to transfer ownership (moving), create an immutable reference (borrowing), or clone the data. The memory is automatically freed when its owner goes out of scope, preventing the need to manually manage memory @bugden_rust_2022. It should be noted that these restrictions can be escaped using `unsafe` blocks, allowing the user to manually manage memory if absolutely necessary, whilst making these regions of code explicit and easily identifiable @rust-lang.

As well as safety, Rust has modern features such as options and pattern matching, a powerful macro system, and a rich type system with generics and traits. It manages to provide these features whilst still being a compiled language with performance comparable to C and C++ @bugden_rust_2022.

Rust also has excellent tooling, with `cargo` as its built-in package manager and build system. It provides utilities such as:
- `cargo run` to resolve dependencies, compile, and run the program.
- `cargo test` to run unit tests.
- `cargo clippy` to provide linting and code quality suggestions.
- `cargo fmt` to automatically format code according to style guidelines.
These tools help streamline development and maintain code quality @rust-lang. Their simplicity also makes continuous integration (CI) straightforward to set up.

The language also has good documentation features, with `rustdoc` able to generate HTML documentation from documentation comments in the source code. If these comments contain example code, `cargo test` will include them in the test suite to ensure they remain correct @rust-lang.

== Fuzzy Logic (Stretch)
#todo[Overview: @zadeh_fuzzy_1988 @kosko_fuzzy_1993 @zadeh_need_2008]
#todo[How it would integrate with Prolog]
#todo[Extra use it would provide]

= Project Specification
== Success Criteria <sec:success_criteria>
#todo(done: true)[User]
#todo(done: true)[Execution of Prolog queries]
#todo(done: true)[All fully justified]

The intended user of this project is a programmer interested in logic programming and Prolog, who wants to both use and understand a Prolog engine. This user would be interested in the implementation details of the engine, and would therefore expect it to be well-documented and easy to read. This is in addition to the engine being useful for executing Prolog queries.

The design would be considered to meet the user requirements if it:
- Is implemented in modern Rust.
- Has clear documentation, including explanatory comments in the code and generated documentation of the API.
- Is structured in a way that is easy to understand, with clear separation between the parser, translator, and engine.

The parser will be considered succesful if it:
- Correctly reads valid Mini-Prolog syntax and converts it into an internal representation. The parser would be useless if it could not handle valid input.
- Provides meaningful error messages for invalid syntax. Producing helpful feedback to users is important for usability and debugging.

The evaluation engine will be considered succesful if it:
- Correctly evaluates Prolog queries based on the internal representation.
- Produces correct results for a set of predefined test cases. A set of test cases will be created to cover various Prolog constructs and scenarios. These will be used to ensure the evaluation engine produces the expected results.

= Design
== High-Level Architecture
#todo(done: true)[`nom` parser]
#todo(done: true)[AST representation]
#todo(done: true)[Engine structure as defined by Dewey @dewey_mini]

The design consists of three parts: a parser to generate an AST from user-facing syntax, a translator to convert the user-facing AST to an internal syntax AST, and an engine to execute the program using the internal syntax AST. Each of these parts will be implemented as separate Rust modules, with clear interfaces between them.

The parser will be written using _nom_, a popular parser combinator library in Rust @nom_github. This will be used to generate an AST representing the user-facing syntax. Ivan Bratko's _Prolog_ @bratko_prolog_1990 will be used as reference for Prolog's syntax.

The user-facing AST will then be translated into an AST representing Dewey and Hardekopf's internal syntax @dewey_mini. This allows the engine to be simplified.

The engine will be structured as defined by Dewey and Hardekopf @dewey_mini, which has a focus on simplicity over performance. It uses a goal stack to keep track of the current goals being evaluated, and an environment to keep track of variable bindings. The engine will implement the unification algorithm to evaluate queries.

== Rationale
#todo(done: true)[Justify all design and development choices]
#todo(done: true)[User requirements]

This design is chosen to meet the user requirements identified in @sec:success_criteria. The use of Rust ensures the implementation is in a modern language with good performance and safety guarantees. The use of _nom_ allows for a clear and maintainable parser, while the use of a translator to an internal syntax provides clear separation of concerns and simplifies the engine implementation.

The engine structure defined by Dewey and Hardekopf is chosen for its simplicity, which is appropriate for this project given the focus on understanding and correctness over performance.

= Development
== Development Environment
#todo(done: true)[Git and GitHub for version control and project management]
#todo(done: true)[Continuous integration with GitHub Actions]
#todo(done: true)[`cargo` for testing, run on CI]
#todo(done: true)[`clippy` and `rustfmt` for code quality as commit hooks]
#todo(done: true)[Documentation generation with `rustdoc`, hosted on GitHub Pages]

For version control I will use Git, with the repository hosted on GitHub. Using GitHub makes setting up continuous integration (CI) with GitHub Actions straightforward, allowing tests and code quality checks to be automatically run on each commit.

The Rust toolchain will be used for testing, code quality, and documentation. Unit tests can be written using Rust's built-in testing framework, and run with `cargo test`. Code quality can be maintained using `cargo clippy` for linting and `cargo fmt` for formatting, which can be set up as commit hooks to ensure they are run before each commit.

Documentation will be generated using `rustdoc`, which can create HTML documentation from comments in the source code. This documentation can be hosted on GitHub Pages for easy access.

== Parser
#todo(done: true)[Using `nom` library]
#todo(done: true)[Grammar taken from Mini-Prolog definition]
#todo(done: true)[Error handling]

Using the _nom_ library, the parser will be implemented as a series of combinators that match the grammar of Mini-Prolog. The grammar will be based on the standard Prolog syntax as given in Bratko's _Prolog_ @bratko_prolog_1990, with adjustments to fit the Mini-Prolog subset defined by Dewey and Hardekopf @dewey_mini.

Parsing functions will be implemented as Rust traits on the AST types. This ties the parsing logic closely to the data structures representing the syntax. A `Parseable` trait will be defined, which requires a `parse` function that takes an input string and returns a result containing the parsed AST node or an error. This allows for a consistent interface for parsing different types of AST nodes:
```rs
pub trait Parseable: std::fmt::Display + Sized {
    fn parse(input: &str) -> nom::IResult<&str, Self>;
}
```
_nom_ parsers return an `IResult` type, which can represent either a successful parse with the remaining input and the parsed value, or an error. This allows for robust error handling, as the parser can provide meaningful error messages when it encounters invalid syntax.

Each parsing function will be thoroughly tested with a variety of valid and invalid input to ensure it behaves as expected and provides helpful feedback to users. They will also be documented with example usage, which are also tested with `cargo test` to ensure they remain correct.

=== Abstract Syntax Tree
#todo(done: true)[Representation of Prolog constructs]
#todo[Design choices, difference between `enum`s and `struct`s]

The Abstract Syntax Tree (AST) represents the structure of the Prolog program in a way that is easier to work with. Rust provides two main ways to represent data structures: enums and structs.

Enums are used for data that can take on one of several different forms. For example, a Prolog term can be an atom, a variable, or a compound term. Structs are used for data that has a fixed structure. For example, a clause always consists of a head and a body. Rust makes handling these different types of data straightforward, and the choice between enums and structs is guided by the nature of the data being represented. See @tab:ast_overview for an overview of the main AST node types used in the implementation.

#figure(
  placement: auto,
  table(
    align: left,
    columns: 3,
    [*Node*], [*Type*], [*Description*],
    [Clause], [Struct], [A clause with head and optional body],

    [Goal],
    [Enum],
    [A goal which makes up the body of a clause. Can be a _relation_ between terms, a _unification_ between terms, or _check_ of a compound term.],

    [Term], [Enum], [A term can be an _atom_, a _variable_, or a _compound_ term with a functor and arguments.],

    [Atom], [Struct], [An atom is a constant symbol.],

    [Variable], [Struct], [A variable is a placeholder that can be unified with any term.],

    [Compound], [Struct], [A compound term consists of a functor and a list of arguments, which are themselves terms.],

    [Expression], [Enum], [An expression is either a compound or an arithmetic expression.],
  ),
  caption: [An overview of the main AST node types used in the implementation.],
) <tab:ast_overview>

== Engine
=== The Unification Algorithm <sec:unification>
#todo[Implementation details]
#todo[Comments on Dewey's version]

== Handling Fuzzy Logic (Stretch)

= Testing
== Correctness
#todo[Test cases]
#todo[Running examples]

== Performance
#todo[Benchmark against other implementations]
#todo[NREV: https://www.cs.cmu.edu/afs/cs.cmu.edu/project/ai-repository/ai/lang/prolog/code/bench/0.html]

= Description of the Final Product

= Evaluation of the Final Product
#todo[Comparison with other Prolog implementations]
#todo[User feedback?]

= Critical Assessment of the Project as a Whole

= Conclusion
== Reflection
== Future Work
== Summary

= Appendix
#appendix[Prolog features removed from Mini-Prolog]
The _cut_ operator allows the programmer to instruct the Prolog engine not to attempt further backtracking. This can be used to make programs more efficient, for instance if two clauses are mutually exclusive then we can cut if the first succeeds because we now know the second will fail.

#appendix[Project Gantt Chart] <appendix:gantt>
Project Gantt Chart. Columns are weeks.

#timeliney.timeline(
  show-grid: true,
  {
    import timeliney: *

    headerline(
      group(([*Christmas*], 4)),
      group(([*T2*], 11)),
      group(([*Easter*], 4)),
      group(([*T3*], 3)),
    )

    headerline(
      group(..range(4).map(n => str(n + 1))),
      group(..range(11).map(n => str(n + 1))),
      group(..range(4).map(n => str(n + 1))),
      group(..range(3).map(n => str(n + 1))),
    )

    taskgroup(
      title: [*Report*],
      {
        task(
          "Research",
          (from: 0, to: 12),
        )

        task(
          "Report Writing",
          (from: 7, to: 19),
        )

        task(
          "Testing and Evaluation",
          (from: 11, to: 18),
        )

        task(
          "Poster Creation",
          (from: 12, to: 14.7),
        )
      },
    )

    taskgroup(
      title: [*Project*],
      {
        task(
          "CI Setup",
          (from: 0, to: 1),
        )

        task(
          "AST Definitions",
          (from: 0, to: 1.5),
        )
        task(
          "Parsing Functions",
          (from: 0.5, to: 3),
        )
        task(
          "Parser Integration Tests",
          (from: 2.5, to: 3.5),
        )

        task(
          "Engine Outline",
          (from: 3, to: 4),
        )

        task(
          "Internal Representation",
          (from: 3.5, to: 5),
        )

        task(
          "Engine Structure",
          (from: 4.5, to: 5.5),
        )

        task(
          "Unification Algorithm",
          (from: 5.5, to: 6),
        )

        task(
          "Engine Integration Tests",
          (from: 6, to: 7),
        )

        task(
          "Translator",
          (from: 7, to: 9),
        )

        task(
          "Translator Integration Tests",
          (from: 8.5, to: 9.5),
        )
      },
    )

    taskgroup(
      title: [*Stretch*],
      {
        task(
          "Fuzzy Logic Research",
          (from: 5, to: 8),
        )

        task(
          "Fuzzy Logic Design",
          (from: 12, to: 13),
        )

        task(
          "Fuzzy Logic Implementation",
          (from: 13, to: 15),
        )
      },
    )
    milestone(
      at: 14.7, // T2 W11
      style: (stroke: (dash: "dashed")),
      align(center, [
        *Poster \ Submission*
      ]),
    )

    milestone(
      at: 19.7, // T3 W1
      style: (stroke: (dash: "dashed")),
      align(center, [
        *Project \ Submission*
      ]),
    )
  },
)
