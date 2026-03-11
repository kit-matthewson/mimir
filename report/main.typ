#import "template.typ": *
#import "@preview/timeliney:0.4.0"

// #codly(display-icon: false, display-name: false)

#let todos = false
#let hide-done-todos = true

#set text(lang: "en")

#show: template.with(
  title: [A Rust Implementation of Mini-Prolog with Fuzzy Logic Support],
  author: "Kit Matthewson",
  student-id: "730002704",
  date: datetime.today(),
  abstract: [
    This dissertation explores the design and implementation of a Mini-Prolog interpreter in Rust. The project is motivated by the rise of large language models (LLMs) and the need for explainable AI (XAI) systems that can provide formal guarantees and explanations for their outputs. Based on Dewey and Hardekopf's specification for Mini-Prolog, the interpreter implements a core subset of Prolog, omitting features like cut and meta-programming to simplify implementation.

    Rust was chosen for its modern features, performance, and safety guarantees. The architecture comprises a parser, a translator to an internal syntax, and an execution engine. The parser is implemented using the _nom_ combinator library, while the engine follows a stack-based execution model.
  ],
  table-of-contents: outline(),
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

#pagebreak(weak: true)

#todo(done: true)[Remove abbreviations]
#todo(done: true)[Gantt chart]

= Introduction
== Context
#todo(done: true)[Use of Prolog in AI]
#todo(done: true)[Personal interest in logic programming]
#todo(done: true)[Rust as a modern systems language]
#todo(done: true)[Examine the target user]

Prolog is a simple but powerful programming language developed at the University of Marseille in the early 1970s. Its ease of use makes it a popular choice for both teaching and using logic programming @bratko_prolog_1990. With roots in formal logic, Prolog is particularly well-suited for applications in theorem proving @stickel_prolog_1992, expert systems @merritt_building_2012, and natural language processing @shieber_prolog_2005.

One of the motivations for this project is the rise of large language models (LLMs) and the need for explainable AI (XAI) systems. LLMs have impressive capabilities but their complexity and lack of transparency make them unsuitable for applications where safety and correctness are paramount @bommasani_opportunities_2022 @wang_decodingtrust_2024. In contrast, Prolog's logical foundations and declarative nature make it a good candidate for building explainable AI systems, particularly in the form of expert systems @dwivedi_explainable_2023.

Expert Systems consist of a knowledge base and an inference engine which applies logical reasoning to the knowledge base to derive new facts or make decisions @griffin_fuzzy_2024 @clark_prolog_1980. Enhancing Prolog with fuzzy logic capabilities would allow it to handle the uncertainty and imprecision inherent in many real-world applications @kosko_fuzzy_1993.

The creation of a Prolog engine from scratch is also a valuable learning experience. It allows for a deep understanding of the methods underlying Prolog, such as unification and backtracking, which in turn prove useful for writing efficient Prolog.

Rust is a modern systems programming language that provides memory safety and high performance. It has been adopted in various domains, including systems programming @bugden_rust_2022. Its safety guarantees, performance, and modern features make it well-suited for this project.

There are multiple target use cases for this project. The first is as a learning tool for myself and others interested in logic programming and Prolog. By implementing a Prolog engine from scratch, I can gain a deeper understanding of how Prolog works and the underlying algorithms involved. The second use case is as a tool for executing Prolog queries. This could be done by writing Prolog programs and executing them with the engine, or by using the engine as a library in other Rust programs. The design and implementation of the project will be guided by these use cases.

== Aims and Objectives
#todo(done: true)[Mini-Prolog interpreter in Rust]
#todo(done: true)[Parse Mini-Prolog syntax]
#todo(done: true)[Implement evaluation of Prolog queries]
#todo(done: true)[Stretch: Fuzzy logic support]

The aim of this project is to use Rust to implement a Mini-Prolog interpreter capable of parsing and evaluating Prolog queries. This will involve two parts: creating a parser to read Mini-Prolog syntax and convert it into an internal representation, and implementing an evaluation engine to answer Prolog queries based on this representation.

Fuzzy logic support is a stretch goal for this project. If implemented, it would allow the engine to evaluate predicates with a degree of truth rather than boolean true or false. This would expand the capabilities of the engine to include the uncertainty and imprecision common in real-world applications.

== Prolog
#todo(done: true)[History]
#todo(done: true)[Syntax and semantics]
#todo(done: true)[Unification algorithm]
#todo(done: true)[Mini-Prolog subset]

Prolog was first developed in the early 1970s by Alain Colmerauer and Philippe Roussel in the artificial intelligence group at Aix-Marseille II University, France. Its original intention was to process natural language in an attempt to create a ‘man-machine communication system in natural language’ @colmerauer_birth_1992.

Since then, Prolog has found applications in various domains, including theorem proving @stickel_prolog_1992, relational databases, symbolic equation solving, natural language processing, and artificial intelligence @clocksin_programming_2003 @merritt_building_2012.

As a _declarative_ language, the Prolog programmer describes _what_ should be accomplished rather than _how_. The execution of a Prolog query works by attempting to unify the query with a stack of goals created from the program's clauses @bratko_prolog_1990.

// Unlike most imperative programming languages, Prolog is a _declarative_ language, where a program describes _what_ should be accomplished, rather than _how_.

// A Prolog program consists of a database of _clauses_, which can be facts or rules. Facts are unconditional statements about the world, while rules define relationships between facts using logical implications. For example, consider:

// ```pl
// parent(alice, bob).
// parent(bob, charlie).

// child(X, Y) :- parent(Y, X).

// ancestor(X, Y) :- parent(X, Y).
// ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
// ```

// This program can be read as a set of logical statements about the world. The facts state that Alice is Bob's parent and Bob is Charlie's parent. Then a rule is defined that states that if _Y_ is a parent of _X_, then _X_ is a child of _Y_. Defining an ancestor is more complex, as it is a recursive relationship. The base case states that if _X_ is a parent of _Y_, then _X_ is an ancestor of _Y_. The recursive case states that if _X_ is a parent of some _Z_, and _Z_ is an ancestor of _Y_, then _X_ is also an ancestor of _Y_.

// This program can be queried to find relationships. For example, the query `ancestor(alice, charlie).` would return true, as Alice is an ancestor of Charlie through Bob. We can also ask Prolog to find all ancestors of Charlie with the query `ancestor(X, charlie).`, which would yield `X = bob; X = alice;` @clocksin_programming_2003.

// Prolog uses a process called _unification_ to answer queries. Unification is an algorithm that attempts to make two terms identical by finding a substitution for variables.

// There are three ways that terms can be unified. If they are identical atoms or numbers, then they are already unified. If only one is a variable, then they can be unified by assigning the variable to the other term. If both are compound terms with the same functor and arity, then they can be unified if each of their corresponding arguments can themselves be unified. If none of these cases apply, then the terms cannot be unified and unification fails @clocksin_programming_2003.

=== Mini-Prolog
For this project, a subset of Prolog will be used that we will call _Mini-Prolog_. This is based on the design given by Dewey and Hardekopf @dewey_mini. Mini-Prolog simplifies the implementation of a Prolog engine in two ways: by removing features from Prolog, and introducing an internal syntax.

The removed features are cut, clause management predicates, meta-programming operators, and built-in predicates.

The _cut_ operator allows the programmer to control backtracking by instructing the Prolog engine not to attempt any further alternatives. This removes _negation as faliure_ by extension, as it is implemented using cut. There are only a few cases where cut is necessary for the execution of a program, it is most often used to improve the efficiency of a program.

Clause management predicates allow the programmer to modify the program at runtime by adding or retracting clauses. This is a powerful feature used in some programs but is not necessary for the execution of most Prolog programs. Note also that if the implementation is being used as a library, the user could implement this functionality themselves.

Full Prolog implementations often include built-in _meta-programming_ operators, which allow the programmer to reason about the program itself. For example, `bagof/3` allows the programmer to generate a list of all solutions to a query. As with clause management predicates, this feature could be implemented externally by users of the engine as a libary and is not used in most programs.

As well as these features, other implementations may also include built-in predicates, equivalent to the standard library of other languages. These can be implemented by the user as required.

Dewey and Hardekopf's internal syntax can be produced from the user-facing syntax by a translation step implemented in the engine.

The internal syntax replaces lists with `./1` structures. For example, the user-facing syntax `[1, 2, 3]` becomes `.(1, .(2, .(3, nil)))`. This means that the engine does not need to implement any special handling for lists, as they are just a specific case of compound terms.

Pattern matching can always be replaced with some number of unification operations. Matching for an empty list, for example, can be replaced with a unification with `nil`.

The head of a clause is changed so that it only contains variables. This can be achieved by inserting a number of unification steps at the beginning of the body of the clause to unify new variables in the head with the original terms in the head. In addition to this, a list of local variables is added alongside the head of the clause, which contains all the variables used in the clause. This has no effect on the execution of the program (as all Prolog variables are clause-local anyway), but simplifies the implementation of the engine by making it clear which variables are in scope at any given point.

Unification between arbitrary values can be replaced with variable bindings and unification on these variables. A variable _binding_ ($arrow.l$) differs from unification ($equiv$) in that it creates an equivalence between the variable and the value, but does not attempt to unify them. By using this translation, the engine only needs to implement unification between variables.

The user-facing syntax:
```pl
allLess(_, []).
allLess(V1, [V2 | Rest]) :-
    V2 < V1,
    allLess(V1, Rest).
```
Would be translated to:
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

== Rust
#todo(done: true)[History and uses]
#todo(done: true)[Key features]
#todo(done: true)[Compare to C/C++]
#todo(done: true)[Performance]
#todo(done: true)[Safety]
#todo(done: true)[Modern tooling]

Rust is a modern systems programming language first released in 2010 by Mozilla. The main focus of Rust is memory safety whilst maintaining high performance, making it a popular choice for tasks traditionally handled by C or C++ @bugden_rust_2022. As a major example, Rust has been adopted as one of the languages accepted into the Linux kernel @nichols_rust_2024.

Anyone who has written C or C++ will be familiar with issues such as buffer overflows, memory leaks, and use-after-free errors. Rust uses an ownership model, where there is always exactly one owner of memory at any given time, to prevent these issues. When sharing data, the user can choose to transfer ownership (moving), create an immutable reference (borrowing), or clone the data. The memory is automatically freed when its owner goes out of scope, preventing the need to manually manage memory @bugden_rust_2022. It should be noted that these restrictions can be escaped using `unsafe` blocks, allowing the user to manually manage memory if absolutely necessary, whilst making these regions of code explicit and easily identifiable @rust-lang.

As well as safety, Rust has modern features such as options and pattern matching, a powerful macro system, and a rich type system with generics and traits. It manages to provide these features whilst still being a compiled language with performance comparable to C and C++ @bugden_rust_2022.

Rust also has excellent tooling, with `cargo` as its built-in package manager and build system. It provides commands for managing dependencies, building and running the program, running tests, and maintaining code quality with linting and formatting.

These tools help streamline development and maintain code quality @rust-lang. Their simplicity also makes continuous integration (CI) straightforward to set up.

The language also has good documentation features, with `rustdoc` able to generate HTML documentation from documentation comments in the source code. If these comments contain example code, `cargo test` will include them in the test suite to ensure they remain correct @rust-lang.

== Fuzzy Logic
#todo(done: true)[Overview]
#todo[How it would integrate with Prolog]
#todo[Extra use it would provide]

As a stretch goal, the Prolog engine will be extended to support fuzzy logic. Fuzzy Logic was introduced in 1965 by Lotfi Zadeh as a way to deal with the uncertainty and imprecision inherent in many real-world applications @zadeh_fuzzy_1965.

In a standard boolean logic system, propositions are either true or false. This can be expanded to a multi-valued logic system, where propositions take on values from a finite set $T$. In fuzzy logic, this is expanded further to allow truth values taken from the continuous interval $[0, 1]$, where 0 is the boolean false, 1 is the boolean true, and values in between represent varying degrees of truth @zadeh_fuzzy_1988.

Using fuzzy logic allows for predicates to be evaluated with a degree of truth, rather than just true or false. For example the predicates 'tall', 'ill', or 'tired' are best evaluated as fuzzy predicates instead of boolean predicates @zadeh_fuzzy_1988.

Boolean logic allows for only two quantifiers: 'for all' and 'there exists'. In contrast fuzzy logic allows for any number of such quantifers, such as 'most', 'several', or 'about ten' @zadeh_fuzzy_1988.

The boolean operators _conjunction_, _disjunction_, and _negation_ need to be replaced with fuzzy equivalents. A common way this is done is to use minimum for conjuction, maximum for disjunction, and $1 - p$ for negation, called the _Zadeh operators_ @zadeh_fuzzy_1965. Consider how with $italic("true") = 1$ and $italic("false") = 0$ these operators behave identically to their boolean counterparts.

Membership functions evaluate the degree of truth of a predicate for a given input. For example, a trapezoidal membership function for the predicate 'warm' could define temperature values below 15 degrees as 0, between 20 and 25 degrees as 1, above 30 degrees as 0, and values in between as a linear interpolation between these points @zadeh_fuzzy_1988.

Integrating fuzzy logic into Prolog would require predicates to be evaluated with a degree of truth, and the unification algorithm to be modified to take this into account.

The syntax `:~`  would be used  instead of `:-` to define fuzzy clauses. For example:
```pl
experienced(X) :~ trapezoidal(2, 5, 10, 15).

skilled(alice) :~ 0.8.
skilled(bob) :~ 0.6.

good_candidate(X) :~ skilled(X), experienced(X).
```
Defines the fuzzy predicate `experienced/1` with a trapezoidal membership function, and the fuzzy predicate `skilled/1` with specific truth values for Alice and Bob. The `good_candidate/1` predicate is then defined as the conjunction of `skilled/1` and `experienced/1`, which would be evaluated using the fuzzy conjunction operator.

= Project Specification
== User Requirements <sec:user_requirements>
I have identified two main personas for this project. The first is someone interested in logic programming and Prolog, who wants to understand how a Prolog engine works. This user would be interested in the implementation details of the engine, and would therefore expect it to be well-documented and easy to read. The second persona is someone who wants to execute Prolog queries, either by writing Prolog programs and executing them with the engine, or by using the engine as a library in other Rust programs.

The design should be implemented in modern Rust, using idiomatic Rust features and best practices to ensure the code is clear and maintainable. Any unsafe code should be clearly marked and justified, as this would be important for the first persona who is interested in understanding the implementation details of the engine.

Clear documentation, including both explanatory comments in the code and documentation comments for the API, would be important for both personas. The first persona would benefit from clear documentation to understand the implementation, while the second persona may wish to verify or extend the engine's functionality.

The structure of the code should be easy to understand, with clear separation between the parser, translator, and engine. This would benefit both personas, as the first would be interested in understanding the implementation details of each component, while the second may wish to verify or extend the functionality of specific components.

As well as the above general requirements, the implementation will be verified with a use case that is designed to test the key features of the engine, such as unification and backtracking.

== Success Criteria <sec:success_criteria>
#todo(done: true)[User]
#todo(done: true)[Execution of Prolog queries]
#todo(done: true)[All fully justified]
This project's success criteria are based on the user's requirements identified in @sec:user_requirements.

To be successful, the parser must be able to read valid Mini-Prolog syntax and use it to generate an abstract syntax tree representing the user-facing syntax. It must also provide meaningful error messages when it encounters invalid syntax.

The translator must correctly translate the user-facing syntax tree into an internal syntax tree representing Dewey and Hardekopf's internal syntax. This includes correctly handling the translation of lists, pattern matching, and unification.

The execution engine must correctly implement the execution model defined by Dewey and Hardekopf, including the handling of the goal stack, environment, and choice stack. The unification algorithm must be implemented correctly according to their design.

These three components will be individually tested with a comprehensive suite of test cases. The entire system will also be tested with a predefined set of Prolog programs and queries, which should produce the expected results. The engine should be usable for executing Prolog queries both by loading Prolog programs and by using the engine as a library in other Rust programs.

The identified validation use case should be implemented using the engine, and it should produce the expected results. This will verify that the implementation meets the user requirements and success criteria.

As well as functional requirements, the code should be well-documented, with clear explanations of the implementation and usage. The code should be clear and maintainable, following Rust best practices and idiomatic usage. Any unsafe code should be clearly marked and justified. The performance of the engine should be reasonable for a simple Prolog implementation, although it is not expected to be competitive with highly optimized Prolog engines.

= Design
== High-Level Architecture
#todo(done: true)[`nom` parser]
#todo(done: true)[AST representation]
#todo(done: true)[Engine structure as defined by Dewey @dewey_mini]

The design consists of three parts: a parser to generate an abstract syntax tree (AST) from user-facing syntax, a translator to convert the user-facing syntax to the internal syntax, and an engine to execute the program using the syntax tree of the internal syntax. Each of these parts will be implemented as separate Rust modules, with clear interfaces between them.

The parser will be written using _nom_, a popular parser combinator library in Rust @nom_github. This will be used to generate an abstract syntax tree representing the user-facing syntax. Ivan Bratko's _Prolog_ @bratko_prolog_1990 will be used as reference for Prolog's syntax.

The user-facing syntax tree will then be translated into a syntax tree representing Dewey and Hardekopf's internal syntax @dewey_mini. Using this internal syntax simplifies the implementation of the engine. It does this by removing unnecessary 'syntactic sugar' from the user-facing syntax, such as lists and pattern-matching, and translating them into simpler constructs.

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

Parsing functions will be implemented as Rust traits on the abstract syntax tree types. This ties the parsing logic closely to the data structures representing the syntax. A `Parseable` trait will be defined, which requires a `parse` function that takes an input string and returns a result containing the parsed abstract syntax tree node or an error. This allows for a consistent interface for parsing different types of abstract syntax tree nodes:
```rs
pub trait Parseable: std::fmt::Display + Sized {
    fn parse(input: &str) -> nom::IResult<&str, Self>;
}
```
_nom_ parsers return an `IResult` type, which can represent either a successful parse with the remaining input and the parsed value, or an error. This allows for robust error handling, as the parser can provide meaningful error messages when it encounters invalid syntax.

Each parsing function will be thoroughly tested with a variety of valid and invalid input to ensure it behaves as expected and provides helpful feedback to users. They will also be documented with example usage, which are also tested with `cargo test` to ensure they remain correct.

=== Abstract Syntax Tree
#todo(done: true)[Representation of Prolog constructs]
#todo(done: true)[Design choices, difference between `enum`s and `struct`s]

The Abstract Syntax Tree (AST) represents the structure of the Prolog program in a way that is easier to work with. Rust provides two main ways to represent data structures: enums and structs.

Enums are used for data that can take on one of several different forms. For example, a Prolog term can be an atom, a variable, or a compound term. Structs are used for data that has a fixed structure. For example, a clause always consists of a head and a body. Rust makes handling these different types of data straightforward, and the choice between enums and structs is guided by the nature of the data being represented. See @tab:ast_overview for an overview of the main abstract syntax tree node types used in the implementation.

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
The engine will be implemented based on the design given by Dewey and Hardekopf @dewey_mini. This implementation uses a state consisting of an environment, equivalence relations between values, a goal stack, and a choice stack.

An environment is a mapping from variables to values. Variables can be one of three types: a number, ground term, or placeholder. A ground term is an atom or compound term that does not contain any variables. A placeholder is a variable that has not yet been unified with any value @dewey_mini.

These values are stored in equivalence classes, which are sets of values that have been unified together. Each equivalence class has a _set representative_, which is the value that represents the class. The classes are stored as a mapping between two values, in order to form a chain of equivalences. The set representative of a value can be found by following the chain of equivalences until a value is reached that is not mapped to any other value. For example, if `X` is unified with `Y`, and `Y` is unified with `Z`, then the equivalence classes would be `{X, Y, Z}`, with `Z` as the set representative @dewey_mini.

The goal stack is fundamental to the execution of Prolog queries. To execute a query, the engine attempts to unify the query with the head of the goal stack. If this is not possible, the engine attempts to use the clauses in the program to derive new goals that can be unified with the query. This process continues until a solution is found or all possibilities have been exhausted @dewey_mini @bratko_prolog_1990.

As well as goals, the goal stack also contains _restoration points_, which allow for local variables within clauses. When evaluating a check expression in the body of a clause, a restoration point is pushed onto the goal stack containing the current environment of the engine. A new environment can then be generated for the execution of the check expression. The original environment will be restored only after the check expression has been evaluated because the restoration point is pushed before the check goal, and so it will only be reached after the check goal has been evaluated @dewey_mini.

When a disjunction is encountered, either through a clause with multiple definitions or through the `;` operator, a choice point is pushed onto the choice stack. This allows the engine to backtrack and try alternative paths if the current path fails. These choice points contain the entire state of the engine at the point of the disjunction @dewey_mini.

=== The Unification Algorithm <sec:unification>
#todo(done: true)[Implementation details]
#todo(done: true)[Comments on Dewey's version]

Vital to any Prolog engine is the unification algorithm. This is the algorithm that attempts to make two terms identical by finding an equivalence between them @dewey_mini.

To unify two terms $v_1$ and $v_2$, we consider the following cases:
+ If $v_1$ and $v_2$ are identical, then they are already unified.
+ If one of the terms is an unassigned (placeholder) variable, then we can unify them by assigning the variable to the other term.
+ If both terms are compound terms with the same functor and arity, then they can be unified if each of their corresponding arguments can be unified.
If none of these cases apply, then the terms cannot be unified and unification fails @dewey_mini.

This algorithm is implemented as a method on the equivalence struct. When called with two values, it attempts to unify them and updates the equivalence classes accordingly. If unification fails, it returns an error. Implementing it in this way allows the unification logic to be encapsulated within the equivalence struct, and so the engine is abstracted from the details of unification and the representation of equivalence classes @dewey_mini.

This algorithm, as given by Dewey and Hardekopf, is simple to understand and implement, making it suitable for this project. However, given the importance of unification to the performance of a Prolog engine, there are more efficient algorithms that could be implemented in future work, for example that used by the WAM @ait-kaci_warrens_1991.

== Handling Fuzzy Logic
In order to support fuzzy logic, most parts of the engine would need to be modified.

The parser and abstract syntax tree would need to be modified to support the new syntax for fuzzy clauses and predicates, as well as the internal representation.


= Testing
== Correctness
#todo[Test cases]
#todo[Running examples]
The correctness of the implementation will be verified through a comprehensive suite of test cases. These will form a test pyramid, with a large number of unit tests for individual components, a smaller number of integration tests for the interaction between components, and a few end-to-end tests that execute complete Prolog programs.

Rust has excellent support for testing, with a built-in testing framework that allows for easy writing and running of tests. Unit tests will be written for the parser, translator, and engine components, while integration tests will verify the correct interaction between these components. End-to-end tests will execute complete Prolog programs and verify that the results are as expected.

These tests will be run automatically on each commit through continuous integration, ensuring that any regressions are quickly identified and addressed.

In addition to these standard tests, Rust also supports documentation tests, where code examples in documentation comments are automatically tested. This acts as both extra unit tests and ensures that the documentation remains correct.

== Verification
#todo[Identify a good concrete use case]
To verify that the implementation meets the user requirements and success criteria, a concrete use case will be identified and developed.

This use case will be a Prolog program similar to one the target user might want to write, and will be designed to test the key features of the engine, such as unification and backtracking. The program will be executed using the engine, and the results compared to the expected results to verify correctness.

== Performance
#todo(done: true)[Benchmark against other implementations]

Although performance is not a primary focus of this project, it must still be reasonable. To verify this, the implementation will be benchmarked against other Prolog implementations. These benchmarks will include both synthetic benchmarks, such as reversing lists and quicksort, and larger, more complex Prolog programs.

If there is time, the implementation of some optimisations could be explored, and these benchmarks used to verify their effectiveness.

= Description of the Final Product

= Evaluation of the Final Product
#todo[Comparison with other Prolog implementations]
#todo[User feedback?]

= Critical Assessment of the Project as a Whole

= Conclusion
== Reflection

== Future Work
#todo[Implementing the WAM for performance and full Prolog support]

== Summary

= Appendix
#appendix[Project Gantt Chart] <appendix:gantt>
A Gantt chart for this project is given in @fig:gantt.

#figure(
  placement: auto,
  caption: [Project Gantt chart. Columns are weeks.],
)[
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

      task(
        [Research],
        (from: 0, to: 12),
      )

      task(
        [Report Writing],
        (from: 7, to: 19),
      )

      task(
        [Testing and Evaluation],
        (from: 11, to: 18),
      )

      task(
        [Poster Creation],
        (from: 12, to: 14.7),
      )

      task(
        [Prepare Demos],
        (from: 13, to: 19),
      )

      task(
        [Continuous Integration Setup],
        (from: 0, to: 1),
      )

      task(
        [Abstract Syntax Tree Definitions],
        (from: 0, to: 1.5),
      )

      task(
        [Parsing Functions],
        (from: 0.5, to: 3),
      )

      task(
        [Parser Integration Tests],
        (from: 2.5, to: 3.5),
      )

      task(
        [Engine Outline],
        (from: 3, to: 4),
      )

      task(
        [Internal Representation],
        (from: 3.5, to: 5),
      )

      task(
        [Engine Structure],
        (from: 4.5, to: 5.5),
      )

      task(
        [Unification Algorithm],
        (from: 5.5, to: 6),
      )

      task(
        [Engine Integration Tests],
        (from: 6, to: 7),
      )

      task(
        [Translator],
        (from: 8, to: 10),
      )

      task(
        [Translator Integration Tests],
        (from: 9.5, to: 10.5),
      )

      task(
        [Integration Testing],
        (from: 10.5, to: 12.5),
      )

      task(
        [Fuzzy Logic Research],
        (from: 5, to: 8),
      )

      task(
        [Fuzzy Logic Design],
        (from: 12, to: 13.5),
      )

      task(
        [Fuzzy Logic Implementation],
        (from: 13, to: 15),
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
] <fig:gantt>
