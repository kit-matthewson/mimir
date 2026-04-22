#import "template.typ": *

#import "@preview/timeliney:0.4.0"
#import "@preview/cetz:0.4.2"
#import "@preview/lilaq:0.6.0" as lq

#set text(lang: "en")

#show: template.with(
  title: [A Rust Implementation of Mini-Prolog including Fuzzy Logic Support],
  author: "Kit Matthewson",
  student-id: "730002704",
  date: datetime.today(),
  abstract: [
    This dissertation explores the design and implementation of a Mini-Prolog interpreter in Rust. The project is motivated by the rise of large language models (LLMs) and the need for explainable AI (XAI) systems that can provide formal guarantees and explanations for their outputs. Based on Dewey and Hardekopf's specification for Mini-Prolog, the interpreter implements a core subset of Prolog, omitting features like cut and meta-programming to simplify implementation.

    Rust was chosen for its modern features, performance, and safety guarantees. The architecture comprises a parser, a translator to an internal syntax, and an execution engine. The parser is implemented using the _nom_ combinator library, while the engine follows a stack-based execution model.
  ],
  table-of-contents: outline(),
)

#show figure.where(kind: raw): set box(stroke: 1pt)

= Introduction
The goal of this dissertation was the implementation of a Mini-Prolog interpreter in Rust, with the stretch goal of adding fuzzy logic support. This starts with an implementation based on an article by Dewey and Hardekopf @dewey_mini, which defines a simple Prolog engine with a focus on simplicity over performance. This implementation was then extended to support fuzzy logic, a new contribution that allows the engine to handle uncertainty and imprecision in a way that standard Prolog cannot.

Prolog is a simple but powerful programming language developed in the artificial intelligence group at the University of Marseille in the early 1970s. Its original intention was to process natural language in an attempt to create a ‘man-machine communication system’ @colmerauer_birth_1992.

Since then, it has become a popular choice for both teaching and using logic programming @bratko_prolog_1990. With roots in formal logic, Prolog is particularly well-suited for applications in theorem proving @stickel_prolog_1992, expert systems @merritt_building_2012, and natural language processing @shieber_prolog_2005.

As a _declarative_ language, the Prolog programmer describes _what_ should be accomplished rather than _how_. A Prolog program is not executed in the traditional sense. Instead, the program is _queried_. The engine attempts to find solutions to the query by unifying it with clauses from the program and logical inference @bratko_prolog_1990.

A Prolog program consists of a database of _clauses_. Clauses with no body are referred to as _facts_, whilst those that have a body are referred to as _rules_. Facts are unconditional statements about the world, while rules define relationships between facts using logical implications. For example, consider:

```
edge(a, b).
edge(b, c).
edge(c, d).
edge(n, p).

path(X, Y) :-
    edge(X, Y).
path(X, Y) :-
    edge(X, Z), path(Z, Y).
```

This program defines a graph with edges between nodes a, b, c, and d. Three facts define the edges of the graph: `edge(a, b)`, `edge(b, c)`, and `edge(c, d)` are all considered true. The `path/2`#footnote[Predicates are referred to by their name and arity (the number of arguments they take), separated by a slash.] predicate is defined with two clauses. The first defines the base case, that `path(X, Y)` is true if `edge(X, Y)` is true. The second defines the recursive case, that `path(X, Y)` is true if there is an edge from `X` to some `Z` and a path from `Z` to `Y`. Note that these rules will be tried in the order they are defined, so the engine will always try the base case first.

The program can then be queried. A query of `path(a, d)` returns true, whilst `path(a, p)` is false. Queries can be more complex if they use variables, for example `path(a, X)` returns `X = b; X = c; X = d;`. All possible pairs of connected nodes would be returned by `path(X, Y)`.

Prolog uses a process called _unification_ to answer queries. Unification is an algorithm that attempts to make two terms identical by finding a substitution for their variables @clocksin_programming_2003. For instance, in the above example the variable `X` in the query `path(a, X)` can be unified with `b`, `c`, and `d`.

The language chosen for the implementation is Rust, a modern systems programming language first released in 2010. The main focus of Rust is on memory safety whilst maintaining high performance, making it a popular choice for tasks traditionally handled by C or C++ @bugden_rust_2022. As a major example, Rust has been adopted as one of the languages accepted into the Linux kernel @nichols_rust_2024.

== Rust
Anyone who has written C or C++ will be familiar with issues such as buffer overflows, memory leaks, and use-after-free errors. Rust uses an ownership model, where there is always exactly one owner of memory at any given time, to prevent these issues. When sharing data, the user can choose to transfer ownership (moving), create an immutable reference (borrowing), or clone the data. The memory is automatically freed when its owner goes out of scope, preventing the need to manually manage memory @bugden_rust_2022. It should be noted that these restrictions can be escaped using `unsafe` blocks, allowing the user to manually manage memory if absolutely necessary, whilst making these regions of code explicit and easily identifiable @rust-lang.

As well as safety, Rust has modern features such as options and pattern matching, a powerful macro system, and a rich type system with generics and traits. It manages to provide these features whilst still being a compiled language with performance comparable to C and C++ @bugden_rust_2022.

Rust also has excellent tooling, with `cargo` as its built-in package manager and build system. It provides commands for managing dependencies, building and running the program, running tests, and maintaining code quality with linting and formatting.

These tools help streamline development and maintain code quality @rust-lang. Their simplicity also makes continuous integration (CI) straightforward to set up.

The language also has good documentation features, with `rustdoc` able to generate HTML documentation from documentation comments in the source code. If these comments contain example code, `cargo test` will include them in the test suite to ensure they remain correct @rust-lang.

== Fuzzy Logic
As a stretch goal, the Prolog engine will be extended to support fuzzy logic. Fuzzy Logic was introduced in 1965 by Lotfi Zadeh as a way to deal with the uncertainty and imprecision inherent in many real-world applications @zadeh_fuzzy_1965.

In a standard boolean logic system, propositions are either true or false. This can be expanded to a multi-valued logic system, where propositions take on values from a finite set $T$. In fuzzy logic, this is expanded further to allow truth values taken from the continuous interval $[0, 1]$, where 0 is the boolean false, 1 is the boolean true, and values in between represent varying degrees of truth @zadeh_fuzzy_1988.

Using fuzzy logic allows for predicates to be evaluated with a degree of truth, rather than just true or false. For example the predicates 'tall', 'ill', or 'tired' are best evaluated as fuzzy predicates instead of boolean predicates @zadeh_fuzzy_1988.

Boolean logic allows for only two quantifiers: 'for all' and 'there exists'. In contrast fuzzy logic allows for any number of such quantifiers, such as 'most', 'several', or 'about ten' @zadeh_fuzzy_1988.

The boolean operators _conjunction_, _disjunction_, and _negation_ need to be replaced with fuzzy equivalents. A common way this is done is to use minimum for conjunction, maximum for disjunction, and $1 - p$ for negation, called the _Zadeh operators_ @zadeh_fuzzy_1965. Consider how with $italic("true") = 1$ and $italic("false") = 0$ these operators behave identically to their boolean counterparts.

Membership functions evaluate the degree of truth of a predicate for a given input. For example, a trapezoidal membership function for the predicate 'warm' could define temperature values below 15 degrees as 0, between 20 and 25 degrees as 1, above 30 degrees as 0, and values in between as a linear interpolation between these points @zadeh_fuzzy_1988.

#figure(
  caption: [Example fuzzy sets for temperature.],
  placement: none,
)[
  #let exeter-light = rgb("#00c896")
  #let exeter-dark = rgb("#003b3b")

  #cetz.canvas({
    import cetz.draw: *

    let axes-stroke = 1pt + black
    let set-stroke = 2pt

    let height = 2.5
    let width = 6
    let top = height - .5

    // Sets
    let cold = (
      (0, top),
      (0.2 * width, top),
      (0.4 * width, 0),
    )

    line(..cold, stroke: set-stroke + exeter-dark, name: "cold")
    content((0.1 * width, top + .2), text(fill: exeter-dark, size: .7em)[cold])

    let warm = (
      (0.2 * width, 0),
      (0.4 * width, top),
      (0.6 * width, top),
      (0.8 * width, 0),
    )

    line(..warm, stroke: set-stroke + exeter-light, name: "warm")
    content((0.5 * width, top + .2), text(fill: exeter-light, size: .7em)[warm])

    let hot = (
      (0.6 * width, 0),
      (0.8 * width, top),
      (width, top),
    )

    line(..hot, stroke: set-stroke + exeter-dark, name: "hot")
    content((0.9 * width, top + .2), text(fill: exeter-dark, size: .7em)[hot])

    // Axes
    line((-.1, 0), (width, 0), stroke: axes-stroke, mark: (end: ")>"))
    line((0, 0), (0, height), stroke: axes-stroke, mark: (end: ")>"))
    content((width / 2, -.3), text(fill: black, size: .8em)[Temperature])
    content((-.3, 0), text(fill: black)[0])
    line((-.1, top), (0, top), stroke: axes-stroke)
    content((-.3, top), text(fill: black)[1])
  })
] <fig:sets>

Integrating fuzzy logic into Prolog would require predicates to be evaluated with a degree of truth, and the unification algorithm to be modified to take this into account.

= Motivation
One of the motivations for this project is the rise of large language models (LLMs) and the need for explainable AI (XAI) systems. LLMs have impressive capabilities but their complexity and lack of transparency make them unsuitable for applications where safety and correctness are paramount @bommasani_opportunities_2022 @wang_decodingtrust_2024. In contrast, Prolog's logical foundations and declarative nature make it a good candidate for building explainable AI systems, particularly in the form of expert systems @dwivedi_explainable_2023.

Expert Systems consist of a knowledge base and an inference engine which applies logical reasoning to the knowledge base to derive new facts or make decisions @griffin_fuzzy_2024 @clark_prolog_1980. Enhancing Prolog with fuzzy logic capabilities would allow it to handle the uncertainty and imprecision inherent in many real-world applications @kosko_fuzzy_1993.

The creation of a Prolog engine from scratch is also a valuable learning experience. It allows for a deep understanding of the methods underlying Prolog, such as unification and backtracking, which in turn prove useful for writing efficient Prolog.

= Aims \& Objectives
The aim of this project is to use Rust to implement a Mini-Prolog interpreter capable of parsing and evaluating Prolog queries. This will involve two parts: creating a parser to read Mini-Prolog syntax and convert it into an internal representation, and implementing an evaluation engine to answer Prolog queries based on this representation.

There are multiple target use cases for this project. The first is as a learning tool for myself and others interested in logic programming and Prolog. By implementing a Prolog engine from scratch, I can gain a deeper understanding of how Prolog works and the underlying algorithms involved. The second use case is as a tool for executing Prolog queries. This could be done by writing Prolog programs and executing them with the engine, or by using the engine as a library in other Rust programs. The design and implementation of the project will be guided by these use cases.

Fuzzy logic support is a stretch goal for this project. If implemented, it would allow the engine to evaluate predicates with a degree of truth rather than boolean true or false. This would expand the capabilities of the engine to include the uncertainty and imprecision common in real-world applications.

== User Requirements <sec:user_requirements>
I have identified two personas for this project. The first is someone interested in logic programming and Prolog, who wants to understand how a Prolog engine works. This user would be interested in the implementation details of the engine, and would therefore expect it to be well-documented and easy to read. The second persona is someone who wants to execute Prolog queries, either by writing Prolog programs and executing them with the engine, or by using the engine as a library in other Rust programs.

The design should be implemented in modern Rust, using idiomatic Rust features and best practices to ensure the code is clear and maintainable. Any unsafe code should be clearly marked and justified, as this would be important for the first persona who is interested in understanding the implementation details of the engine.

Clear documentation, including both explanatory comments in the code and documentation comments for the API, would be important for both personas. The first persona would benefit from clear documentation to understand the implementation, while the second persona may wish to verify or extend the engine's functionality.

The structure of the code should be easy to understand, with clear separation between the parser, translator, and engine. This would benefit both personas, as the first would be interested in understanding the implementation details of each component, while the second may wish to verify or extend the functionality of specific components.

= Design \& Implementation
== Mini-Prolog
For this project, the implementation will target a subset of Prolog referred to as _Mini-Prolog_. This is based on the specification given by Dewey and Hardekopf @dewey_mini. Mini-Prolog simplifies the implementation of a Prolog engine by removing some features from Prolog, and so allowing the use of an internal syntax.

The removed features are cut, clause management predicates, meta-programming operators, and built-in predicates.

The _cut_ operator allows the programmer to control backtracking by instructing the Prolog engine not to attempt any further alternatives. This removes _negation as failure_ by extension, as it is implemented using cut. There are only a few cases where cut is necessary for the execution of a program, it is most often used to improve the efficiency of a program.

Clause management predicates allow the programmer to modify the program at runtime by adding or retracting clauses. This is a powerful feature used in some programs but is not necessary for the execution of most Prolog programs. Note also that if the implementation is being used as a library in a Rust program, the user could implement this functionality externally.

Full Prolog implementations often include built-in _meta-programming_ operators, which allow the programmer to reason about the program itself. For example, `bagof/3` allows the programmer to generate a list of all solutions to a query. As with clause management predicates, this feature could be implemented externally by users of the engine as a library.

Dewey and Hardekopf introduce an internal syntax that can be produced from the user-facing syntax by a translation step. This internal syntax removes syntactic sugar from the user-facing syntax, such as lists and pattern-matching, and translates them into structures that can be handled with simple unification.

The internal syntax replaces lists with `cons/2` structures. For example, the user-facing syntax `[1, 2, 3]` becomes `cons(1, cons(2, cons(3, nil)))`. This means that the engine does not need to implement any special handling for lists, as they are just a specific case of compound terms.

Pattern matching can always be replaced with some number of unification operations. Matching for an empty list, for example, can be replaced by unification with `nil`.

The head of a clause is changed so that it only contains variables. This can be achieved by inserting a number of unification steps at the beginning of the body of the clause to unify new variables in the head with the original terms in the head. In addition to this, a list of local variables is added alongside the head of the clause, which contains all the variables used in the clause. This has no effect on the execution of the program (as all Prolog variables are clause-local anyway), but simplifies the implementation of the engine by making it clear which variables are in scope at any given point.

Unification between arbitrary values can be replaced with variable bindings and unification on these variables. A variable _binding_ ($arrow.l$) differs from unification ($equiv$) in that it creates an equivalence between the variable and the value, but does not attempt to unify them. By using this translation, the engine only needs to implement unification between variables.

The user-facing syntax:
```
allLess(_, []).
allLess(V1, [V2 | Rest]) :-
    V2 < V1,
    allLess(V1, Rest).
```
Would be translated to:
```
allLess(T1, T2) {T3} :-
  T3 ← nil(),
  T2 ≡ T3.

allLess(V1, T1) {V2, Rest, T2} :-
  T2 ← cons(V2, Rest),
  T1 ≡ T2,
  V2 < V1,
  allLess(V1, Rest).
```

== High-Level Architecture
The design consists of three parts: a parser to generate an abstract syntax tree (AST) from user-facing syntax, a translator to convert the user-facing syntax to the internal syntax, and an engine to execute the program using the syntax tree of the internal syntax. Each of these parts will be implemented as separate Rust modules, with clear interfaces between them.

The parser will be written using _nom_, a popular parser combinator library in Rust @nom_github. This will be used to generate an abstract syntax tree representing the user-facing syntax. Ivan Bratko's _Prolog_ @bratko_prolog_1990 will be used as reference for Prolog's syntax.

The user-facing syntax tree will then be translated into a syntax tree representing Dewey and Hardekopf's internal syntax @dewey_mini.

The engine will be structured as defined by Dewey and Hardekopf @dewey_mini, which has a focus on simplicity over performance. It uses a goal stack to keep track of the current goals being evaluated, and an environment to keep track of variable bindings. The engine will implement the unification algorithm to evaluate queries.

These three components are separated into Rust modules, with clear interfaces between them. This allows for a clear separation of concerns, making the code easier to understand and maintain.

This design is chosen to meet the identified user requirements and success criteria. The use of Rust ensures the implementation is in a modern language with good performance and safety guarantees. The use of _nom_ allows for a clear and maintainable parser, while the use of a translator to an internal syntax provides clear separation of concerns and simplifies the engine implementation.

The engine structure defined by Dewey and Hardekopf is chosen for its simplicity, which is appropriate for this project given the focus on understanding and correctness over performance.

== Parser Design
Using the _nom_ library, the parser will be implemented as a series of combinators that match the grammar of Mini-Prolog. The grammar will be based on the standard Prolog syntax as given in Bratko's _Prolog_ @bratko_prolog_1990, with adjustments to fit the Mini-Prolog subset defined by Dewey and Hardekopf @dewey_mini.

Nom provides combinators for matching patterns in the input string, from specific character sequences to repetitions and alternatives. These are composed together to create parsers for more complex structures @swierstra_combinator_2009.

The parser produces an abstract syntax tree (AST) representing the user-facing syntax. This AST will be defined using Rust's enums and structs. Enums are used for data that can take on one of several different forms, such as a 'goals' which make up the body of a clause:
```rs
pub enum Goal {
    Relation(Term, RelationalOp, Term),
    Assign(Variable, Rhs),
    Check(Compound),
}
```
Structs are used for data that has a fixed structure, such as a clause which always consists of a head and a body:
```rs
pub struct Clause {
    pub head: Compound,
    pub body: Vec<Goal>,
}
```
A parsing _trait_ is then defined. Traits in Rust are similar to interfaces in other languages, and allow for a consistent interface for parsing different types of AST nodes. The `Parseable` trait requires a `parse` method which takes an input string and returns a result containing the parsed AST node or an error.

Attaching the parsing functions to the AST types in this way allows for a clear and maintainable design, as the parsing logic is closely tied to the data structures representing the syntax. For example, when defining the parsing of the `Clause` struct, we can call the parsing functions for the `Compound` type to parse the head of the clause, and then the parsing functions for the `Goal` enum to parse the body of the clause.

In addition to requiring a `parse` function, the `Parseable` trait also requires that the type implement the `Display` trait. This is a built-in Rust trait that allows the printing of the type in a human-readable format. By requiring this, we can easily test the parsing functions by comparing an input string to the output of the `Display` implementation for the parsed type. For example:
```rs
let input = "path(X, Y) :- edge(X, Z), path(Z, Y).";
let (_, clause) = ast::Clause::parse(input).unwrap();

assert_eq!(clause.to_string(), input);
```
Nom allows 'context' to be added whilst parsing. When parsing a pair of brackets we can attach this context so that syntax error messages can provide more useful information on what caused them.

Each parsing function will be thoroughly tested with a variety of valid and invalid input to ensure it behaves as expected and provides helpful feedback to users. They will also be documented with example usage, which are also tested with `cargo test` to ensure they remain correct.

The parsing module provides two public functions: one for parsing a program and one for parsing a query. The program parsing function attempts to consume a string of as a sequence of clauses, while the query parsing function attempts to consume a string as a single goal. Both functions return an AST representing the parsed input, or an error if the input is invalid or is not fully consumed.

== Translator Design
The primary function of the translator module is to take a syntax tree representing a user-facing clause and translate it into the internal representation of a clause.

The translator starts with the head of the clause, which starts as a compound with arbitrary terms as arguments. This needs to be converted into a compound with only variables as arguments, which can be achieved by replacing any non-variable terms with a new variable and adding unification goals to the body of the clause.

Each goal of the body can then be translated individually. Each user-facing goal may map to a number of internal goals, for example internal relational operators can only compare variables, so any non-variable terms are replaced with new variables and unification goals. The user-facing goal:
```
X + 1 > 3
```
Would be translated into multiple internal goals:
```
T1 ← X + 1,
T2 ← 3,
T1 > T2
```
An internal clause technically only has one goal, which is produced by folding multiple goals into conjunctions. Using this method, the above goals would be folded into: `((T1 ← X + 1, T2 ← 3), T1 > T2)`.

Wildcard variables (represented by variables starting with an underscore in the user-facing syntax) are replaced with new, arbitrary, variables. Because these variables are ensured to be unique, they will unify with any term and so can be used in place of wildcards without requiring any special handling by the engine.

Throughtout the translation process, a state is maintained to keep track of new local and wildcard variables. This ensures that all the translation functions can generate new variables without needing to worry about name clashes.

Once all of the goals have been translated, a final pass of the full body is completed to collect a list of the local variables used in the body, which is added to the clause alongside the head.

== Crisp Engine Design
The design for the crisp (standard) Prolog engine is based on the specification given by Dewey and Hardekopf @dewey_mini. This design is chosen for its simplicity, which is appropriate for this project given the focus on understanding and correctness over performance.

The goal of the engine is to take a Mini-Prolog program and query and find a satisfying assignment of variables in the query (if one exists). The engine will attempt to find different solutions until it has found all of them.

The engine maintains a state consisting of a clause database, environment of variable bindings, equivalence relations between values, a goal stack, and a choice stack.

In Rust, the clause database is represented as a mapping from predicate names and arities to lists of clauses. This makes it easy to look up the clauses relevant to a particular goal during execution. It is important that the multiple clauses that define a predicate are stored in the same order as they appear in the program, as the engine must try them in this order.

The environment uses a hash map between variables and values, where values can be numbers, ground terms, or placeholders. Ground terms are structures that consist of a functor and a list of arguments, where all the arguments are themselves values. Placeholders are used to represent variables that have not yet been unified with any value. They are therefore free to be unified with any value.

The `Environment` struct provides an interface to the environment, by providing methods for creating new environments, looking up variable bindings, and adding new bindings.

When an environment is created for a symbol, such as when entering a clause, the symbol's parameters are assigned using the provided arguments and all other variables are assigned to new placeholders. This ensures that variables are clause-local, as they will only be unified with values within the clause.

When values are looked up in the environment, the equivalence relations are also followed to find the set representative of the value. This ensures that if a variable has been unified with another variable or a ground term, the correct value is returned.

The equivalence relations are stored as a mapping between two values, which allows for the formation of chains of equivalences. Unifying values, which is done through the `Equivalence` struct, can only be done if one value is a placeholder, or if both values are ground terms. In the case of placeholders, an equivalence is created between the placeholder and the other value. In the case of two ground terms, it is first checked that they are the same term (have the same functor and arity), and then each pair of arguments is unified recursively. If any of these unifications fail, then the unification fails.

Creating equivalences in this way leads to chains of equivalences, called _equivalence classes_, where all values in the class are unified with each other. For example, if `X` is unified with `Y`, and `Y` is unified with `Z`, then `X`, `Y`, and `Z` are all in the same equivalence class, as they are all unified with each other. In this case, `Z` would be the _set representative_ of the class because it is the final value in the chain.

Because of this structure, requesting the value of a variable that has a value of `X` assigned in the environment would return the set representative of the equivalence class that `X` is in.

The goal stack is fundamental to the execution of Prolog queries. To execute a query, the engine attempts to unify the query with the head of the goal stack. If this is not possible, the engine attempts to use the clauses in the program to derive new goals that can be unified with the query. This process continues until a solution is found or all possibilities have been exhausted @bratko_prolog_1990.

In Dewey and Hardekopf's implementation, as well as goals, the goal stack also contains _restoration points_. These allow for local variables within clauses. When evaluating a check expression in the body of a clause, which requires entering new clauses, a restoration point is pushed onto the goal stack containing the current environment of the engine. A new environment can then be generated for the execution of the check expression. Because the restoration point is pushed before the goal of the check expression, the original environment will be restored after the check expression has been evaluated, ensuring that variables in the original environment are not unified with values in the new environment.

When a disjunction is encountered, either through a clause with multiple definitions or through the `;` operator, a choice point is pushed onto the choice stack. This allows the engine to backtrack and try alternative paths if the current path fails..

Choice points are represented as tuples of the goal that should be tried alongside the environment, equivalences, and goal stack to be restored.

If a failure occurs, the engine pops the most recent choice point from the choice stack and restores the state of the engine to that point. It can then resume execution from there, trying the next alternative.

The main body of the engine is a loop that continues until the goal stack is empty. In each iteration, the engine pops the top goal from the goal stack and uses Rust's pattern matching to determine how to handle it.

Conjunctions are the simplest goals to handle, as they only require the engine to push each conjunct onto the goal stack. For disjunctions, a choice point is created for the second disjunct and pushed onto the choice stack, and the first disjunct is pushed onto the goal stack. This allows the engine to try the second disjunct if the first disjunct fails.

An equality goal requires the engine to attempt to unify the values of the variables on either side of the equality. If this unification fails, `false` is pushed onto the goal stack.

Check goals require the engine to look up the relevant clauses in the program and check whether any of them are satisfied. For each clause that matches the goal, a choice point is created and pushed onto the choice stack. The body of the first matching clause is then pushed onto the goal stack.

To handle relational operators between variables, the engine first looks up the values of the variables in the environment. If either variable is not a number, then the _execution_ fails. This is different from a unification failure, as the engine does not backtrack to try alternative paths, but immediately halts. The relational operator is then evaluated on the values of the variables, and if it returns `false`, then `false` is pushed onto the goal stack.

Assignment allows for the evaluation of expressions and the assignment of their values to variables. To handle an assignment goal, the engine first evaluates the right-hand side expression, which may involve looking up variable values in the environment and evaluating any operations. If this evaluation fails, then execution fails. The resulting value is then assigned to the variable on the left-hand side by creating an equivalence between them.

If a `false` goal is encountered, then backtracking is attempted. This involves popping the most recent choice point from the choice stack and restoring the state of the engine to that point. The goal contained in the choice point is pushed onto the goal stack. If there are no more choice points, then execution fails.

== Fuzzy Engine Design
The adaption of Dewey and Hardekopf's design to support fuzzy logic is my own contribution.

My method for adding fuzzy logic support to Prolog consists of allowing predicates to have a truth value, in the form of an expression evaluated to a float. This expression is referred to as the 'truth value expression' of the clause.

The syntax I chose for this was for fuzzy clauses to use `:~` instead of `:-` to separate the head of the clause from its body. The final line of these clauses is then interpreted as a 'truth value expression'. Standard `:-` crisp predicates can be treated as fuzzy clauses that imply a truth value of 1.0, allowing compatibility between fuzzy and crisp predicates.

Using my implementation, a simple fuzzy predicate for 'warm' could be defined as follows:
```
trapezoidal(X, A, _, _, _, 0) :-
  X < A,
trapezoidal(X, A, B, _, _, F) :-
  X >= A,
  X <= B,
  F = (X - A) / (B - A).
trapezoidal(X, _, B, C, _, 1) :-
  X > B,
  X < C.
trapezoidal(X, _, _, C, D, F) :-
  X >= C,
  X <= D,
  F = (D - X) / (D - C).
trapezoidal(X, _, _, _, D, 0) :-
  X > D.

warm(X) :~
  trapezoidal(X, 15, 20, 25, 30, F),
  F.
```
This program starts by defining a predicate `trapezoidal/6` which defines a trapezoidal membership function. This predicate takes an input `X`, the parameters of the trapezoidal function, and returns the degree of truth `F` for the input `X`. Note that this predicate is a standard crisp Prolog predicate, as it uses `:-` and does not have a truth value expression. The second clause defines the fuzzy predicate `warm/1`, which uses the `trapezoidal/6` predicate to evaluate the degree of truth of `warm(X)`. Because this clause uses `:~`, the final line (`F`) is used as the truth value for the clause.

Note a limitation of the implementation: structures cannot be used as truth value expressions. This is why the `warm/1` predicate must get the truth value from the `trapezoidal/6` predicate through the variable `F`, rather than calling `trapezoidal/6` directly as the truth value expression. This does not reduce the types of program that can be created, as all clauses could be written to return their truth value through a variable so that they can be used in this way.

Clauses that are defined using the standard `:-` syntax have a truth value expression of `1.0` automatically added to them, so that they can be handled in the same way as fuzzy clauses.

These syntactic modifications required adding support for floats. Rust's primitive float types, `f32` and `f64`, do not implement the `Ord`, `Eq`, or `Hash` traits. This means that they cannot be compared for order or equality, or used as keys in a hash map. Because these operations are necessary: comparisons are needed to evaluate goals, and the equivalence classes are stored as a hash map, I chose to use the `ordered_float` crate, which provides a wrapper type around floats that implements these traits @ordered_float_github.

The conjunction of fuzzy predicates is evaluated using the Zadeh operators, with minimum for conjunction, maximum for disjunction, and $1 - p$ for negation @zadeh_fuzzy_1965. As goals are evaluated, a running truth value is maintained and updated using these operators.

Standard Prolog implementations 'short-circuit' disjunctions, meaning that if the first disjunct is evaluated as true, then the second disjunct is not evaluated at all. However, when fuzzy goals are being handled we do need to evaluate both sides of disjunctions in order to find the maximum truth value of the disjuncts. The case for multiple clauses defining the same predicate is similar, as they are effectively disjunctions. Therefore, when evaluating a goal, all relevant clauses must be evaluated to find the maximum truth value.

To achieve this, the engine was largely restructured to use a recursive approach, rather than the stack-based approach used in the crisp engine. These modifications were my own contribution, and were necessary to support the evaluation of fuzzy goals. The main loop of the engine was replaced with a single recursive `handle_goal` function, which takes a goal and the current state of the engine as input, and returns a list of possible resulting states.

When the execution needs to branch, due to a disjunction or predicate, the `handle_goal` function is called recursively on the different branches, and the resulting states are collected. When a truth value expression is encountered, the truth value is evaluated using the current environment. If the truth value is below a set threshold, then the state is discarded.

States are only discarded if their truth value is below the threshold. This allows for the engine to return all possible solutions along with their truth values, rather than just the single solution with the highest truth value.

== Success Criteria
Each of the parser, translator, and engine components have key criteria that must be met for the implementation to be considered successful.

The parser must be able to read valid Mini-Prolog syntax and use it to generate an abstract syntax tree representing the user-facing syntax. It must also provide meaningful error messages when it encounters invalid syntax.

Clauses and goals must be parsed correctly, including handling of lists, pattern matching, and unification. The parser must also be able to parse the new syntax for fuzzy predicates if this feature is implemented.

The translator must correctly translate the user-facing syntax tree into an internal syntax tree representing Dewey and Hardekopf's internal syntax. This includes correctly handling the translation of lists, pattern matching, and unification.

To verify the functionality of the translator, a number of test cases will be created with user-facing syntax and their expected internal syntax. The translator will be tested against these cases to ensure it produces the correct internal syntax.

The execution engine must correctly implement the execution model defined by Dewey and Hardekopf, including the handling of the goal stack, environment, and choice stack. The unification algorithm must be implemented correctly according to their design.

Verification of the engine can be achieved with tests for each of the different goals that the engine can handle, such as conjunctions, checks, and relational operators. These tests will involve checking the engine's internal state before and after handling a goal, to ensure that it behaves as expected. For example, when handling a conjunction, the engine should push each conjunct onto the goal stack.

The most concrete success criterion is that the implementation produces the expected results for a predefined set of Prolog programs and queries. These will be complete programs that test all the key features of the engine. These can be constructed so that they have well-defined correct results for a variety of queries.

As well as functional requirements, the code should be well-documented, with clear explanations of the implementation and usage. The code should be clear and maintainable, following Rust best practices and idiomatic usage. Any unsafe code should be clearly marked and justified. The performance of the engine should be reasonable for a simple Prolog implementation, although it is not expected to be competitive with highly optimised Prolog engines.

= Methods
== Development Environment
For version control I will use Git, with the repository hosted on GitHub. Using GitHub makes setting up continuous integration (CI) with GitHub Actions straightforward, allowing tests and code quality checks to be automatically run on each commit.

The Rust toolchain will be used for testing, code quality, and documentation. Unit tests can be written using Rust's built-in testing framework, and run with `cargo test`. Code quality can be maintained using `cargo clippy` for linting and `cargo fmt` for formatting, which can be set up as commit hooks to ensure they are run before each commit.

Documentation will be generated using `rustdoc`, which can create HTML documentation from comments in the source code. This documentation can be hosted on GitHub Pages for easy access.

== Testing Strategy
The correctness of the implementation will be verified through a comprehensive suite of test cases. These will form a test pyramid, with a large number of unit tests for individual components, a smaller number of integration tests for the interaction between components, and a few end-to-end tests that execute complete Prolog programs. Rust has excellent support for testing, with a built-in testing framework that allows for easy writing and running of tests.

Unit tests will cover a wide range of cases, including valid inputs, invalid inputs, edge cases, and expected error conditions.

Integration tests will be written to verify the correct interaction between the parser, translator, and engine. End-to-end tests will parse complete Prolog programs from files, translate them into the internal syntax, and execute them with the engine to verify that the results are as expected.

These tests will be run automatically on each commit through continuous integration, ensuring that any regressions are quickly identified and addressed.

In addition to standard testing, Rust also supports documentation tests, where code examples in documentation comments are automatically tested. This acts as extra unit tests and ensures that documentation remains correct.

= Results
== Description of the Final Product
My implementation allows users to execute Prolog queries both by loading Prolog programs and by using the engine as a library in other Rust programs. These programs can be entirely standard (crisp) Prolog, entirely Fuzzy, or a combination of the two.

Fuzzy Prolog predicates use new syntax that I have defined, namely the use of `:~` to separate the head of a clause from its body, and the inclusion of a 'truth value expression' as the final line of the clause. This allows for predicates to be evaluated with a degree of truth, rather than just true or false, and for the use of fuzzy quantifiers.

== Verification
=== Standard Prolog Verification
The implementation of standard, crisp, Prolog can be verified with simple programs that test the key features of the engine. I identified two programs that together test all the key features of the engine: a graph traversal program and a list operations program.

The graph operations program is given in @lst:graph_program. This program tests the engine's ability to handle recursion.

#figure(
  caption: [Graph traversal program.],
)[
  ```
  edge(a, b).
  edge(b, c).
  edge(c, d).
  edge(a, e).

  path(X, Y) :- edge(X, Y).
  path(X, Y) :- edge(X, Z), path(Z, Y).
  ```
] <lst:graph_program>

Example queries and their expected results with this program are given in @tab:graph_verification_results.

#figure(
  caption: [Queries and results for the graph traversal program.],
  placement: auto,
  table(
    columns: 2,
    align: (left,),

    table.header[Query][Expected Result],
    [`path(a, b)`], [`true`],
    [`path(a, e)`], [`true`],
    [`path(b, e)`], [`false`],
    [`path(a, Y)`], [`Y = b; Y = e; Y = c; Y = d`],
  ),
) <tab:graph_verification_results>

The list operations program defines `first/2` and `last/2` to get the first and last elements of a list, `append/3` to append two lists together, `member/2` to check if an element is in a list, and `reverse/2` to reverse a list. The implementation of these predicates is given in @lst:list_program.

#figure(
  caption: [List operations program.],
)[
  ```
  first([H|_], H).

  last([X], X).
  last([_|T], X) :- last(T, X).

  append([], Ys, Ys).
  append([X|Xs], Ys, [X|Zs]) :- append(Xs, Ys, Zs).

  member(X, [X|_]).
  member(X, [_|T]) :- member(X, T).

  reverse([], []).
  reverse([H|T], R) :- reverse(T, RT), append(RT, [H], R).
  ```
] <lst:list_program>

Each of these predicates requires handling lists, including the `[H|T]` syntax for pattern matching against the head and tail of a list. Example queries for these predicates are given in @tab:list_verification_results. Notice how some of the predicates can be used in multiple ways, for example `append/3` can be used to append two lists together and also to remove a prefix or suffix.

#figure(
  caption: [Queries and results for the list operations program.],
  placement: auto,

  table(
    columns: 2,
    align: (left,),

    table.header[Query][Expected Result],
    [`first([1, 2, 3])`], [`1`],
    [`last([1, 2, 3])`], [`3`],
    [`all_less(0, [1, 2, 3])`], [`true`],
    [`all_less(2, [1, 2, 3])`], [`false`],
    [`append([1, 2], [3, 4], X)`], [`X = [1, 2, 3, 4]`],
    [`append(X, [3, 4], [1, 2, 3, 4])`], [`X = [1, 2]`],
    [`member(2, [1, 2, 3])`], [`true`],
    [`member(4, [1, 2, 3])`], [`false`],
    [`member(X, [1, 2, 3])`], [`X = 1; X = 2; X = 3`],
    [`reverse([1, 2, 3], X)`], [`X = [3, 2, 1]`],
  ),
) <tab:list_verification_results>

The results of queries to these programs are well-defined and can be easily verified, making them ideal for testing the correctness of the engine. The implementation does produce the expected results for the set of queries, which verifies that the engine is correctly implementing the execution model of standard Prolog.

=== Fuzzy Prolog Verification
In order to verify the implementation of fuzzy Prolog I used two programs: one that defines a trapezoidal membership function, and one that defines a graph similar to the one used in the graph traversal program, but with fuzzy edges.

The trapezoidal membership function program defines a predicate `trapezoidal/5` that has parameters for an input value $X$ and four parameters of the trapezoidal function. It uses these to create a fuzzy truth expression for the final line of the clause, as dictated by my syntax. The trapezoidal function can be notated as:
#set math.cases(gap: 0.4em)
$
  f(x) = cases(
    0 wide & x < a,
    (x - a) / (b - a) wide & a <= x <= b,
    1 wide & b < x < c,
    (d - x) / (d - c) wide & c <= x <= d,
    0 wide & x > d,
  )
$
Where $a, b, c, d in ZZ$ are the parameters of the function, defining the shape of the trapezoid. This can be defined using my fuzzy Prolog syntax as follows:
```
trapezoidal(X, A, _, _, _) :~
  X < A,
  0.
trapezoidal(X, A, B, _, _) :~
  X >= A,
  X <= B,
  (X - A) / (B - A).
trapezoidal(X, _, B, C, _) :~
  X > B,
  X < C,
  1.
trapezoidal(X, _, _, C, D) :~
  X >= C,
  X <= D,
  (D - X) / (D - C).
trapezoidal(X, _, _, _, D) :~
  X > D,
  0.
```
The implementation was verified using this program by querying it for values of $X$ within each of the different regions of the function, and verifying that the resulting truth value was as expected. For example, querying `trapezoidal(0, 1, 2, 3, 4)` should return a truth value of 0, whilst querying `trapezoidal(1.8, 1, 2, 3, 4)` should return a truth value of 0.8.

The crisp graph defined in @lst:graph_program can be modified by adding a truth value expression to some or all of the `edge/2` predicates, for example: `edge(a, b) :~ 0.8`. This allows for the verification that the Zadeh operators are being correctly applied. A path should have a truth value equal to the minimum of the truth values of all the edges in the path, as the conjunction of the goals in the path is evaluated using the minimum operator. For example, if `edge(a, b) :~ 0.8` and `edge(b, c) :~ 0.6`, then querying `path(a, c)` should return a truth value of 0.6.

This was verified by modifying the graph program in the described way and querying for paths between different nodes, verifying that the resulting truth values were as expected.

== Performance
Although performance is not a primary focus of this project, it must still be reasonable.

Two programs were used to measure the performance of the engine: a program to calculate the Fibonacci sequence, and a program that reverses a list of a given length. These programs were chosen because they are simple to understand whilst having exponential time complexity with the given implementations. The implementations of these programs are given in @lst:performance_programs.

#figure(
  caption: [Fibonacci and list reversal programs used for performance evaluation.],
  placement: auto,
)[
  ```
  fib(0, 0).
  fib(1, 1).
  fib(N, F) :-
      N > 1,
      N1 = N - 1,
      N2 = N - 2,
      fib(N1, F1),
      fib(N2, F2),
      F = F1 + F2.

  reverse([], []).
  reverse([H|T], R) :-
      reverse(T, RT),
      append(RT, [H], R).
  ```
] <lst:performance_programs>

I tested the performance of these programs by running a series of queries with increasing input sizes. For the Fibonacci program I ran queries for `fib(n, F)` and for the list reversal program I ran queries for `reverse(L, R)` where `L` is a list of length `n`. I increased `n` until the execution time surpassed 10 seconds. To compare the performance of my implementation, I ran queries using a similar range of input sizes on SWI-Prolog @swi_github, which is a highly optimised Prolog engine.

To measure the execution time of queries in my implementation, I used Rust's `std::time::Instant` to record the start and end times of query execution. For SWI-Prolog, I used the builtin `statistics/2` predicate which provides the execution time of queries. The differences in these methods is not significant compared to the execution times being measured, which are on the order of seconds.

These measurements are intended to provide a comparison between the engines, and to verify that the performance of my implementation is adequate for simple queries. Therefore, producing exact results is not necessary, and the measurements are sufficient to show the general trend of the execution time as the input size increases.

The results of the performance evaluation are shown in @fig:performance. Both programs show an exponential increase in execution time as the input size increases, which is expected given the nature of the programs. The execution time of my implementation for the Fibonacci program surpasses one second at $n=15$, and the list reversal program surpasses one second at $n=100$.

#figure(
  caption: [Performance of the engine on the Fibonacci and list reversal programs.],
  placement: auto,
)[
  #let exeter-light = rgb("#00c896")
  #let exeter-dark = rgb("#003b3b")

  #grid(
    columns: (45%, 45%),
    // align: (left, right),
    column-gutter: 30pt,
    [
      #let mimir = (
        (0, 0),
        (1, 0),
        (2, 0),
        (3, 0),
        (4, 0),
        (5, 0),
        (6, 0),
        (7, 0),
        (8, 0),
        (9, 11),
        (10, 23),
        (11, 54),
        (12, 120),
        (13, 295),
        (14, 761),
        (15, 1977),
        (16, 8059),
        // (17, 33761),
      )

      #let swi = (
        (0, 0),
        (5, 0),
        (10, 0),
        (15, 1),
        (20, 10),
        (25, 160),
        (26, 252),
        (27, 469),
        // (28, 24893),
      )

      #let mimir_xs = mimir.map(x => x.at(0))
      #let mimir_ys = mimir.map(x => x.at(1) / 1000)

      #let swi_xs = swi.map(x => x.at(0))
      #let swi_ys = swi.map(x => x.at(1) / 1000)

      #lq.diagram(
        title: [Time to calculate $"fib"(n)$],
        xlabel: $n$,
        ylabel: [Time / s],

        lq.plot(mimir_xs, mimir_ys, mark: "s", color: exeter-dark, label: [Mine]),
        lq.plot(swi_xs, swi_ys, mark: "d", color: exeter-light, label: [SWI-Prolog]),
      )
    ],

    [
      #let data = (
        (0, 0),
        (10, 4),
        (20, 17),
        (30, 49),
        (40, 100),
        (50, 181),
        (60, 290),
        (70, 468),
        (80, 648),
        (90, 920),
        (100, 1258),
        (110, 1683),
        (120, 2185),
        (130, 2876),
        (140, 4068),
        (150, 5618),
        (160, 7494),
        (170, 9566),
        // (180, 11483),
      )

      #let xs = data.map(x => x.at(0))
      #let ys = data.map(x => x.at(1) / 1000)

      #lq.diagram(
        title: [Time to reverse a list of length $n$],
        xlabel: $n$,
        ylabel: [Time / s],

        lq.plot(xs, ys, mark: "s", color: exeter-dark, label: [Mine]),
        // SWI-Prolog is 0ms for all list reversal queries
        lq.plot(
          range(0, 250, step: 50),
          range(0, 250, step: 50).map(_ => 0),
          mark: "d",
          color: exeter-light,
          label: [SWI-Prolog],
        ),
      )
    ],
  )
] <fig:performance>

My implementation is significantly slower than SWI-Prolog, which was expected. The simplicity of my design misses out on many of the optimisations that are used in highly optimised Prolog engines such as SWI-Prolog, which uses the Warren Abstract Machine (WAM) @ait-kaci_warrens_1991, and further optimisations such as clause indexing and tail call optimisation.

For simple queries, such as those used in the verification programs, the execution time is typically under a second, which meets the success criteria defined above.

== Evaluation
The implementation meets the success criteria defined in the previous section. The criteria for the parser, translator, and engine are provably met through the comprehensive suite of tests that have been created for each component. The complete implementation has also been verified against a set of Prolog programs with well-defined results, and produces the expected results for all of the queries tested.

For the fuzzy logic features, an intuitive syntax was designed and implemented that ties closely to existing Prolog syntax. The fuzzy execution model is simple to understand and, to the best of my knowledge, unique.

The fuzzy extension was evaluated by checking the truth values returned by a trapezoidal membership function against expected values, which verified that the fuzzy logic features are working as intended. A noted limitation of the fuzzy implementation is that structures cannot be used in truth value expressions, which requires some types of program to be more verbose than they would be if this were supported. An example of such a program would be if one clause has a truth value defined as twice that of another clause.

Performance is clearly a weakness of the implementation, which was anticipated given the focus on simplicity. Improvements to the performance of the engine are discussed in the future work section below.

A key tradeoff in the design is between simplicity and functionality. The design of the engine is focused on simplicity, but this comes at the cost of performance and support for some Prolog features. Implementing a complete Prolog engine such as the Warren Abstract Machine (WAM) would significantly improve performance and support all Prolog features, but would be a much more complex implementation. This would increase the time required to complete the project and would make it more difficult to understand the final product.

= Reflection
== Future Work
There are some features that could be added to the implementation I created for this project that would improve its usability. These include allowing the user to define their own fuzzy operators that could be used instead of the Zadeh operators. This would allow for more flexibility in how fuzzy logic is used in Prolog, and would allow users to define operators that are more appropriate for their specific use case.

Implementing the Warren Abstract Machine (WAM) would be an interesting extension of this project. The WAM is a highly efficient abstract machine designed for executing Prolog programs, and is used by many modern Prolog implementations @ait-kaci_warrens_1991. This would be a significant undertaking, but would allow for much better performance and support for the full Prolog language, including features that were removed in Mini-Prolog.

It would also be interesting to modify an existing Prolog implementation, such as Scryer Prolog @scryer_github, to add support for fuzzy logic using the syntax and semantics I have defined in this project. This would allow for fuzzy logic to be used in a more mature and feature-rich Prolog implementation, and would be a good way to verify the generality of my approach to integrating fuzzy logic into Prolog.

= Conclusion
In this project I have successfully implemented a Prolog engine in Rust, following the design of Dewey and Hardekopf's Mini-Prolog implementation, and then extended it to support fuzzy logic using a novel syntax and execution model.

My project allows users to execute Prolog queries with both crisp and fuzzy predicates, all whilst using an engine with a core algorithm that is simple to understand implemented in a modern language.

I met all of the success criteria and objectives that I set out at the beginning of the project, and this is verified through a comprehensive suite of tests and the successful execution of a set of Prolog programs.

This work significantly increased my knowledge of Prolog and introduced me to Fuzzy Logic, which I had not previously studied. It also gave me experience using Rust in a large project. In wider contexts, this project has applications in teaching Prolog as the simplicity of the engine allows for a clear demonstration of how Prolog works, and in applications that require fuzzy logic such as expert systems and decision making under uncertainty.

The extension of Prolog to support fuzzy logic is an area that could be explored further, especially through the modification of the Warren Abstract Machine or an existing Prolog implementation. This would allow for the performance benefits of these implementations to be combined with the added functionality of fuzzy logic.

#pagebreak(weak: true)

#bibliography("refs.bib", style: "ieee")

#pagebreak(weak: true)

#show heading.where(level: 2): set heading(
  numbering: (..nums) => numbering("A", ..nums.pos().slice(1)),
  supplement: "Appendix",
  outlined: false,
)
#show heading.where(level: 2): it => [
  Appendix #numbering("A", ..counter(heading).get().slice(1)): #it.body \
]
#show heading.where(level: 3): set heading(
  numbering: (..nums) => numbering("1.", ..nums.pos().slice(1)),
  outlined: false,
)

#heading(numbering: none)[Appendices]
== Project Gantt Chart <appendix:gantt>
A Gantt chart for this project is given in @fig:gantt.

#figure(
  placement: none,
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
