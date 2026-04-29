#import "@preview/touying:0.7.3": *
#import themes.metropolis: *

#import "@preview/numbly:0.1.0": numbly

#show: metropolis-theme.with(
  aspect-ratio: "16-9",
  footer: self => self.info.institution,
  config-info(
    title: [A Rust Implementation of Mini-Prolog including Fuzzy Logic Support],
    // subtitle: [University of Exeter],
    author: [Kit Matthewson],
    // date: [30th April 2026],
    institution: [University of Exeter],
    // contact: [km852\@exeter.ac.uk],
    // logo: emoji.city,
  ),
  config-colors(
    primary: rgb("#003c3c"),
    primary-light: rgb("#00a87e"),
    secondary: rgb("#007d69"),
    neutral-lightest: rgb("#ffffff"),
    neutral-dark: rgb("#003c3c"),
    neutral-darkest: rgb("#022020"),
  ),
)

#show raw: set text(.8em)

// #set heading(numbering: numbly("{1}.", default: "1.1"))

#title-slide()

= Outline <touying:hidden>

#outline(title: none, indent: 1em, depth: 1)

= Introduction
== Motivation
- Classical Prolog is ideal for explainable AI systems
- Extending with Fuzzy Logic allows for handling uncertainty and imprecision
- Personal interest in logic programming

== Prolog
#slide[
  - Declarative, query-based programming language
  - Unification and backtracking
][
  ```
  edge(a, b).
  edge(b, c).
  edge(c, d).
  edge(a, e).

  path(X, Y) :- edge(X, Y).
  path(X, Y) :- edge(X, Z), path(Z, Y).
  ```
]

== Mini-Prolog
- A simplified version of Prolog
- Focuses on core features
- Drastic reduction in complexity of implementation

= Architecture \& Design
- Uses Rust for performance, safety, and modern features
- Parser generates an Abstract Syntax Tree (AST) from Prolog code
- Translator converts AST to an intermediate representation
- Engine executes queries using backtracking and unification

== Fuzzy Logic Support
#slide[
  - Introduces degrees of truth
  - Uses new `:~` operator for fuzzy predicates
  - Required engine to be significantly modified to use a recursive approach
]

= Results

#focus-slide[
  Demonstrations
]

- Verified correctness with Prolog programs
- With fuzzy logic, can handle queries with degrees of truth
- Performance is traded-off for simplicity

= Conclusion
- Successfully implemented a Mini-Prolog interpreter in Rust
- Added support for fuzzy logic
- Future work: performance optimisations, full WAM implementation
