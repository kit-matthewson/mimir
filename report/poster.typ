#import "@preview/cetz:0.4.2"

#let exeter-light = rgb("#00C896")
#let exeter-dark = rgb("#003B3B")

#set page(columns: 3, paper: "a1", margin: 2.5cm)

#set text(size: 24pt, font: "Libertinus Sans")
#set par(leading: 0.5em, spacing: 1.35em, justify: true)

#show heading: set text(fill: exeter-dark)
#show heading.where(level: 1): smallcaps
#show heading: set block(above: 1em, below: .5em)
#show heading: set align(center)

#show heading.where(level: 2): set text(size: 1em, fill: exeter-dark)
#show heading.where(level: 2): set align(left)

#set list(marker: text(fill: exeter-light, sym.bullet))

#show raw: set block(fill: exeter-light.lighten(95%), inset: .5em, width: 100%)
#show raw: set text(size: 0.9em)
#place(
  top + center,
  float: true,
  scope: "parent",
  clearance: 2em,
)[
  #block(
    fill: exeter-dark,
    width: 100%,
    inset: 2em,
    // stroke: 10pt + exeter-light,
  )[
    #block(width: 75%)[
      #text(
        size: 1.7em,
        fill: white,
        weight: "bold",
      )[A Rust Implementation of Mini-Prolog including Fuzzy Logic Support]
      #v(-1em)
      #text(size: 1em, fill: exeter-dark.lighten(80%), weight: "bold")[Kit Matthewson]
    ]
  ]
]

// - Font size #sym.checkmark
// - Go into detail on engine implementation
// - How will fuzzy logic be implemented in the engine
// - Try to link to demo
// - Emphasise originality, use keywords: 'original', 'new contribution'
// - More bullets, less text

= Introduction
// Prolog is a logic programming language that allows the programmer to declare facts and rules, and then ask queries about them.

// Rust is a modern systems programming language with emphasis on safety and performance.

// Fuzzy logic is a form of many-valued logic that allows for reasoning about imprecise or uncertain information.
This project explores the implementation of a simple Prolog interpreter in Rust. This is then extended to incorporate fuzzy logic.

== Motivation
- Prolog is a powerful language for certain problems but can be hard to understand.
- Implementing a Prolog interpreter would improve my understanding of the language.

== Aims
- Produce a Rust implementation of a Prolog interpreter.
- Support a subset of Prolog's features, including unification and backtracking.
- Extend the implementation to support fuzzy logic.

= Technical Background
The design of the implementation is based on that given by Dewey and Hardekopf @dewey_mini.

It has three main components:
- A parser that generates an abstract syntax tree (AST) from the user's program.
- A translator that converts this user-facing AST into an internal representation.
- The engine which executes queries using the internal representation.

#figure(
  caption: "Overview of the implementation design.",
  placement: auto,
)[
  #image("./assets/diagram.png", width: 75%)
]

== Fuzzy Logic
// Fuzzy logic is implemented using fuzzy sets, which use a membership function to assign a degree of membership to each element in the set. This allows for reasoning about imprecise concepts such as 'hot' and 'cold' @zadeh_fuzzy_1988.

- Fuzzy sets define a membership function $mu : X -> [0, 1]$ that assigns a degree of membership to each element in the set.
- Allows for imprecise concepts such as 'hot' and 'cold' to be represented and reasoned about.
- Conjunction and disjunction are respectively performed using the minimum and maximum of the truth values.

#figure(
  caption: "Example fuzzy sets for temperature.",
  placement: auto,
)[
  #image("./assets/fuzzy-sets.png", width: 90%)
]

To incorporate this into Prolog, predicates are extended to return a degree of truth rather than a boolean. These would use predefined membership functions like 'trapezoidal'.

#block(breakable: false)[
  A simple example of a fuzzy Prolog program is:
  ```
  warm(T) :~ trapezoidal(T, 20, 25, 30, 35).
  lights_on(L) :- L = on.

  comfortable(T, L) :- warm(T), lights_on(L).
  ```
]

// = Core Principles
// == Unification
// In Prolog, unification is the process of making two terms equal by finding a suitable substitution for variables. This is the key algorithm that allows Prolog to match queries against facts and rules.

// The substitution required to unify two terms $X$ and $Y$ can be defined as:
// $
//   "unify"(X, Y) = wide cases(
//     {} & "if" X = Y,
//     {p |-> Y} & "if" X = p,
//     {p |-> X} & "if" Y = p,

//     italic("fail") & "otherwise"
//   )
// $
// For the unification of compounds, $f(X_1, ..., X_n) = g(Y_1, ..., Y_m)$, we check that $f = g$ and $n = m$ and then attempt to unify each pair of corresponding arguments $X_i$ and $Y_i$.

// == Backtracking
// If two terms cannot be unified the execution engine backtracks to the last decision point. Using a goal stack which also contains choice points allows this to be implemented simply and efficiently.

// ```
// pseudocode for backtracking
// ```

= Implementation
== Engine
- Environment stores variable bindings.
- Equivalence relation allows for unification of variables.
- Stack of goals to be solved.
- Stack of choice points to allow for backtracking.

== Fuzzy Logic
The integration of fuzzy logic into a simple Prolog interpreter is a novel contribution.

= Results
The implementation of Mini-Prolog was successful and supports the core features of Prolog.

== Future Work
- Implement a full Prolog interpreter, for example the Warren Abstract Machine (WAM).
- Modify an existing Prolog implementation to support fuzzy logic.

= Conclusion
This project has provided a deeper understanding of Prolog and its implementation.

#bibliography("refs.bib")
