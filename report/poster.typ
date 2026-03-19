#import "@preview/cetz:0.4.2"

#let exeter-light = rgb("#00C896")
#let exeter-dark = rgb("#003B3B")

#set page(columns: 3, paper: "a1", margin: 2.5cm)

#set text(size: 26pt, font: "Libertinus Sans")
#set par(leading: 0.5em, spacing: 1.35em, justify: true, linebreaks: "optimized")

#show heading: set text(fill: exeter-dark)
#show heading.where(level: 1): smallcaps
#show heading: set block(above: 1em, below: .5em)
#show heading: set align(center)

#show heading.where(level: 2): set text(size: 1em, fill: exeter-dark)
#show heading.where(level: 2): set align(left)

#set list(marker: text(fill: exeter-light, sym.bullet))
#set enum(numbering: "1.")

#show raw: set block(fill: exeter-light.lighten(95%), inset: .5em, width: 100%, breakable: false)
#show raw: set text(size: 0.9em)

#show figure.caption: set text(size: 0.9em, fill: exeter-dark)

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
        hyphenate: false,
      )[A Rust Implementation of Mini-Prolog \ including Fuzzy Logic Support]
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

Prolog can be used in a range of applications, including artificial intelligence, natural language processing, and theorem proving @bratko_prolog_1990.

== Motivation
- Prolog is a powerful language for certain problems but can be hard to understand.
- Implementing a Prolog interpreter would improve my understanding of the language.

== Aims
- Produce a Rust implementation of a Prolog interpreter.
- Support a subset of Prolog's features, including unification and backtracking.
- Extend the implementation to support fuzzy logic.


#figure(caption: [A Simple Prolog Program.])[
  ```
  parent(john, mary).
  parent(mary, susan).

  ancestor(X, Y) :-
    parent(X, Y).
  ancestor(X, Y) :-
    parent(X, Z),
    ancestor(Z, Y).
  ```
]

= Technical Background
The design of the implementation is based on that given by Dewey and Hardekopf @dewey_mini.

It has three main components:
- A parser that generates an abstract syntax tree (AST) from the user's program @aho_compilers_2002.
- A translator that converts this user-facing AST into an internal representation.
- The engine which executes queries using the internal representation.

#figure(
  caption: [Overview of the implementation design.],
  placement: auto,
)[
  #cetz.canvas({
    import cetz.draw: *

    let size = 2.5

    circle((0, 0), radius: size, fill: exeter-light, stroke: none, name: "parser")
    content((0, 0), text(weight: "bold")[Parser])

    content(
      (rel: (6, 4), update: false),
      text(fill: black)[Input Program],
      frame: "rect",
      stroke: 2pt + exeter-light,
      padding: .5em,
      name: "input_program",
    )
    content(
      (rel: (7, 1.3), update: false),
      text(fill: black)[Query],
      frame: "rect",
      stroke: 2pt + exeter-light,
      padding: .5em,
      name: "query",
    )

    let p = (3, 2)

    line("input_program", p, "parser", mark: (end: ">"), stroke: 2pt)
    line("query", p, stroke: 2pt)

    circle((rel: (6, -8)), radius: size, fill: exeter-dark, stroke: none, name: "translator")
    content((rel: (0, 0)), text(fill: white, weight: "bold")[Translator])

    circle((rel: (-7, -7)), radius: size, fill: exeter-light, stroke: none, name: "engine")
    content((rel: (0, 0)), text(weight: "bold")[Engine])

    content(
      (rel: (7, 1), update: false),
      text(fill: black)[Solutions],
      frame: "rect",
      stroke: 2pt + exeter-light,
      padding: .5em,
      name: "solution",
    )

    line("engine", "solution", mark: (end: ">"), stroke: 2pt)

    line("parser", "translator", mark: (end: ">"), stroke: 2pt, name: "parser_to_translator")
    content(
      "parser_to_translator.mid",
      text(fill: black, size: .7em)[Abstract Syntax Tree],
      frame: "rect",
      stroke: none,
      fill: white,
      padding: .2em,
    )
    line("translator", "engine", mark: (end: ">"), stroke: 2pt, name: "translator_to_engine")
    content(
      "translator_to_engine.mid",
      text(fill: black, size: .7em)[Internal Representation],
      frame: "rect",
      stroke: none,
      fill: white,
      padding: .2em,
    )
  })
]

Fuzzy logic allows for reasoning about imprecise or uncertain information @zadeh_fuzzy_1988:
- Fuzzy sets define a membership function $mu : X -> [0, 1]$ that assigns a degree of membership to each element in the set.
- Allows for imprecise concepts such as 'hot' and 'cold' to be represented and reasoned about.
- Conjunction and disjunction are respectively performed using the minimum and maximum of the truth values.

#figure(
  caption: [Example fuzzy sets for temperature.],
  placement: auto,
)[
  #image("./assets/fuzzy_sets.png", width: 80%)
] <fig:sets>

= Implementation
== Engine
At the core of the execution of Prolog queries is the engine.

- Environment stores variable bindings.
- Equivalence relation allows for unification of values.
- Stack of goals to be solved.
- Stack of choice points to allow for backtracking.

// Uses the above components to execute the algorithm for solving a query:
// + If the goal stack is empty:
//   + Halt if the environent is also empty.
//   + Otherwise, record the current solution and backtrack.
// + Otherwise, attempt to handle the current goal:
//   + Conjunctions and disjunctions are handled by pushing the appropriate goals onto the stack.
//   + Constraint goals are evaluated to fuzzy truth values which are pushed to the goal stack.
//   + If the goal is a truth value, update the current query's truth value and backtrack if it is below the 'true' threshold.

// #figure(
//   caption: [Overview of the engine.],
//   placement: auto,
// )[
//   #cetz.canvas({
//     import cetz.draw: *

//     let size = 2.5

//     // Goal stack (stack of rects)
//     rect(
//       (rel: (0, -1.2)),
//       (rel: (6, 1.2), update: false),
//       stroke: 2pt + exeter-dark,
//       name: "goal_top",
//     )
//     content((rel: (3, 0.6), update: false), text(fill: exeter-dark)[$"current goal"$])

//     rect(
//       (rel: (0, -1.2)),
//       (rel: (6, 1.2), update: false),
//       stroke: 2pt + exeter-dark,
//     )
//     content((rel: (3, 0.6), update: false), text(fill: exeter-dark)[$dots.v$])

//     rect(
//       (rel: (0, -1.2)),
//       (rel: (6, 1.2), update: false),
//       stroke: 2pt + exeter-dark,
//     )
//     content((rel: (3, 0.6), update: false), text(fill: exeter-dark)[$"query goal"$])

//     content((rel: (3, -.7), update: false), text(fill: exeter-dark)[Goal Stack])

//     content((3, 2), [Engine], frame: "rect", stroke: 2pt + exeter-light, padding: .5em, name: "engine")

//     rect(
//       (rel: (5, -.7)),
//       (rel: (6, 1.2), update: false),
//       stroke: 2pt + exeter-dark,
//       name: "choice_top",
//     )
//     content((rel: (3, 0.6), update: false), text(fill: exeter-dark)[$"choice point"$])

//     rect(
//       (rel: (0, -1.2)),
//       (rel: (6, 1.2), update: false),
//       stroke: 2pt + exeter-dark,
//     )
//     content((rel: (3, 0.6), update: false), text(fill: exeter-dark)[$dots.v$])

//     line("goal_top", "engine", mark: (end: ">", start: ">"), stroke: 2pt)
//     line("choice_top", "engine", mark: (end: ">", start: ">"), stroke: 2pt)
//   })
// ]

== Fuzzy Logic
The integration of fuzzy logic into a simple Prolog interpreter is a novel contribution.

- Predicates return a degree of truth rather than a boolean.
- Users can define their own membership functions, for example 'trapezoidal'.
- Truth values can be expressions that are evaluated using arguments of the predicate.
- Conjunction and disjunction are performed using the minimum and maximum of the truth values respectively.
- Truth values below a certain threshold are treated as false.

#figure(
  caption: [Example usage of fuzzy logic.],
  placement: auto,
)[
  #cetz.canvas({
    import cetz.draw: *

    let size = 2.5

    circle((0, 0), radius: size, fill: exeter-dark, stroke: none, name: "controller")
    content((0, 0), text(weight: "bold", fill: white)[Controller])

    content(
      (rel: (6, 5)),
      text(fill: black)[Fuzzy 'Warm'],
      frame: "rect",
      stroke: 2pt + exeter-light,
      padding: .5em,
      name: "fuzzy_warm",
    )
    content(
      (rel: (-6, 3)),
      text(fill: black)[Crisp 'Occupied'],
      frame: "rect",
      stroke: 2pt + exeter-light,
      padding: .5em,
      name: "crisp_occupied",
    )

    let p = (1, 4)

    line("fuzzy_warm", p, stroke: 2pt)
    line("crisp_occupied", p, "controller", mark: (end: ">"), stroke: 2pt)

    content(
      (rel: (6, -2.3)),
      text(fill: black)[Heating],
      frame: "rect",
      stroke: 2pt + exeter-light,
      padding: .5em,
      name: "heater_on",
    )
    line("controller", "heater_on", mark: (end: ">"), stroke: 2pt)
  })
]

#figure(caption: [Definition of Trapezoidal Membership Functions.], placement: auto)[
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

  warm(X) :~
    trapezoidal(X, 15, 20, 25, 30).
  ```
]

= Results
The implementation of Mini-Prolog was successful and supports the core features of Prolog.

The extension to support fuzzy logic was also successful. Fuzzy predicates are intuitive to define and use, and the engine correctly evaluates truth values according to the defined semantics.

== Future Work
- Allow for user-defined aggregation functions for combining truth values.
- Implement a full Prolog interpreter, for example the Warren Abstract Machine (WAM).
- Modify an existing Rust-based Prolog implementation to support fuzzy logic.

= Conclusion
- Standard Prolog programs and queries can be executed using the implemented engine.
- Fuzzy logic can be integrated into a Prolog interpreter in a natural way, allowing for reasoning about imprecise information.
- This project has provided me with a deeper understanding of Prolog and Fuzzy logic.

#bibliography("refs.bib")
