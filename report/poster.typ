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

#show raw: set block(fill: exeter-light.lighten(95%), inset: .5em, width: 90%, breakable: false)
#show raw: set text(size: 0.8em)

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

= Introduction
This project explores the implementation of a simple Prolog interpreter in Rust. This is then extended to incorporate fuzzy logic.

// Prolog can be used in a range of applications, including artificial intelligence, natural language processing, and theorem proving @bratko_prolog_1990.

== Motivation
- Improve my understanding of the language.
- Implement a simple, understandable Prolog interpreter.
- Explore the integration of fuzzy logic into Prolog.

== Aims
- Create Rust implementation of a Prolog interpreter.
- Support a subset of Prolog's features.
- Extend to support fuzzy logic.

#figure(
  caption: [A simple Prolog program.],
)[
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

#v(1fr)

= Implementation
== Crisp Prolog Engine
Prolog implementation based on the design given by Dewey and Hardekopf @dewey_mini:
- Parser that generates an abstract syntax tree (AST) from the user's program
- Translator that converts this user-facing AST into an internal representation
- Engine which executes queries using the internal representation

The engine maintains the following state:
- Environment stores variable bindings
- Equivalence relation allows for unification of values
- Stack of goals to be solved
- Stack of choice points to allow for backtracking

This is implemented in Rust, the first such implementation that I am aware of.

#v(1fr)

#figure(
  caption: [Parts of the Japanese subway use fuzzy control systems @jet0_sendai_2008.],
  placement: none,
  image("assets/sendai_subway.jpg", width: 90%),
)

#v(1fr)

#figure(
  caption: [Overview of the implementation design.],
  placement: top,
)[
  #cetz.canvas({
    import cetz.draw: *

    let size = 2.4

    circle((0, 0), radius: size, fill: exeter-light, stroke: none, name: "parser")
    content((0, 0), text(weight: "bold")[Parser])

    content(
      (rel: (8, 3), update: false),
      text(fill: black)[Input Program],
      frame: "rect",
      stroke: 2pt + exeter-light,
      padding: .5em,
      name: "input_program",
    )
    content(
      (rel: (8, 0.3), update: false),
      text(fill: black)[Query],
      frame: "rect",
      stroke: 2pt + exeter-light,
      padding: .5em,
      name: "query",
    )

    let p = (4, 1)

    line("input_program", p, "parser", mark: (end: ">"), stroke: 2pt)
    line("query", p, stroke: 2pt)

    circle((rel: (6, -6)), radius: size, fill: exeter-dark, stroke: none, name: "translator")
    content((rel: (0, 0)), text(fill: white, weight: "bold")[Translator])

    circle((rel: (-10, -5)), radius: size, fill: exeter-light, stroke: none, name: "engine")
    content((rel: (0, 0)), text(weight: "bold")[Engine])

    content(
      (rel: (8, -1), update: false),
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
      text(fill: black, size: .7em)[AST],
      frame: "rect",
      stroke: none,
      fill: white,
      padding: .2em,
    )
    line("translator", "engine", mark: (end: ">"), stroke: 2pt, name: "translator_to_engine")
    content(
      "translator_to_engine.mid",
      text(fill: black, size: .7em)[Internal \ Representation],
      frame: "rect",
      stroke: none,
      fill: white,
      padding: .2em,
    )
  })
]

#colbreak(weak: true)

== Fuzzy Prolog
The integration of fuzzy logic into a simple Prolog interpreter is a novel contribution.

The method I chose to implement fuzzy logic is as follows:
- Predicates return a degree of truth (float).
- Truth values can be values or expressions.
- Users define their own membership functions.
- Conjunction and disjunction are performed using minimum and maximum.
See @fig:fuzzy_prolog for an example of how fuzzy predicates are defined and used in my implementation.

#figure(
  caption: [A fuzzy Prolog program using my implementation.],
  placement: none,
)[
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
] <fig:fuzzy_prolog>

The main modifications I made to the implementation in order to support fuzzy logic were:
- Adding fuzzy predicate syntax to the parser.
- Backtracking to evaluate all branches in order to find the maximum truth value.
- Halting the exploration of a branch if the truth value goes below a threshold.

My implementation allows for standard Prolog alongside fuzzy predicates, and they can be used together in the same program.

#colbreak(weak: true)

= Results \& Achievements
A simple Prolog interpreter that supports fuzzy logic has not been implemented in Rust before, to the best of my knowledge.

I have:
- Implemented core features of Prolog in a simple Rust interpreter.
- Extended to support fuzzy logic with a natural syntax and semantics.
- Programs can be entirely crisp, entirely fuzzy, or a mixture of both.

My work has given me a deeper understanding of Prolog and fuzzy logic, and has provided a foundation for future work in this area.

#v(1fr)

= Future Work
- Allow for user-defined aggregation functions for combining truth values.
- Implement a full Prolog interpreter, for example the Warren Abstract Machine (WAM).
- Modify an existing Rust-based Prolog implementation to support fuzzy logic.

#v(1fr)

#figure(
  caption: [Example fuzzy sets for temperature.],
  placement: none,
)[
  #image("./assets/fuzzy_sets.png", width: 90%)
] <fig:sets>

#v(1fr)

// #figure(
//   caption: [Example usage of fuzzy logic.],
//   placement: auto,
// )[
//   #cetz.canvas({
//     import cetz.draw: *

//     let size = 2.5

//     circle((0, 0), radius: size, fill: exeter-dark, stroke: none, name: "controller")
//     content((0, 0), text(weight: "bold", fill: white)[Controller])

//     content(
//       (rel: (6, 5)),
//       text(fill: black)[Fuzzy 'Warm'],
//       frame: "rect",
//       stroke: 2pt + exeter-light,
//       padding: .5em,
//       name: "fuzzy_warm",
//     )
//     content(
//       (rel: (-6, 3)),
//       text(fill: black)[Crisp 'Occupied'],
//       frame: "rect",
//       stroke: 2pt + exeter-light,
//       padding: .5em,
//       name: "crisp_occupied",
//     )

//     let p = (1, 4)

//     line("fuzzy_warm", p, stroke: 2pt)
//     line("crisp_occupied", p, "controller", mark: (end: ">"), stroke: 2pt)

//     content(
//       (rel: (6, -2.3)),
//       text(fill: black)[Heating],
//       frame: "rect",
//       stroke: 2pt + exeter-light,
//       padding: .5em,
//       name: "heater_on",
//     )
//     line("controller", "heater_on", mark: (end: ">"), stroke: 2pt)
//   })
// ]

= Conclusions
- Standard Prolog programs and queries can be executed using the implemented engine.
- Fuzzy logic can be integrated into a Prolog interpreter in a natural way.
- This project has provided me with a deeper understanding of Prolog and Fuzzy logic.

#v(1fr)

#bibliography("refs.bib")

#v(1fr)
