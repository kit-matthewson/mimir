#import "@preview/cetz:0.4.2"

#let exeter-light = rgb("#00c896")
#let exeter-dark = rgb("#003b3b")

#set page(columns: 3, paper: "a1", margin: 3cm)

#set text(size: 23pt, font: "Libertinus Sans")
#set par(leading: 0.5em, spacing: 1.35em, justify: true, linebreaks: "optimized")

#show heading: set text(fill: exeter-dark)
#show heading.where(level: 1): smallcaps
#show heading.where(level: 1): set align(center)
#show heading.where(level: 1): set block(above: 1.7em, below: .5em)

#show heading.where(level: 2): set text(size: 1em, fill: exeter-dark)
#show heading.where(level: 2): set block(above: 1.2em, below: .5em)
#show heading.where(level: 2): set align(left)

#set list(marker: text(fill: exeter-light, sym.bullet))
#set enum(numbering: "1.")

#show raw: set block(fill: exeter-light.lighten(95%), inset: 1em, width: 90%, breakable: false, radius: 5pt)
#show raw: set text(size: 0.9em)

#show figure.caption: set text(size: 0.9em, fill: exeter-dark)

#place(
  top + center,
  float: true,
  scope: "parent",
  clearance: 3cm,
)[
  #block(
    fill: exeter-dark,
    width: 200%,
    inset: 2em,
    stroke: 10pt + exeter-light,
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

Prolog is used in a range of applications including artificial intelligence and natural language processing @bratko_prolog_1990.

== Motivation
- Improve my understanding of Prolog
// - Powerful language for logic programming @bratko_prolog_1990
- Implement a simple, understandable Prolog interpreter
- Explore the integration of fuzzy logic into Prolog

== Aims
- Create Rust implementation of a Prolog interpreter.
- Support a subset of Prolog's features.
- Extend to support fuzzy logic.

#figure(
  caption: [A simple Prolog program @clocksin_programming_2003.],
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

// #v(1fr)

= Implementation
== Core Prolog Engine
Prolog implementation based on the design given by Dewey and Hardekopf @dewey_mini:
- Parser that generates an abstract syntax tree (AST) from the user's program @aho_compilers_2002
- Translator that converts this user-facing AST into an internal representation
- Engine which executes queries using the internal representation

The engine maintains the following state:
- Environment stores variable bindings
- Equivalence relation allows for unification of values
- Stack of goals to be solved
- Stack of choice points to allow for backtracking

This is implemented in Rust, the first such implementation that I am aware of.

// #v(1fr)

#figure(
  caption: [Parts of the Japanese subway use fuzzy control systems @jet0_sendai_2008.],
  placement: none,
  image("assets/sendai_subway.jpg", width: 90%),
)

// #v(1fr)

// #colbreak(weak: true)

#figure(
  caption: [Overview of the implementation design.],
  placement: top,
  gap: 32pt,
)[
  #cetz.canvas({
    import cetz.draw: *

    let size = 2.4

    circle((0, 0), radius: size, fill: exeter-light, stroke: none, name: "parser")
    content((0, 0), text(weight: "bold")[Parser])

    content(
      (rel: (9, 3), update: false),
      text(fill: black)[Input Program],
      frame: "rect",
      stroke: 2pt + exeter-dark,
      padding: .5em,
      name: "input_program",
    )
    content(
      (rel: (7.5, 1), update: false),
      text(fill: black)[Query],
      frame: "rect",
      stroke: 2pt + exeter-dark,
      padding: .5em,
      name: "query",
    )

    line("input_program", (rel: (-5, 0)), (rel: (0, -3)), "parser", mark: (end: ")>"), stroke: 2pt)
    line("query", (rel: (-3.5, 0)), stroke: 2pt)

    circle((rel: (6, -6)), radius: size, fill: exeter-dark, stroke: none, name: "translator")
    content((rel: (0, 0)), text(fill: white, weight: "bold")[Translator])

    circle((rel: (-10, -5)), radius: size, fill: exeter-light, stroke: none, name: "engine")
    content((rel: (0, 0)), text(weight: "bold")[Engine])

    content(
      (rel: (8, -1), update: false),
      text(fill: black)[Solutions],
      frame: "rect",
      stroke: 2pt + exeter-dark,
      padding: .5em,
      name: "solution",
    )

    line("engine", "solution", mark: (end: ")>"), stroke: 2pt)

    line("parser", "translator", mark: (end: ")>"), stroke: 2pt, name: "parser_to_translator")
    content(
      "parser_to_translator.mid",
      text(fill: black, size: .7em)[AST],
      frame: "rect",
      stroke: none,
      fill: white,
      padding: .2em,
    )
    line("translator", "engine", mark: (end: ")>"), stroke: 2pt, name: "translator_to_engine")
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

== Fuzzy Prolog Extension
The integration of fuzzy logic into a simple Prolog interpreter is a novel contribution.

@fig:fuzzy_prolog shows how fuzzy predicates are defined and used in my implementation.

#block(breakable: false)[
  The method I chose to implement fuzzy logic is as follows:
  - Predicates return a degree of truth (float).
  - Truth values can be values or expressions.
  - Users define their own membership functions.
  - Conjunction and disjunction are performed using minimum and maximum.
]

// #v(1fr)

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

I made the following modifications to the Prolog engine in order to support fuzzy logic:
- Adding fuzzy predicate syntax to the parser.
- Backtracking to evaluate all branches in order to find the maximum truth value.
- Halting the exploration of a branch if the truth value goes below a threshold.

My implementation allows for standard Prolog alongside fuzzy predicates, and they can be used together in the same program.

#v(2fr)

#figure(
  caption: [Example fuzzy sets for temperature.],
  placement: none,
)[
  #cetz.canvas({
    import cetz.draw: *

    let axes-stroke = 2pt + black
    let set-stroke = 4pt

    let height = 6
    let width = 13
    let top = height - 1

    // Sets
    let cold = (
      (0, top),
      (0.2 * width, top),
      (0.4 * width, 0),
    )

    line(..cold, stroke: set-stroke + exeter-dark, name: "cold")
    content((0.1 * width, top + .5), text(fill: exeter-dark, size: .7em)[cold])

    let warm = (
      (0.2 * width, 0),
      (0.4 * width, top),
      (0.6 * width, top),
      (0.8 * width, 0),
    )

    line(..warm, stroke: set-stroke + exeter-light, name: "warm")
    content((0.5 * width, top + .5), text(fill: exeter-light, size: .7em)[warm])

    let hot = (
      (0.6 * width, 0),
      (0.8 * width, top),
      (width, top),
    )

    line(..hot, stroke: set-stroke + exeter-dark, name: "hot")
    content((0.9 * width, top + .5), text(fill: exeter-dark, size: .7em)[hot])

    // Axes
    line((-.1, 0), (width, 0), stroke: axes-stroke, mark: (end: ")>"))
    line((0, 0), (0, height), stroke: axes-stroke, mark: (end: ")>"))
    content((width / 2, -.7), text(fill: black, size: .8em)[Temperature])
    content((-.5, 0), text(fill: black)[0])
    line((-.1, top), (0, top), stroke: axes-stroke)
    content((-.5, top), text(fill: black)[1])
  })
] <fig:sets>

#v(1fr)

= Results \& Achievements
A simple Prolog interpreter that supports fuzzy logic has not been implemented in Rust before, to the best of my knowledge.

I have:
- Implemented the core features of Prolog in a simple Rust interpreter.
- Extended Prolog to support fuzzy logic with a natural syntax and semantics.
- Programs can be entirely crisp, entirely fuzzy, or a mixture of both.

The implementation allows for the creation of a fuzzy inference engine entirely within Prolog.

#figure(
  caption: [Elements of a fuzzy inference engine.],
  placement: none,
  gap: 32pt,
)[
  #cetz.canvas({
    import cetz.draw: *

    let size = 2.5

    // Temperature Sensor
    content(
      (1.5, 0),
      text(fill: black)[Sensors],
      frame: "rect",
      stroke: 2pt + exeter-dark,
      padding: .5em,
      name: "temperature_sensor",
    )

    // Occupancy Sensor
    content(
      (7.5, 0),
      text(fill: black)[Fuzzy Sets],
      frame: "rect",
      stroke: 2pt + exeter-dark,
      padding: .5em,
      name: "occupancy_sensor",
    )

    // Fuzzification
    content(
      (6, -4),
      text(fill: black)[Fuzzification],
      frame: "rect",
      stroke: 2pt + exeter-light,
      padding: .5em,
      name: "fuzzification",
    )

    line("temperature_sensor", (rel: (0, -1.5)), (rel: (4.5, 0)), "fuzzification", mark: (end: ")>"), stroke: 2pt)
    line("occupancy_sensor", (rel: (0, -1.5)), (rel: (-3, 0)), stroke: 2pt)

    // Inference Engine
    circle((4.5, -9), radius: size, fill: exeter-light, stroke: none, name: "engine")
    let x = 0.2 * size
    content((rel: (0, x), update: false), text(weight: "bold")[Inference])
    content((rel: (0, -x), update: false), text(weight: "bold")[Engine])

    // Rules
    content(
      (0, -4),
      text(fill: black)[Fuzzy Rules],
      frame: "rect",
      stroke: 2pt + exeter-light,
      padding: .5em,
      name: "rules",
    )

    line("fuzzification", (rel: (0, -1.5)), "engine", mark: (end: ")>"), stroke: 2pt)
    line("rules", (rel: (0, -5)), "engine", mark: (end: ")>"), stroke: 2pt)

    // Defuzzification
    content(
      (4.5, -14),
      text(fill: black)[Defuzzification],
      frame: "rect",
      stroke: 2pt + exeter-light,
      padding: .5em,
      name: "defuzzification",
    )

    line("engine", "defuzzification", mark: (end: ")>"), stroke: 2pt)

    // Output
    content(
      (4.5, -17),
      text(fill: black)[Output],
      frame: "rect",
      stroke: 2pt + exeter-dark,
      padding: .5em,
      name: "output",
    )

    line("defuzzification", "output", mark: (end: ")>"), stroke: 2pt)
  })
]

= Future Work
- Allow for user-defined aggregation functions for combining truth values.
- Implement a full Prolog interpreter, for example the Warren Abstract Machine (WAM) @ait-kaci_warrens_1991.
- Modify an existing Rust-based Prolog implementation to support fuzzy logic.

= Conclusions
- Standard Prolog programs and queries can be executed using the implemented engine.
- Fuzzy logic can be integrated into a Prolog interpreter in a natural way.
- This project has provided me with a deeper understanding of Prolog and Fuzzy logic.

= Bibliography
#set text(size: 0.7em)
#bibliography("refs.bib", title: none)
