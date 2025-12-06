use mimir::parser::*;

#[test]
fn test_atom_basic() {
    let (remaining, parsed) = atom("t").unwrap();
    assert_eq!(parsed, ast::Term::atom("t"));
    assert_eq!(remaining, "");

    let (remaining, parsed) = atom("text").unwrap();
    assert_eq!(parsed, ast::Term::atom("text"));
    assert_eq!(remaining, "");

    let (remaining, parsed) = atom("tExt").unwrap();
    assert_eq!(parsed, ast::Term::atom("tExt"));
    assert_eq!(remaining, "");
}

#[test]
fn test_atom_with_suffix() {
    let (remaining, parsed) = atom("text ").unwrap();
    assert_eq!(parsed, ast::Term::atom("text"));
    assert_eq!(remaining, " ");

    let (remaining, parsed) = atom("text.").unwrap();
    assert_eq!(parsed, ast::Term::atom("text"));
    assert_eq!(remaining, ".");
}

#[test]
fn test_atom_fails_uppercase() {
    let parsed = atom("X");
    assert!(parsed.is_err())
}

#[test]
fn test_quoted_atom() {
    let (remaining, parsed) = quoted_atom("\"text text\"").unwrap();
    assert_eq!(parsed, ast::Term::atom("text text"));
    assert_eq!(remaining, "");
}

#[test]
fn test_quoted_atom_with_suffix() {
    let (remaining, parsed) = quoted_atom("\"text text\".").unwrap();
    assert_eq!(parsed, ast::Term::atom("text text"));
    assert_eq!(remaining, ".");
}

#[test]
fn test_quoted_atom_fails() {
    let parsed = quoted_atom("\" \"");
    assert!(parsed.is_err());

    let parsed = quoted_atom("\"text \"");
    assert!(parsed.is_err());

    let parsed = quoted_atom("\" text\"");
    assert!(parsed.is_err());
}

#[test]
fn test_number_basic() {
    let (remaining, parsed) = number("1234567890").unwrap();
    assert_eq!(parsed, ast::Term::number(1234567890));
    assert_eq!(remaining, "");

    let (remaining, parsed) = number("1_234_567_890").unwrap();
    assert_eq!(parsed, ast::Term::number(1234567890));
    assert_eq!(remaining, "");
}

#[test]
fn test_number_with_suffix() {
    let (remaining, parsed) = number("10.").unwrap();
    assert_eq!(parsed, ast::Term::number(10));
    assert_eq!(remaining, ".");

    let (remaining, parsed) = number("10 ").unwrap();
    assert_eq!(parsed, ast::Term::number(10));
    assert_eq!(remaining, " ");
}

#[test]
fn test_number_negative() {
    let (remaining, parsed) = number("-10").unwrap();
    assert_eq!(parsed, ast::Term::number(-10));
    assert_eq!(remaining, "");

    let parsed = number("-a");
    assert!(parsed.is_err());
}

#[test]
fn test_number_fails() {
    let parsed = number("text");
    assert!(parsed.is_err());

    let parsed = number("a10");
    assert!(parsed.is_err());

    let parsed = number("1_");
    assert!(parsed.is_err());

    let parsed = number("_1");
    assert!(parsed.is_err());

    let parsed = number("___");
    assert!(parsed.is_err());
}

#[test]
fn test_variable_basic() {
    let (remaining, parsed) = variable("T").unwrap();
    assert_eq!(parsed, ast::Term::var("T"));
    assert_eq!(remaining, "");

    let (remaining, parsed) = variable("Text").unwrap();
    assert_eq!(parsed, ast::Term::var("Text"));
    assert_eq!(remaining, "");

    let (remaining, parsed) = variable("TeXt").unwrap();
    assert_eq!(parsed, ast::Term::var("TeXt"));
    assert_eq!(remaining, "");

    let (remaining, parsed) = variable("_text").unwrap();
    assert_eq!(parsed, ast::Term::var("_text"));
    assert_eq!(remaining, "");
}

#[test]
fn test_variable_with_suffix() {
    let (remaining, parsed) = variable("Text ").unwrap();
    assert_eq!(parsed, ast::Term::var("Text"));
    assert_eq!(remaining, " ");

    let (remaining, parsed) = variable("Text.").unwrap();
    assert_eq!(parsed, ast::Term::var("Text"));
    assert_eq!(remaining, ".");
}

#[test]
fn test_variable_fails_lowercase() {
    let parsed = variable("t");
    assert!(parsed.is_err())
}

#[test]
fn test_compound_basic() {
    let (remaining, parsed) = compound("f(a, b, c)").unwrap();
    assert_eq!(
        parsed,
        ast::Term::compound(
            "f",
            vec![
                ast::Term::atom("a"),
                ast::Term::atom("b"),
                ast::Term::atom("c")
            ]
        )
    );
    assert_eq!(remaining, "");

    let (remaining, parsed) = compound("f  (a,b ,  c)").unwrap();
    assert_eq!(
        parsed,
        ast::Term::compound(
            "f",
            vec![
                ast::Term::atom("a"),
                ast::Term::atom("b"),
                ast::Term::atom("c")
            ]
        )
    );
    assert_eq!(remaining, "");

    let (remaining, parsed) = compound("f(a, X, c)").unwrap();
    assert_eq!(
        parsed,
        ast::Term::compound(
            "f",
            vec![
                ast::Term::atom("a"),
                ast::Term::var("X"),
                ast::Term::atom("c")
            ]
        )
    );
    assert_eq!(remaining, "");
}

#[test]
fn test_compound_nested() {
    let (remaining, parsed) = compound("f(a, g(n, m), c)").unwrap();
    assert_eq!(
        parsed,
        ast::Term::compound(
            "f",
            vec![
                ast::Term::atom("a"),
                ast::Term::compound("g", vec![ast::Term::atom("n"), ast::Term::atom("m"),]),
                ast::Term::atom("c")
            ]
        )
    );
    assert_eq!(remaining, "");
}

#[test]
fn test_term() {
    let (remaining, parsed) = term("atom").unwrap();
    assert_eq!(parsed, ast::Term::atom("atom"));
    assert_eq!(remaining, "");

    let (remaining, parsed) = term("Var").unwrap();
    assert_eq!(parsed, ast::Term::var("Var"));
    assert_eq!(remaining, "");

    let (remaining, parsed) = term("123").unwrap();
    assert_eq!(parsed, ast::Term::number(123));
    assert_eq!(remaining, "");

    let (remaining, parsed) = term("f(a, b)").unwrap();
    assert_eq!(
        parsed,
        ast::Term::compound("f", vec![ast::Term::atom("a"), ast::Term::atom("b")])
    );
    assert_eq!(remaining, "");
}

#[test]
fn test_clause() {
    let input = "parent(X, Y) :- father(X, Y), mother(X, Y).";
    let expected = ast::Clause::rule(
        ast::Term::compound("parent", vec![ast::Term::var("X"), ast::Term::var("Y")]),
        vec![
            ast::Term::compound("father", vec![ast::Term::var("X"), ast::Term::var("Y")]),
            ast::Term::compound("mother", vec![ast::Term::var("X"), ast::Term::var("Y")]),
        ],
    );

    let (remaining, parsed) = clause(input).unwrap();
    assert_eq!(parsed, expected);
    assert_eq!(remaining, "");

    let input = "parent(X, Y)  :-  \n father(X, Y) \t,  mother(X, Y) . ";
    let (remaining, parsed) = clause(input).unwrap();
    assert_eq!(parsed, expected);
    assert_eq!(remaining, "");
}

#[test]
fn test_fact() {
    let input = "father(john, mary).";
    let expected = ast::Clause::fact(ast::Term::compound(
        "father",
        vec![ast::Term::atom("john"), ast::Term::atom("mary")],
    ));

    let (remaining, parsed) = fact(input).unwrap();
    assert_eq!(parsed, expected);
    assert_eq!(remaining, "");
}

#[test]
fn test_rhs_terms() {
    let (remaining, parsed) = rhs_term("X \\= Y").unwrap();
    assert_eq!(
        parsed,
        ast::Term::compound(
            "not_equal",
            vec![ast::Term::var("X"), ast::Term::var("Y")]
        )
    );
    assert_eq!(remaining, "");

    let (remaining, parsed) = rhs_term("A = B").unwrap();
    assert_eq!(
        parsed,
        ast::Term::compound("equal", vec![ast::Term::var("A"), ast::Term::var("B")])
    );
    assert_eq!(remaining, "");

    let (remaining, parsed) = rhs_term("X =< Y").unwrap();
    assert_eq!(
        parsed,
        ast::Term::compound(
            "less_than_equal",
            vec![ast::Term::var("X"), ast::Term::var("Y")]
        )
    );
    assert_eq!(remaining, "");
}

#[test]
fn test_nested_rhs_terms() {
    let (remaining, parsed) = rhs_term("A = B + C").unwrap();
    assert_eq!(
        parsed,
        ast::Term::compound(
            "equal",
            vec![
                ast::Term::var("A"),
                ast::Term::compound(
                    "add",
                    vec![ast::Term::var("B"), ast::Term::var("C")]
                )
            ]
        )
    );
    assert_eq!(remaining, "");
}

#[test]
fn test_clause_with_rhs_terms() {
    let input = "sibling(X, Y) :- parent(Z, X), parent(Z, Y), X \\= Y.";
    let expected = ast::Clause::rule(
        ast::Term::compound("sibling", vec![ast::Term::var("X"), ast::Term::var("Y")]),
        vec![
            ast::Term::compound("parent", vec![ast::Term::var("Z"), ast::Term::var("X")]),
            ast::Term::compound("parent", vec![ast::Term::var("Z"), ast::Term::var("Y")]),
            ast::Term::compound(
                "not_equal",
                vec![ast::Term::var("X"), ast::Term::var("Y")],
            ),
        ],
    );

    let (remaining, parsed) = clause(input).unwrap();
    assert_eq!(parsed, expected);
    assert_eq!(remaining, "");
}

#[test]
fn test_list() {
    let (remaining, parsed) = list("[a, b, c]").unwrap();
    assert_eq!(
        parsed,
        ast::Term::compound(
            "cons",
            vec![
                ast::Term::atom("a"),
                ast::Term::compound(
                    "cons",
                    vec![
                        ast::Term::atom("b"),
                        ast::Term::compound("cons", vec![ast::Term::atom("c"), ast::Term::atom("nil")])
                    ]
                )
            ]
        )
    );
    assert_eq!(remaining, "");

    let (remaining, parsed) = list("[X, Y | Z]").unwrap();
    assert_eq!(
        parsed,
        ast::Term::compound(
            "cons",
            vec![
                ast::Term::var("X"),
                ast::Term::compound(
                    "cons",
                    vec![ast::Term::var("Y"),
                    ast::Term::compound("cons", vec![ast::Term::var("Z"), ast::Term::atom("nil")])

                    ]
                )
            ]
        )
    );
    assert_eq!(remaining, "");

    let (remaining, parsed) = list("[X, Y | [a, b]]").unwrap();
    assert_eq!(
        parsed,
        ast::Term::compound(
            "cons",
            vec![
                ast::Term::var("X"),
                ast::Term::compound(
                    "cons",
                    vec![
                        ast::Term::var("Y"),
                        ast::Term::compound(
                            "cons",
                            vec![ast::Term::atom("a"), ast::Term::compound("cons", vec![ast::Term::atom("b"), ast::Term::atom("nil")])]
                        )
                    ]
                )
            ]
        )
    );
    assert_eq!(remaining, "");
}

#[test]
fn test_files() {
    // Get path to tests/prolog_files
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR")
        .expect("CARGO_MANIFEST_DIR should be set by Cargo");
    let test_dir = std::path::Path::new(&manifest_dir).join("tests\\prolog_files");

    let paths = std::fs::read_dir(&test_dir).unwrap();

    for path in paths {
        let path = path.unwrap().path();

        // Only attempt .pl files
        if path.extension().and_then(|s| s.to_str()) == Some("pl") {
            // Get contents and attempt to parse
            let content = std::fs::read_to_string(&path).unwrap();
            let res = program(&content);

            assert!(
                res.is_ok(),
                "Failed to parse file {:?}: {:?}",
                path,
                res.err()
            );

            // Check that the entire input was consumed
            let (remaining, _) = res.unwrap();

            assert!(
                remaining.trim().is_empty(),
                "Did not consume entire input for file {:?}.\n\nRemaining:\n{:?}\n",
                path,
                remaining
            );

            println!("\nSuccessfully parsed file {:?}\n---", path);
            for clause in program(&content).unwrap().1 {
                println!("{}", clause);
            }
            println!("---");
        }
    }
}
