//! Parser for Mini-Prolog.
//!
//! Contains the AST definitions and parsing functions.

mod ast;

pub use ast::*;

use nom::{
    IResult, Parser,
    branch::*,
    bytes::complete::*,
    character::complete::*,
    combinator::*,
    error::{Error, ParseError},
    multi::*,
    sequence::*,
};

/// Valid characters for the start of an atom.
const ATOM_START_CHARS: &str = "abcdefghijklmnopqrstuvwxyz";
/// Valid characters for the start of a variable.
const VAR_START_CHARS: &str = "ABCDEFGHIJKLMNOPQRSTUVWXYZ_";
/// Valid characters for the rest of an atom or variable.
const ALPHANUMERIC_CHARS: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ01234567890";

/// Takes a parser and produces a new parser that also consumes leading and tracing whitespace.
///
/// This implementation is based on the `ws` combinator from the nom documentation.
pub fn ws<'a, O, E: nom::error::ParseError<&'a str>, F>(
    inner: F,
) -> impl Parser<&'a str, Output = O, Error = E>
where
    F: Parser<&'a str, Output = O, Error = E>,
{
    delimited(multispace0, inner, multispace0)
}

/// Takes a parser and produces a new parser that also consumes a non-zero amount of leading and trailing whitespace.
pub fn ws1<'a, O, E: nom::error::ParseError<&'a str>, F>(
    inner: F,
) -> impl Parser<&'a str, Output = O, Error = E>
where
    F: Parser<&'a str, Output = O, Error = E>,
{
    delimited(multispace1, inner, multispace1)
}

/// Parses the name of an atom.
///
/// An atom name is a string of one or more chars, starting with a lowercase letter.
/// The rest of the name can contain alphanumeric characters or underscores.
///
/// # Example
/// ```
/// # use mimir::parser::atom_name;
/// let (_, name) = atom_name("atom").unwrap();
/// assert_eq!(name, "atom");
/// ```
pub fn atom_name(input: &str) -> IResult<&str, String> {
    let (input, head) = one_of(ATOM_START_CHARS).parse(input)?;
    let (input, tail) =
        recognize(many0(alt((one_of(ALPHANUMERIC_CHARS), char('_'))))).parse(input)?;

    let name = format!("{}{}", head, tail);

    Ok((input, name))
}

/// Parses a single atom.
///
/// An atom is a string of one or more chars, starting with a lowercase letter.
///
/// # Example
/// ```
/// # use mimir::parser::atom;
/// # use mimir::parser::Term;
/// let (_, atom) = atom("atom").unwrap();
/// assert_eq!(atom, Term::atom("atom"));
/// ```
pub fn atom(input: &str) -> IResult<&str, Term> {
    let (input, name) = atom_name(input)?;
    let atom = Term::atom(name);

    Ok((input, atom))
}

/// Parses a single quoted atom.
///
/// A quoted atom can be any string surrounded by "", but cannot start or end with a space.
///
/// # Example
/// ```
/// # use mimir::parser::quoted_atom;
/// # use mimir::parser::Term;
/// let (_, atom) = quoted_atom("\"quoted atom\"").unwrap();
/// assert_eq!(atom, Term::atom("quoted atom"));
/// ```
pub fn quoted_atom(input: &str) -> IResult<&str, Term> {
    let (input, name) = delimited(
        tag("\""),
        verify(take_till(|c| c == '"'), |content: &str| {
            !(content.is_empty() || content.starts_with(' ') || content.ends_with(' '))
        }),
        tag("\""),
    )
    .parse(input)?;

    let atom = Term::atom(name);

    Ok((input, atom))
}

/// Parses a single number.
///
/// Numbers can be positive or negative integers, and can contain underscores as digit separators.
/// Numbers must fit within the range of i64.
///
/// # Example
/// ```
/// # use mimir::parser::number;
/// # use mimir::parser::Term;
/// let (_, num) = number("1_234_567").unwrap();
/// assert_eq!(num, 1234567);
/// ```
pub fn number(input: &str) -> IResult<&str, i64> {
    let (input, negative) = opt(tag("-")).parse(input)?;
    let (input, digits) = recognize(many1(one_of("01234567890_"))).parse(input)?;

    // Must contain a digit
    if !digits.contains(|c: char| c.is_ascii_digit()) {
        return Err(nom::Err::Error(Error::from_error_kind(
            input,
            nom::error::ErrorKind::Verify,
        )));
    }

    // Cannot start or end with an underscore
    if digits.starts_with('_') || digits.ends_with('_') {
        return Err(nom::Err::Error(Error::from_error_kind(
            input,
            nom::error::ErrorKind::Verify,
        )));
    }

    // Remove the underscores
    let str_num = digits.replace('_', "");

    // Convert to i64
    let mut num = match str_num.parse::<i64>() {
        Ok(n) => n,
        Err(_) => {
            return Err(nom::Err::Error(Error::from_error_kind(
                input,
                nom::error::ErrorKind::MapRes,
            )));
        }
    };

    if negative.is_some() {
        num = -num;
    }

    Ok((input, num))
}

/// Parses a single variable.
///
/// A variable is a string of one or more chars, starting with an underscore or uppercase letter.
///
/// # Example
/// ```
/// # use mimir::parser::variable;
/// # use mimir::parser::Term;
/// let (_, var) = variable("VarName").unwrap();
/// assert_eq!(var, Term::var("VarName"));
/// ```
pub fn variable(input: &str) -> IResult<&str, Term> {
    let (input, head) = one_of(VAR_START_CHARS).parse(input)?;
    let (input, tail) = alphanumeric0(input)?;

    let name = format!("{}{}", head, tail);

    if name == "_" {
        return Ok((input, Term::Wildcard));
    }

    let var = Term::var(name);

    Ok((input, var))
}

/// Parses a compound.
///
/// A compound has a functor and argument list.
/// arguments are any terms separated by commas and enclosed in parentheses.
///
/// # Example
/// ```
/// # use mimir::parser::compound;
/// # use mimir::parser::Term;
/// let (_, comp) = compound("f(a, b, c)").unwrap();
/// assert_eq!(comp, Term::compound("f", vec![Term::atom("a"), Term::atom("b"), Term::atom("c")]));
/// ```
pub fn compound(input: &str) -> IResult<&str, Term> {
    let (input, functor) = atom_name(input)?;
    let (input, _) = multispace0(input)?;
    let (input, args) =
        delimited(tag("("), separated_list0(ws(tag(",")), term), tag(")")).parse(input)?;

    let compound = Term::compound(functor, args);

    Ok((input, compound))
}

/// Parses a term.
///
/// Can be an atom, quoted atom, variable, number, or compound.
///
/// # Example
/// ```
/// # use mimir::parser::term;
/// # use mimir::parser::Term;
/// let (_, t) = term("atom").unwrap();
/// assert_eq!(t, Term::atom("atom"));
///
/// let (_, t) = term("Var").unwrap();
/// assert_eq!(t, Term::var("Var"));
///```
pub fn term(input: &str) -> IResult<&str, Term> {
    // Compound has to be checked before atom, because compound has an atom as a prefix
    alt((
        compound,
        atom,
        quoted_atom,
        variable,
        number.map(Term::Number),
        list,
    ))
    .parse(input)
}

/// Parses a term that can only appear on the right-hand side of a clause.
///
/// These are binary operations like equality, arithmetic, and comparisons.
/// They are mapped to arity-2 compounds with specific functor names.
///
/// # Example
/// ```
/// # use mimir::parser::rhs_term;
/// # use mimir::parser::Term;
/// let (_, t) = rhs_term("X \\= Y").unwrap();
/// assert_eq!(t, Term::compound("not_equal", vec![Term::var("X"), Term::var("Y")]));
///
/// let (_, t) = rhs_term("A = B + C").unwrap();
/// assert_eq!(t, Term::compound("equal", vec![Term::var("A"), Term::compound("add", vec![Term::var("B"), Term::var("C")])]));
/// ```
/// # TODO
/// - Does not handle operator precedence or parentheses.
/// - Accepts statements such as `A = B = C`, which may not be desired.
pub fn rhs_term(input: &str) -> IResult<&str, Term> {
    // A dict of operators and their corresponding functor names
    let operators = vec![
        // Equality
        (r"\=", "not_equal"),
        ("=", "equal"),
        // Arithmetic
        ("+", "add"),
        ("-", "subtract"),
        ("*", "multiply"),
        ("/", "divide"),
        // Comparisons
        (">", "greater_than"),
        ("<", "less_than"),
        (">=", "greater_than_equal"),
        ("=<", "less_than_equal"),
    ];

    for (op, functor) in operators {
        // Parse the operator with surrounding whitespace
        let op_parser = ws(tag::<&str, &str, Error<_>>(op));

        let mut parser = (term, op_parser, rhs_term);

        if let Ok((input, parsed)) = parser.parse(input) {
            let (left, _, right) = parsed;
            let term = Term::compound(functor.to_string(), vec![left, right]);
            return Ok((input, term));
        }
    }

    // Try to parse a normal term if no operator matched
    term(input)
}

/// Parses an arithmetic expression.
pub fn arith_expression(input: &str) -> IResult<&str, ArithExp> {
    let operators = vec![
        ArithOp::Addition,
        ArithOp::Subtraction,
        ArithOp::Multiplication,
        ArithOp::Division,
    ];

    for operator in operators {
        let op_str = operator.to_string();

        let mut expr_parser = (
            arith_expression,
            ws(tag::<&str, &str, Error<_>>(&op_str)),
            arith_expression,
        );

        if let Ok((input, parsed)) = expr_parser.parse(input) {
            let expr = ArithExp::Expr(Box::new(parsed.0), Box::new(parsed.2), operator);

            return Ok((input, expr));
        }
    }

    // Try and parse as a single number (base case)
    let (input, term) = term(input)?;

    let expr = ArithExp::Term(Box::new(term));
    Ok((input, expr))
}

/// Parses a list.
///
/// Lists can contain elements seperated by commas or be for pattern matching, with variables separated by `|`.
/// Lists are converted into nested `cons/2` compounds ending with the `nil/0` atom.
pub fn list(input: &str) -> IResult<&str, Term> {
    // [a, b, c]
    let comma_list = separated_list0(tag(","), ws(term));

    // [X, Y | Z]
    // [X, Y | [a, b, c]]
    let pattern_list = separated_pair(
        separated_list1(tag(","), ws(term)),
        ws(tag("|")),
        alt((
            delimited(tag("["), separated_list0(tag(","), ws(term)), tag("]")),
            term.map(|t| vec![t]),
        )),
    )
    .map(|(mut head, mut tail)| {
        head.append(&mut tail);
        head
    });

    let (input, elements) =
        delimited(tag("["), alt((pattern_list, comma_list)), tag("]")).parse(input)?;

    // Convert to nested cons/2 compounds ending with nil/0
    let mut list_term = Term::atom("nil");
    for element in elements.into_iter().rev() {
        list_term = Term::compound("cons", vec![element, list_term]);
    }

    Ok((input, list_term))
}

/// Parses a clause.
///
/// A clause has a head (a compound) and a body (a list of terms).
/// The head and body are separated by ':-', and the body terms are separated by commas.
/// The clause ends with a period.
///
/// # Example
/// ```
/// # use mimir::parser::clause;
/// # use mimir::parser::{Term, Clause};
/// let input = "parent(X, Y) :- father(X, Y), mother(X, Y).";
/// let (_, clause) = clause(input).unwrap();
/// let expected = Clause::rule(
///     Term::compound("parent", vec![Term::var("X"), Term::var("Y")]),
///     vec![
///         Term::compound("father", vec![Term::var("X"), Term::var("Y")]),
///         Term::compound("mother", vec![Term::var("X"), Term::var("Y")]),
///   ]
/// );
/// assert_eq!(clause, expected);
/// ```
pub fn clause(input: &str) -> IResult<&str, Clause> {
    let (input, head) = compound(input)?;
    let (input, _) = ws(tag(":-")).parse(input)?;
    let (input, body) = separated_list1(ws(tag(",")), rhs_term).parse(input)?;
    let (input, _) = ws(tag(".")).parse(input)?;

    Ok((input, Clause::rule(head, body)))
}

/// Parses a fact, a special case of a clause with no body (and so no ':-').
///
/// # Example
/// ```
/// # use mimir::parser::fact;
/// # use mimir::parser::{Term, Clause};
/// let input = "father(john, mary).";
/// let (_, fact) = fact(input).unwrap();
/// let expected = Clause::fact(
///     Term::compound("father", vec![Term::atom("john"), Term::atom("mary")])
/// );
/// assert_eq!(fact, expected);
/// ```
pub fn fact(input: &str) -> IResult<&str, Clause> {
    let (input, head) = compound(input)?;
    let (input, _) = ws(tag(".")).parse(input)?;

    Ok((input, Clause::fact(head)))
}

/// Parses a program, a series of clauses and facts.
pub fn program(input: &str) -> IResult<&str, Vec<Clause>> {
    many0(ws(alt((clause, fact)))).parse(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atom_basic() {
        let (remaining, parsed) = atom("t").unwrap();
        assert_eq!(parsed, Term::atom("t"));
        assert_eq!(remaining, "");

        let (remaining, parsed) = atom("text").unwrap();
        assert_eq!(parsed, Term::atom("text"));
        assert_eq!(remaining, "");

        let (remaining, parsed) = atom("tExt").unwrap();
        assert_eq!(parsed, Term::atom("tExt"));
        assert_eq!(remaining, "");
    }

    #[test]
    fn test_atom_with_suffix() {
        let (remaining, parsed) = atom("text ").unwrap();
        assert_eq!(parsed, Term::atom("text"));
        assert_eq!(remaining, " ");

        let (remaining, parsed) = atom("text.").unwrap();
        assert_eq!(parsed, Term::atom("text"));
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
        assert_eq!(parsed, Term::atom("text text"));
        assert_eq!(remaining, "");
    }

    #[test]
    fn test_quoted_atom_with_suffix() {
        let (remaining, parsed) = quoted_atom("\"text text\".").unwrap();
        assert_eq!(parsed, Term::atom("text text"));
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
        assert_eq!(parsed, 1234567890);
        assert_eq!(remaining, "");

        let (remaining, parsed) = number("1_234_567_890").unwrap();
        assert_eq!(parsed, 1234567890);
        assert_eq!(remaining, "");
    }

    #[test]
    fn test_number_with_suffix() {
        let (remaining, parsed) = number("10.").unwrap();
        assert_eq!(parsed, 10);
        assert_eq!(remaining, ".");

        let (remaining, parsed) = number("10 ").unwrap();
        assert_eq!(parsed, 10);
        assert_eq!(remaining, " ");
    }

    #[test]
    fn test_number_negative() {
        let (remaining, parsed) = number("-10").unwrap();
        assert_eq!(parsed, -10);
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
        assert_eq!(parsed, Term::var("T"));
        assert_eq!(remaining, "");

        let (remaining, parsed) = variable("Text").unwrap();
        assert_eq!(parsed, Term::var("Text"));
        assert_eq!(remaining, "");

        let (remaining, parsed) = variable("TeXt").unwrap();
        assert_eq!(parsed, Term::var("TeXt"));
        assert_eq!(remaining, "");

        let (remaining, parsed) = variable("_text").unwrap();
        assert_eq!(parsed, Term::var("_text"));
        assert_eq!(remaining, "");
    }

    #[test]
    fn test_variable_with_suffix() {
        let (remaining, parsed) = variable("Text ").unwrap();
        assert_eq!(parsed, Term::var("Text"));
        assert_eq!(remaining, " ");

        let (remaining, parsed) = variable("Text.").unwrap();
        assert_eq!(parsed, Term::var("Text"));
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
            Term::compound("f", vec![Term::atom("a"), Term::atom("b"), Term::atom("c")])
        );
        assert_eq!(remaining, "");

        let (remaining, parsed) = compound("f  (a,b ,  c)").unwrap();
        assert_eq!(
            parsed,
            Term::compound("f", vec![Term::atom("a"), Term::atom("b"), Term::atom("c")])
        );
        assert_eq!(remaining, "");

        let (remaining, parsed) = compound("f(a, X, c)").unwrap();
        assert_eq!(
            parsed,
            Term::compound("f", vec![Term::atom("a"), Term::var("X"), Term::atom("c")])
        );
        assert_eq!(remaining, "");
    }

    #[test]
    fn test_compound_nested() {
        let (remaining, parsed) = compound("f(a, g(n, m), c)").unwrap();
        assert_eq!(
            parsed,
            Term::compound(
                "f",
                vec![
                    Term::atom("a"),
                    Term::compound("g", vec![Term::atom("n"), Term::atom("m"),]),
                    Term::atom("c")
                ]
            )
        );
        assert_eq!(remaining, "");
    }

    #[test]
    fn test_term() {
        let (remaining, parsed) = term("atom").unwrap();
        assert_eq!(parsed, Term::atom("atom"));
        assert_eq!(remaining, "");

        let (remaining, parsed) = term("Var").unwrap();
        assert_eq!(parsed, Term::var("Var"));
        assert_eq!(remaining, "");

        let (remaining, parsed) = term("123").unwrap();
        assert_eq!(parsed, Term::number(123));
        assert_eq!(remaining, "");

        let (remaining, parsed) = term("f(a, b)").unwrap();
        assert_eq!(
            parsed,
            Term::compound("f", vec![Term::atom("a"), Term::atom("b")])
        );
        assert_eq!(remaining, "");
    }

    #[test]
    fn test_clause() {
        let input = "parent(X, Y) :- father(X, Y), mother(X, Y).";
        let expected = Clause::rule(
            Term::compound("parent", vec![Term::var("X"), Term::var("Y")]),
            vec![
                Term::compound("father", vec![Term::var("X"), Term::var("Y")]),
                Term::compound("mother", vec![Term::var("X"), Term::var("Y")]),
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
        let expected = Clause::fact(Term::compound(
            "father",
            vec![Term::atom("john"), Term::atom("mary")],
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
            Term::compound("not_equal", vec![Term::var("X"), Term::var("Y")])
        );
        assert_eq!(remaining, "");

        let (remaining, parsed) = rhs_term("A = B").unwrap();
        assert_eq!(
            parsed,
            Term::compound("equal", vec![Term::var("A"), Term::var("B")])
        );
        assert_eq!(remaining, "");

        let (remaining, parsed) = rhs_term("X =< Y").unwrap();
        assert_eq!(
            parsed,
            Term::compound("less_than_equal", vec![Term::var("X"), Term::var("Y")])
        );
        assert_eq!(remaining, "");
    }

    #[test]
    fn test_nested_rhs_terms() {
        let (remaining, parsed) = rhs_term("A = B + C").unwrap();
        assert_eq!(
            parsed,
            Term::compound(
                "equal",
                vec![
                    Term::var("A"),
                    Term::compound("add", vec![Term::var("B"), Term::var("C")])
                ]
            )
        );
        assert_eq!(remaining, "");
    }

    #[test]
    fn test_clause_with_rhs_terms() {
        let input = "sibling(X, Y) :- parent(Z, X), parent(Z, Y), X \\= Y.";
        let expected = Clause::rule(
            Term::compound("sibling", vec![Term::var("X"), Term::var("Y")]),
            vec![
                Term::compound("parent", vec![Term::var("Z"), Term::var("X")]),
                Term::compound("parent", vec![Term::var("Z"), Term::var("Y")]),
                Term::compound("not_equal", vec![Term::var("X"), Term::var("Y")]),
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
            Term::compound(
                "cons",
                vec![
                    Term::atom("a"),
                    Term::compound(
                        "cons",
                        vec![
                            Term::atom("b"),
                            Term::compound("cons", vec![Term::atom("c"), Term::atom("nil")])
                        ]
                    )
                ]
            )
        );
        assert_eq!(remaining, "");

        let (remaining, parsed) = list("[X, Y | Z]").unwrap();
        assert_eq!(
            parsed,
            Term::compound(
                "cons",
                vec![
                    Term::var("X"),
                    Term::compound(
                        "cons",
                        vec![
                            Term::var("Y"),
                            Term::compound("cons", vec![Term::var("Z"), Term::atom("nil")])
                        ]
                    )
                ]
            )
        );
        assert_eq!(remaining, "");

        let (remaining, parsed) = list("[X, Y | [a, b]]").unwrap();
        assert_eq!(
            parsed,
            Term::compound(
                "cons",
                vec![
                    Term::var("X"),
                    Term::compound(
                        "cons",
                        vec![
                            Term::var("Y"),
                            Term::compound(
                                "cons",
                                vec![
                                    Term::atom("a"),
                                    Term::compound(
                                        "cons",
                                        vec![Term::atom("b"), Term::atom("nil")]
                                    )
                                ]
                            )
                        ]
                    )
                ]
            )
        );
        assert_eq!(remaining, "");
    }
}
