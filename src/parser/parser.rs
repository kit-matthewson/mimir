//! Parser implementation for Mini-Prolog.
//!
//! Uses the [`nom`] crate to parse Mini-Prolog syntax into an AST defined in the `ast` module.
//! Because
use super::ast;

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
/// # use mimir::parser::ast::Term;
/// let (_, atom) = atom("atom").unwrap();
/// assert_eq!(atom, Term::atom("atom"));
/// ```
pub fn atom(input: &str) -> IResult<&str, ast::Term> {
    let (input, name) = atom_name(input)?;
    let atom = ast::Term::atom(name);

    Ok((input, atom))
}

/// Parses a single quoted atom.
///
/// A quoted atom can be any string surrounded by "", but cannot start or end with a space.
///
/// # Example
/// ```
/// # use mimir::parser::quoted_atom;
/// # use mimir::parser::ast::Term;
/// let (_, atom) = quoted_atom("\"quoted atom\"").unwrap();
/// assert_eq!(atom, Term::atom("quoted atom"));
/// ```
pub fn quoted_atom(input: &str) -> IResult<&str, ast::Term> {
    let (input, name) = delimited(
        tag("\""),
        verify(take_till(|c| c == '"'), |content: &str| {
            !(content.is_empty() || content.starts_with(' ') || content.ends_with(' '))
        }),
        tag("\""),
    )
    .parse(input)?;

    let atom = ast::Term::atom(name);

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
/// # use mimir::parser::ast::Term;
/// let (_, num) = number("1_234_567").unwrap();
/// assert_eq!(num, Term::number(1234567));
/// ```
pub fn number(input: &str) -> IResult<&str, ast::Term> {
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

    Ok((input, ast::Term::Number(num)))
}

/// Parses a single variable.
///
/// A variable is a string of one or more chars, starting with an underscore or uppercase letter.
///
/// # Example
/// ```
/// # use mimir::parser::variable;
/// # use mimir::parser::ast::Term;
/// let (_, var) = variable("VarName").unwrap();
/// assert_eq!(var, Term::var("VarName"));
/// ```
pub fn variable(input: &str) -> IResult<&str, ast::Term> {
    let (input, head) = one_of(VAR_START_CHARS).parse(input)?;
    let (input, tail) = alphanumeric0(input)?;

    let var = ast::Term::var(format!("{}{}", head, tail));

    Ok((input, var))
}

/// Parses a compound.
///
/// A compound has a functor and argument list.
/// Arguments are any terms separated by commas and enclosed in parentheses.
///
/// # Example
/// ```
/// # use mimir::parser::compound;
/// # use mimir::parser::ast::Term;
/// let (_, comp) = compound("f(a, b, c)").unwrap();
/// assert_eq!(comp, Term::compound("f", vec![Term::atom("a"), Term::atom("b"), Term::atom("c")]));
/// ```
pub fn compound(input: &str) -> IResult<&str, ast::Term> {
    let (input, functor) = atom_name(input)?;
    let (input, _) = multispace0(input)?;
    let (input, args) =
        delimited(tag("("), separated_list0(ws(tag(",")), term), tag(")")).parse(input)?;

    let compound = ast::Term::compound(functor, args);

    Ok((input, compound))
}

/// Parses a term.
///
/// Can be an atom, quoted atom, variable, number, or compound.
///
/// # Example
/// ```
/// # use mimir::parser::term;
/// # use mimir::parser::ast::Term;
/// let (_, t) = term("atom").unwrap();
/// assert_eq!(t, Term::atom("atom"));
///
/// let (_, t) = term("Var").unwrap();
/// assert_eq!(t, Term::var("Var"));
///```
pub fn term(input: &str) -> IResult<&str, ast::Term> {
    // Compound has to be checked before atom, because compound has an atom as a prefix
    alt((compound, atom, quoted_atom, variable, number)).parse(input)
}

/// Parses a clause.
///
/// A clause has a head (a compound) and an optional body (a list of terms).
/// The head and body are separated by ':-', and the body terms are separated by commas.
/// The clause ends with a period.
///
/// # Example
/// ```
/// # use mimir::parser::clause;
/// # use mimir::parser::ast::{Term, Clause};
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
pub fn clause(input: &str) -> IResult<&str, ast::Clause> {
    let (input, head) = compound(input)?;
    let (input, _) = ws(tag(":-")).parse(input)?;
    let (input, body) = separated_list0(ws(tag(",")), term).parse(input)?;
    let (input, _) = ws(tag(".")).parse(input)?;

    Ok((input, ast::Clause::rule(head, body)))
}

/// Parses a fact, a special case of a clause with no body (and so no ':-').
///
/// # Example
/// ```
/// # use mimir::parser::fact;
/// # use mimir::parser::ast::{Term, Clause};
/// let input = "father(john, mary).";
/// let (_, fact) = fact(input).unwrap();
/// let expected = Clause::fact(
///     Term::compound("father", vec![Term::atom("john"), Term::atom("mary")])
/// );
/// assert_eq!(fact, expected);
/// ```
pub fn fact(input: &str) -> IResult<&str, ast::Clause> {
    let (input, head) = compound(input)?;
    let (input, _) = ws(tag(".")).parse(input)?;

    Ok((input, ast::Clause::fact(head)))
}

/// Parses a program, a series of clauses and facts.
pub fn program(input: &str) -> IResult<&str, Vec<ast::Clause>> {
    many0(ws(alt((clause, fact)))).parse(input)
}
