use crate::parser::{compound, term, ws};

use super::ast;

use nom::{IResult, Parser, bytes::complete::*, multi::*};

/// Parses a clause.
pub fn clause(input: &str) -> IResult<&str, ast::Clause> {
    let (input, head) = compound(input)?;
    let (input, _) = ws(tag(":-")).parse(input)?;
    let (input, body) = separated_list0(ws(tag(",")), term).parse(input)?;
    let (input, _) = ws(tag(".")).parse(input)?;

    Ok((input, ast::Clause::rule(head, body)))
}

/// Parses a fact, a special case of a clause with no body (and so no ':-').
pub fn fact(input: &str) -> IResult<&str, ast::Clause> {
    let (input, head) = compound(input)?;
    let (input, _) = super::ws(tag(".")).parse(input)?;

    Ok((input, ast::Clause::fact(head)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::ast;

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

        let input = "parent(X, Y)  :-  \n father(X, Y) ,  mother(X, Y) . ";
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
}
