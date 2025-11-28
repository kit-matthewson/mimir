pub mod ast;
pub mod clause_parsing;
pub mod term_parsing;

pub use clause_parsing::*;
pub use term_parsing::*;

use nom::{Parser, character::complete::*, sequence::*};

/// Takes a parser and produces a parser that also consumes leading and tracing whitespace.
/// From the nom documentation.
pub fn ws<'a, O, E: nom::error::ParseError<&'a str>, F>(
    inner: F,
) -> impl Parser<&'a str, Output = O, Error = E>
where
    F: Parser<&'a str, Output = O, Error = E>,
{
    delimited(multispace0, inner, multispace0)
}
