//! Parser for Mini-Prolog.
//!
//! Contains the AST definitions and parsing functions.
//!
//! TODO: Quoted atoms, strings

pub mod ast;

use nom::{
    Parser, branch::*, bytes::complete::*, character::complete::*, combinator::*, multi::*,
    sequence::*,
};

/// Parses an entire Mini-Prolog program consisting of multiple clauses.
///
/// Each clause is separated by optional whitespace.
pub fn program(input: &str) -> nom::IResult<&str, Vec<ast::Clause>> {
    many0(ws(ast::Clause::parse)).parse(input)
}

/// Takes a parser and produces a new parser that also consumes leading and tracing whitespace.
///
/// This implementation is based on the `ws` combinator from the nom documentation.
fn ws<'a, O, E: nom::error::ParseError<&'a str>, F>(
    inner: F,
) -> impl nom::Parser<&'a str, Output = O, Error = E>
where
    F: nom::Parser<&'a str, Output = O, Error = E>,
{
    delimited(multispace0, inner, multispace0)
}

/// Parses a single number.
///
/// Numbers can be positive or negative integers, and can contain underscores as digit separators.
/// Numbers must fit within the range of i64.
///
/// # Example
/// ```
/// # use mimir::parser::number;
/// let (_, num) = number("1_234_567").unwrap();
/// assert_eq!(num, 1234567);
/// ```
pub fn number(input: &str) -> nom::IResult<&str, i64> {
    let (input, sign) = opt(alt((tag("-"), tag("+")))).parse(input)?;
    // Use recognize to capture the full digit string instead of parsing to a vector of &str
    let (input, digits) = recognize(separated_list1(tag("_"), digit1)).parse(input)?;

    let mut number: i64 = digits.replace("_", "").parse().unwrap();

    if let Some(s) = sign
        && s == "-"
    {
        number = -number;
    }

    Ok((input, number))
}

/// Types which can be parsed.
///
/// The type's `Display` implementation should parse into an identical type.
pub trait Parseable: std::fmt::Display + Sized {
    /// Parse the type from a &str input.
    fn parse(input: &str) -> nom::IResult<&str, Self>;
}

impl Parseable for ast::Clause {
    /// A clause has a head (a compound) and an optional body (a list of terms).
    /// The head and body are separated by ':-', and the body terms are separated by commas.
    /// Clauses must end with a period.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::{ast, Parseable};
    /// let input = "parent(X, Y) :- father(X, Y), mother(X, Y).";
    /// let (_, clause) = ast::Clause::parse(input).unwrap();
    ///
    /// assert_eq!(clause.to_string(), input);
    /// ```
    fn parse(input: &str) -> nom::IResult<&str, Self> {
        let (input, head) = ast::Compound::parse(input)?;
        let (input, body) = opt((
            ws(tag(":-")),
            separated_list1(ws(tag(",")), ast::Goal::parse),
        ))
        .parse(input)?;
        let (input, _) = tag(".").parse(input)?;

        let body = body.map_or(vec![], |(_, terms)| terms);

        Ok((input, Self { head, body }))
    }
}

impl Parseable for ast::Goal {
    /// A Goal can be anything that appears as lines of the body of a clause.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::{ast, Parseable};
    /// let input = "X = 5";
    /// let (_, goal) = ast::Goal::parse(input).unwrap();
    ///
    /// assert_eq!(goal.to_string(), input);
    /// ```
    fn parse(input: &str) -> nom::IResult<&str, Self> {
        alt((
            // Relation
            |input| {
                let (input, left) = ast::Term::parse(input)?;
                let (input, op) = ws(ast::RelationalOp::parse).parse(input)?;
                let (input, right) = ast::Term::parse(input)?;

                Ok((input, Self::Relation(left, op, right)))
            },
            // Assignment
            |input| {
                let (input, var) = ast::Variable::parse(input)?;
                let (input, _) = ws(tag("=")).parse(input)?;
                let (input, rhs) = ast::RHS::parse(input)?;

                Ok((input, Self::Assign(var, rhs)))
            },
            // Check
            |input| {
                let (input, compound) = ast::Compound::parse(input)?;

                Ok((input, Self::Check(compound)))
            },
        ))
        .parse(input)
    }
}

impl Parseable for ast::Term {
    /// A Term can be an Atom, Number, Variable, or Compound.
    ///
    /// A special case is lists, which are parsed into `cons/2` compounds.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::{ast, Parseable};
    /// let input = "parent(john, X)";
    /// let (_, term) = ast::Term::parse(input).unwrap();
    ///
    /// assert_eq!(term.to_string(), input);
    /// ```
    fn parse(input: &str) -> nom::IResult<&str, Self> {
        alt((
            |input| {
                let (input, list) = ast::ConsList::parse(input)?;
                Ok((input, Self::List(list)))
            },
            |input| {
                let (input, num) = number.parse(input)?;
                Ok((input, Self::Num(num)))
            },
            |input| {
                // Compound must come before Atom to avoid ambiguity
                let (input, compound) = ast::Compound::parse(input)?;
                Ok((input, Self::Compound(compound)))
            },
            |input| {
                let (input, atom) = ast::Atom::parse(input)?;
                Ok((input, Self::Atom(atom)))
            },
            |input| {
                let (input, var) = ast::Variable::parse(input)?;
                Ok((input, Self::Var(var)))
            },
        ))
        .parse(input)
    }
}

impl Parseable for ast::Atom {
    /// An atom starts with a lowercase letter, followed by any number of alphanumeric characters or underscores.
    ///
    /// For simplicity, quoted atoms are not supported.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::{ast, Parseable};
    /// let input = "john";
    /// let (_, atom) = ast::Atom::parse(input).unwrap();
    ///
    /// assert_eq!(atom.to_string(), input);
    /// ```
    fn parse(input: &str) -> nom::IResult<&str, Self> {
        let (input, name) = recognize(pair(
            take_while1(|c: char| c.is_ascii_lowercase()),
            take_while(|c: char| c.is_ascii_alphanumeric() || c == '_'),
        ))
        .parse(input)?;

        Ok((
            input,
            Self {
                name: name.to_string(),
            },
        ))
    }
}

impl Parseable for ast::Compound {
    /// A compound has a functor and parameter list.
    /// Parameters are terms separated by commas and enclosed in parentheses.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::{ast, Parseable};
    /// let input = "parent(john, X)";
    /// let (_, compound) = ast::Compound::parse(input).unwrap();
    ///
    /// assert_eq!(compound.to_string(), input);
    /// ```
    fn parse(input: &str) -> nom::IResult<&str, Self> {
        let (input, functor) = ast::Atom::parse(input)?;
        let (input, params) = delimited(
            tag("("),
            separated_list0(ws(tag(",")), ast::Term::parse),
            tag(")"),
        )
        .parse(input)?;

        Ok((
            input,
            Self {
                functor: functor.to_string(),
                params,
            },
        ))
    }
}

impl Parseable for ast::Variable {
    /// A variable starts with an uppercase letter or underscore, followed by any number of alphanumeric characters or underscores.
    ///
    /// An underscore alone represents a wildcard variable.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::{ast, Parseable};
    /// let input = "X";
    /// let (_, var) = ast::Variable::parse(input).unwrap();
    ///
    /// assert_eq!(var.to_string(), input);
    /// ```
    fn parse(input: &str) -> nom::IResult<&str, Self> {
        let (input, name) = recognize(pair(
            alt((take_while1(|c: char| c.is_ascii_uppercase()), tag("_"))),
            take_while(|c: char| c.is_ascii_alphanumeric() || c == '_'),
        ))
        .parse(input)?;

        if name == "_" {
            Ok((input, Self::Wildcard))
        } else {
            Ok((input, Self::Var(name.to_string())))
        }
    }
}

impl Parseable for ast::ConsList {
    /// Parses a list.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::{ast, Parseable};
    /// let input = "[1, 2, 3]";
    /// let (_, list) = ast::ConsList::parse(input).unwrap();
    ///
    /// assert_eq!(list.to_string(), input);
    /// ````
    fn parse(input: &str) -> nom::IResult<&str, Self> {
        // [a, b, c]
        let comma_list = separated_list0(tag(","), ws(ast::Term::parse));

        // [X, Y | Z]
        // [X, Y | [a, b, c]]
        let pattern_list = separated_pair(
            separated_list1(tag(","), ws(ast::Term::parse)),
            ws(tag("|")),
            alt((
                delimited(
                    tag("["),
                    separated_list0(tag(","), ws(ast::Term::parse)),
                    tag("]"),
                ),
                ast::Term::parse.map(|t| vec![t]),
            )),
        )
        .map(|(mut head, mut tail)| {
            head.append(&mut tail);
            head
        });

        let (input, elements) =
            delimited(tag("["), alt((pattern_list, comma_list)), tag("]")).parse(input)?;

        let mut list = ast::ConsList::Empty;

        for element in elements.iter().rev() {
            list = ast::ConsList::List(Box::new(element.clone()), Box::new(list));
        }

        Ok((input, list))
    }
}

impl Parseable for ast::RelationalOp {
    /// A relational operator can be one of: ==, \=, <, =<, >, >=.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::{ast, Parseable};
    /// let input = ">=";
    /// let (_, op) = ast::RelationalOp::parse(input).unwrap();
    ///
    /// assert_eq!(op.to_string(), input);
    /// ```
    fn parse(input: &str) -> nom::IResult<&str, Self> {
        alt((
            value(Self::LessThanEqual, tag("=<")),
            value(Self::LessThan, tag("<")),
            value(Self::GreaterThanEqual, tag(">=")),
            value(Self::GreaterThan, tag(">")),
            value(Self::Equal, tag("==")),
            value(Self::NotEqual, tag("\\=")),
        ))
        .parse(input)
    }
}

impl Parseable for ast::RHS {
    /// The right-hand side of an assignment can be a Term or an ArithExpr.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::{ast, Parseable};
    /// let input = "(X + 5)";
    /// let (_, rhs) = ast::RHS::parse(input).unwrap();
    ///
    /// assert_eq!(rhs.to_string(), input);
    /// ```
    fn parse(input: &str) -> nom::IResult<&str, Self> {
        alt((
            |input| {
                let (input, expr) = ast::ArithExpr::parse(input)?;
                Ok((input, Self::Expr(expr)))
            },
            |input| {
                let (input, compound) = ast::Compound::parse(input)?;
                Ok((input, Self::Compound(compound)))
            },
        ))
        .parse(input)
    }
}

impl Parseable for ast::ArithExpr {
    /// An arithmetic expression can be a variable, number, or binary operation.
    /// Expressions can be nested using parentheses, but otherwise precedence is not handled.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::{ast, Parseable};
    /// let input = "((X + 5) * Y)";
    /// let (_, expr) = ast::ArithExpr::parse(input).unwrap();
    ///
    /// assert_eq!(expr.to_string(), input);
    /// ```
    fn parse(input: &str) -> nom::IResult<&str, Self> {
        // Parse a primary expression: variable, number, or parenthesized expression
        fn parse_primary(input: &str) -> nom::IResult<&str, ast::ArithExpr> {
            alt((
                map(ast::Variable::parse, ast::ArithExpr::Var),
                map(number, ast::ArithExpr::Num),
                delimited(ws(tag("(")), ast::ArithExpr::parse, ws(tag(")"))),
            ))
            .parse(input)
        }

        // Take the leftmost primary expression
        let (input, initial) = parse_primary(input)?;

        // Fold over any subsequent (op, primary) pairs to build the full expression
        fold_many0(
            pair(ws(ast::ArithOp::parse), parse_primary),
            move || initial.clone(),
            |acc, (op, next)| Self::Expr(Box::new(acc), op, Box::new(next)),
        )
        .parse(input)
    }
}

impl Parseable for ast::ArithOp {
    /// An arithmetic operator can be one of: +, -, *, /.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::{ast, Parseable};
    /// let input = "+";
    /// let (_, op) = ast::ArithOp::parse(input).unwrap();
    ///
    /// assert_eq!(op.to_string(), input);
    /// ```
    fn parse(input: &str) -> nom::IResult<&str, Self> {
        alt((
            value(Self::Add, tag("+")),
            value(Self::Subtract, tag("-")),
            value(Self::Multiply, tag("*")),
            value(Self::Divide, tag("/")),
        ))
        .parse(input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_number_parsing() {
        let cases = vec![
            ("123", 123),
            ("-456", -456),
            ("1_000_000", 1_000_000),
            ("+42", 42),
        ];

        for (input, expected) in cases {
            let (_, result) = number(input).unwrap();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_number_parsing_invalid() {
        let cases = vec!["abc", "12a34", "--123", "1__000"];

        for input in cases {
            let result = number(input);
            // May either fail to parse or not consume the entire input
            assert!(result.is_err() || !result.unwrap().0.is_empty());
        }
    }

    #[test]
    fn test_clause_parsing() {
        let input = "parent(X, Y) :- father(X, Y), mother(X, Y).";
        let (_, clause) = ast::Clause::parse(input).unwrap();

        assert_eq!(clause.to_string(), input);

        let input = "factorial(0, 1).";
        let (_, clause) = ast::Clause::parse(input).unwrap();
        assert_eq!(clause.to_string(), input);
    }

    #[test]
    fn test_clause_parsing_invalid() {
        let cases = vec![
            "parent(X, Y) father(X, Y), mother(X, Y).", // Missing ':-'
            "parent(X, Y) :- father(X, Y) mother(X, Y).", // Missing comma
            "parent(X, Y) :- father(X, Y), mother(X, Y)", // Missing period
            "parent(X, Y) :- .",                        // Empty body
            "parent(X, Y)) :- father(X, Y).",           // Extra parenthesis
        ];

        for input in cases {
            let result = ast::Clause::parse(input);
            assert!(result.is_err());
        }
    }

    #[test]
    fn test_goal_parsing() {
        let cases = vec![
            (
                "X = 5",
                ast::Goal::Assign(
                    ast::Variable::Var("X".to_string()),
                    ast::RHS::Expr(ast::ArithExpr::Num(5)),
                ),
            ),
            (
                "age(Y) > 18",
                ast::Goal::Relation(
                    ast::Term::Compound(ast::Compound {
                        functor: "age".to_string(),
                        params: vec![ast::Term::Var(ast::Variable::Var("Y".to_string()))],
                    }),
                    ast::RelationalOp::GreaterThan,
                    ast::Term::Num(18),
                ),
            ),
            (
                "parent(john, X)",
                ast::Goal::Check(ast::Compound {
                    functor: "parent".to_string(),
                    params: vec![
                        ast::Term::Atom(ast::Atom {
                            name: "john".to_string(),
                        }),
                        ast::Term::Var(ast::Variable::Var("X".to_string())),
                    ],
                }),
            ),
        ];

        for (input, expected) in cases {
            let (_, result) = ast::Goal::parse(input).unwrap();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_term_parsing() {
        let cases = vec![
            (
                "atom",
                ast::Term::Atom(ast::Atom {
                    name: "atom".to_string(),
                }),
            ),
            ("12345", ast::Term::Num(12345)),
            ("X", ast::Term::Var(ast::Variable::Var("X".to_string()))),
            (
                "parent(john, X)",
                ast::Term::Compound(ast::Compound {
                    functor: "parent".to_string(),
                    params: vec![
                        ast::Term::Atom(ast::Atom {
                            name: "john".to_string(),
                        }),
                        ast::Term::Var(ast::Variable::Var("X".to_string())),
                    ],
                }),
            ),
        ];

        for (input, expected) in cases {
            let (_, result) = ast::Term::parse(input).unwrap();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_atom_parsing() {
        let cases = vec![
            (
                "atom",
                ast::Atom {
                    name: "atom".to_string(),
                },
            ),
            (
                "foo_bar123",
                ast::Atom {
                    name: "foo_bar123".to_string(),
                },
            ),
        ];

        for (input, expected) in cases {
            let (_, result) = ast::Atom::parse(input).unwrap();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_atom_parsing_invalid() {
        let cases = vec!["Atom", "123abc", "_atom", ""];

        for input in cases {
            let result = ast::Atom::parse(input);
            assert!(result.is_err());
        }
    }

    #[test]
    fn test_variable_parsing() {
        let cases = vec![
            ("X", ast::Variable::Var("X".to_string())),
            ("_Y", ast::Variable::Var("_Y".to_string())),
            ("_abc", ast::Variable::Var("_abc".to_string())),
            ("_", ast::Variable::Wildcard),
        ];

        for (input, expected) in cases {
            let (_, result) = ast::Variable::parse(input).unwrap();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_list_parsing() {
        // TODO Tests for [H | T] etc
        let cases = vec![
            (
                "[1, 2, 3]",
                ast::ConsList::List(
                    Box::new(ast::Term::Num(1)),
                    Box::new(ast::ConsList::List(
                        Box::new(ast::Term::Num(2)),
                        Box::new(ast::ConsList::List(
                            Box::new(ast::Term::Num(3)),
                            Box::new(ast::ConsList::Empty),
                        )),
                    )),
                ),
            ),
            (
                "[1, 2]",
                ast::ConsList::List(
                    Box::new(ast::Term::Num(1)),
                    Box::new(ast::ConsList::List(
                        Box::new(ast::Term::Num(2)),
                        Box::new(ast::ConsList::Empty),
                    )),
                ),
            ),
            (
                "[1]",
                ast::ConsList::List(Box::new(ast::Term::Num(1)), Box::new(ast::ConsList::Empty)),
            ),
            ("[]", ast::ConsList::Empty),
        ];

        for (input, expected) in cases {
            let (_, result) = ast::ConsList::parse(input).unwrap();
            assert_eq!(result, expected)
        }
    }

    #[test]
    fn test_variable_parsing_invalid() {
        let cases = vec!["atom", "1Var", ""];

        for input in cases {
            let result = ast::Variable::parse(input);
            assert!(result.is_err());
        }
    }

    #[test]
    fn test_relational_op_parsing() {
        let cases = vec![
            ("==", ast::RelationalOp::Equal),
            ("\\=", ast::RelationalOp::NotEqual),
            ("<", ast::RelationalOp::LessThan),
            ("=<", ast::RelationalOp::LessThanEqual),
            (">", ast::RelationalOp::GreaterThan),
            (">=", ast::RelationalOp::GreaterThanEqual),
        ];

        for (input, expected) in cases {
            let (_, result) = ast::RelationalOp::parse(input).unwrap();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_relational_op_parsing_invalid() {
        let cases = vec!["=", "!=", "=>", "<>", "abc"];

        for input in cases {
            let result = ast::RelationalOp::parse(input);
            // May either fail to parse or not consume the entire input
            assert!(result.is_err() || !result.unwrap().0.is_empty());
        }
    }

    #[test]
    fn test_rhs_parsing() {
        let cases = vec![
            (
                "X",
                ast::RHS::Expr(ast::ArithExpr::Var(ast::Variable::Var("X".to_string()))),
            ),
            (
                "(X + 5)",
                ast::RHS::Expr(ast::ArithExpr::Expr(
                    Box::new(ast::ArithExpr::Var(ast::Variable::Var("X".to_string()))),
                    ast::ArithOp::Add,
                    Box::new(ast::ArithExpr::Num(5)),
                )),
            ),
            (
                "parent(john, X)",
                ast::RHS::Compound(ast::Compound {
                    functor: "parent".to_string(),
                    params: vec![
                        ast::Term::Atom(ast::Atom {
                            name: "john".to_string(),
                        }),
                        ast::Term::Var(ast::Variable::Var("X".to_string())),
                    ],
                }),
            ),
        ];

        for (input, expected) in cases {
            let (_, result) = ast::RHS::parse(input).unwrap();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_arith_expr_parsing() {
        let cases = vec![
            (
                "X",
                ast::ArithExpr::Var(ast::Variable::Var("X".to_string())),
            ),
            ("42", ast::ArithExpr::Num(42)),
            (
                "X + 5",
                ast::ArithExpr::Expr(
                    Box::new(ast::ArithExpr::Var(ast::Variable::Var("X".to_string()))),
                    ast::ArithOp::Add,
                    Box::new(ast::ArithExpr::Num(5)),
                ),
            ),
            (
                "(X + 5) * Y",
                ast::ArithExpr::Expr(
                    Box::new(ast::ArithExpr::Expr(
                        Box::new(ast::ArithExpr::Var(ast::Variable::Var("X".to_string()))),
                        ast::ArithOp::Add,
                        Box::new(ast::ArithExpr::Num(5)),
                    )),
                    ast::ArithOp::Multiply,
                    Box::new(ast::ArithExpr::Var(ast::Variable::Var("Y".to_string()))),
                ),
            ),
        ];

        for (input, expected) in cases {
            let (_, result) = ast::ArithExpr::parse(input).unwrap();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_arith_expr_parsing_invalid() {
        let cases = vec!["X +", "X ++ 5", "42 ** 2", "(X + 5", "X + )5(", "(X + 5))"];

        for input in cases {
            let result = ast::ArithExpr::parse(input);
            // May either fail to parse or not consume the entire input
            assert!(result.is_err() || !result.unwrap().0.is_empty());
        }
    }

    #[test]
    fn test_arith_op_parsing() {
        let cases = vec![
            ("+", ast::ArithOp::Add),
            ("-", ast::ArithOp::Subtract),
            ("*", ast::ArithOp::Multiply),
            ("/", ast::ArithOp::Divide),
        ];

        for (input, expected) in cases {
            let (_, result) = ast::ArithOp::parse(input).unwrap();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_arith_op_parsing_invalid() {
        let cases = vec!["++", "--", "**", "//", "abc"];

        for input in cases {
            let result = ast::ArithOp::parse(input);
            // May either fail to parse or not consume the entire input
            assert!(result.is_err() || !result.unwrap().0.is_empty());
        }
    }
}
