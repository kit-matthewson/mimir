//! Abstract Syntax Tree (AST) definitions for Mini-Prolog.
//!
//! Defines the core data structures used to represent Mini-Prolog terms and clauses.
//! Being the Mini-Prolog syntax, it does not support full Prolog features like lists.

/// A relational operator between two numbers.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RelationalOp {
    LessThan,
    LessThanEqual,
    GreaterThan,
    GreaterThanEqual,
    Equal,
    NotEqual,
}

impl std::fmt::Display for RelationalOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            RelationalOp::LessThan => "<",
            RelationalOp::LessThanEqual => "<=",
            RelationalOp::GreaterThan => ">",
            RelationalOp::GreaterThanEqual => ">=",
            RelationalOp::Equal => "=",
            RelationalOp::NotEqual => "!=",
        };

        write!(f, "{}", s)
    }
}

/// An arithmetic operator between two numbers.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArithOp {
    Addition,
    Subtraction,
    Multiplication,
    Division,
}

impl std::fmt::Display for ArithOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            ArithOp::Addition => "+",
            ArithOp::Subtraction => "-",
            ArithOp::Multiplication => "*",
            ArithOp::Division => "/",
        };

        write!(f, "{}", s)
    }
}

/// An arithmetic expression.
#[derive(Debug, Clone, PartialEq)]
pub enum ArithExp {
    /// A Term.
    Term(Box<Term>),
    /// Two sub-expressions combined with an arithmetic operator.
    Expr(Box<ArithExp>, Box<ArithExp>, ArithOp),
}

impl std::fmt::Display for ArithExp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ArithExp::Term(t) => write!(f, "{}", t),
            ArithExp::Expr(a, b, op) => {
                write!(f, "({}{}{})", a, b, op)
            }
        }
    }
}

/// A Mini-Prolog term.
///
/// Terms can be atoms, numbers, variables, or compound terms.
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// A constant string.
    Atom(String),
    /// A relational operator between two numbers.
    Relation(i64, i64, RelationalOp),
    /// An arithmetic expression
    Expression(ArithExp),
    /// A constant integer.
    Number(i64),
    /// A variable, starting with an uppercase letter.
    Variable(String),
    /// A wildcard variable, represented by `_`.
    Wildcard,
    /// A compound term with a functor and argument list.
    Compound {
        /// The functor name of the compound term.
        functor: String,
        /// The arguments of the compound term.
        args: Vec<Term>,
    },
}

impl Term {
    /// Creates a new atom term.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::Term;
    /// let atom = Term::atom("example");
    /// assert_eq!(atom, Term::Atom("example".to_string()));
    /// ```
    pub fn atom<T: Into<String>>(name: T) -> Self {
        Term::Atom(name.into())
    }

    /// Creates a new number term.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::Term;
    /// let number = Term::number(42);
    /// assert_eq!(number, Term::Number(42));
    /// ```
    pub fn number(num: i64) -> Self {
        Term::Number(num)
    }

    /// Creates a new variable term.
    ///
    /// The name should start with an uppercase letter or underscore, but this invariant is not enforced here.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::Term;
    /// let var = Term::var("X");
    /// assert_eq!(var, Term::Variable("X".to_string()));
    /// ```
    pub fn var<T: Into<String>>(name: T) -> Self {
        Term::Variable(name.into())
    }

    /// Creates a new compound term.
    ///
    /// The functor should be a valid atom name, but this invariant is not enforced here.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::Term;
    /// let comp = Term::compound("f", vec![Term::atom("a"), Term::atom("b")]);
    /// assert_eq!(comp, Term::Compound { functor: "f".to_string(), args: vec![Term::atom("a"), Term::atom("b")] });
    /// ```
    pub fn compound<T: Into<String>>(functor: T, args: Vec<Term>) -> Self {
        Term::Compound {
            functor: functor.into(),
            args,
        }
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Atom(str) | Term::Variable(str) => write!(f, "{}", str),
            Term::Number(num) => write!(f, "{}", num),
            Term::Relation(a, b, op) => {
                write!(f, "{}{}{}", a, b, op)
            }
            Term::Expression(expr) => {
                write!(f, "{}", expr)
            }
            Term::Compound { functor, args } => {
                write!(f, "{}(", functor)?;

                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{}", arg)?;
                }

                write!(f, ")")
            }
            Term::Wildcard => write!(f, "_"),
        }
    }
}

/// A Mini-Prolog clause.
///
/// Clauses consist of a head term and an optional body of terms.
/// Clauses without a body are sometimes called "facts".
#[derive(Debug, Clone, PartialEq)]
pub struct Clause {
    /// The head term of the clause. This is a compound term.
    pub head: Term,
    /// The body terms of the clause.
    pub body: Vec<Term>,
}

impl Clause {
    /// Creates a new fact.
    ///
    /// A fact is a clause with no body.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::{Term, Clause};
    /// // father(john, mary).
    /// let fact = Clause::fact(Term::compound("father", vec![Term::atom("john"), Term::atom("mary")]));
    /// assert_eq!(fact, Clause { head: Term::compound("father", vec![
    ///    Term::atom("john"), Term::atom("mary")
    /// ]), body: vec![] });
    /// ```
    pub fn fact(head: Term) -> Self {
        Clause { head, body: vec![] }
    }

    /// Creates a new rule.
    ///
    /// A rule is a clause with a body of terms.
    ///
    /// # Example
    /// ```
    /// # use mimir::parser::{Term, Clause};
    /// // parent(X, Y) :- father(X, Y), mother(X, Y).
    /// let rule = Clause::rule(
    ///     Term::compound("parent", vec![Term::var("X"), Term::var("Y")]),
    ///     vec![
    ///         Term::compound("father", vec![Term::var("X"), Term::var("Y")]),
    ///         Term::compound("mother", vec![Term::var("X"), Term::var("Y")]),
    ///     ]
    /// );
    /// assert_eq!(rule, Clause { head: Term::compound("parent", vec![Term::var("X"), Term::var("Y")]), body: vec![
    ///     Term::compound("father", vec![Term::var("X"), Term::var("Y")]),
    ///     Term::compound("mother", vec![Term::var("X"), Term::var("Y")]),
    /// ] });
    /// ```
    pub fn rule(head: Term, body: Vec<Term>) -> Self {
        Clause { head, body }
    }
}

impl std::fmt::Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.head)?;

        if !self.body.is_empty() {
            write!(f, " :- ")?;

            for (i, term) in self.body.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }

                write!(f, "{}", term)?;
            }
        }

        write!(f, ".")
    }
}
