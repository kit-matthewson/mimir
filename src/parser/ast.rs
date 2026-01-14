//! Abstract Syntax Tree (AST) definitions for Mini-Prolog.
//!
//! Defines the core data structures used to represent Mini-Prolog terms and clauses.
//! Being the Mini-Prolog syntax, it does not support full Prolog features like lists.

/// The type to use for numbers.
type Number = i64;

/// A Mini-Prolog clause.
///
/// Clauses consist of a head term and an optional body of terms.
/// Clauses without a body are sometimes called "facts".
#[derive(Debug, Clone, PartialEq)]
pub struct Clause {
    /// The head term of the clause. This is a compound term.
    pub head: Compound,
    /// The body goals of the clause.
    pub body: Vec<Goal>,
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

/// Goals (lines) that can appear as the body of a clause.
#[derive(Debug, Clone, PartialEq)]
pub enum Goal {
    /// A relational operator between two terms.
    Relation(Term, RelationalOp, Term),
    /// An assignment expression.
    Assign(Variable, RHS),
    /// A compound term to check.
    Check(Compound),
}

impl std::fmt::Display for Goal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Goal::Relation(a, op, b) => write!(f, "{} {} {}", a, op, b),
            Goal::Assign(var, rhs) => write!(f, "{} = {}", var, rhs),
            Goal::Check(compound) => write!(f, "{}", compound),
        }
    }
}

/// A Mini-Prolog term.
///
/// Terms can be atoms, numbers, variables, or compound terms.
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// An atom.
    Atom(Atom),
    /// A constant integer.
    Num(Number),
    /// A variable, starting with an uppercase letter.
    Var(Variable),
    /// A list.
    List(Vec<Term>),
    /// A compound term with a functor and parameter list.
    Compound(Compound),
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Atom(atom) => write!(f, "{}", atom),
            Term::Num(n) => write!(f, "{}", n),
            Term::Var(var) => write!(f, "{}", var),
            Term::List(list) => write!(f, "{:?}", list),
            Term::Compound(compound) => write!(f, "{}", compound),
        }
    }
}

/// An atom, represented by a lowercase string.
#[derive(Debug, Clone, PartialEq)]
pub struct Atom {
    /// The name of the atom.
    pub name: String,
}

impl std::fmt::Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// A compound term with functor and parameter list.
#[derive(Debug, Clone, PartialEq)]
pub struct Compound {
    /// The functor (name) of the compound term.
    pub functor: String,
    /// The parameters of the compound term.
    pub params: Vec<Term>,
}

impl std::fmt::Display for Compound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}(", self.functor)?;

        for (i, arg) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            write!(f, "{}", arg)?;
        }

        write!(f, ")")?;

        Ok(())
    }
}

/// A variable, represented by a string or underscore for wildcard.
#[derive(Debug, Clone, PartialEq)]
pub enum Variable {
    /// A named variable.
    Var(String),
    /// A wildcard variable (_).
    Wildcard,
}

impl std::fmt::Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Variable::Var(name) => write!(f, "{}", name),
            Variable::Wildcard => write!(f, "_"),
        }
    }
}

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
            RelationalOp::Equal => "==",
            RelationalOp::NotEqual => "\\=",
        };

        write!(f, "{}", s)
    }
}

/// An expression that can appear as the right hand side of an expression.
///
/// These can be compounds or arithmetic expressions.
#[derive(Debug, Clone, PartialEq)]
pub enum RHS {
    /// A compound.
    Compound(Compound),
    /// An arithmetic expression.
    Expr(ArithExpr),
}

impl std::fmt::Display for RHS {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RHS::Compound(compound) => write!(f, "{}", compound),
            RHS::Expr(expr) => write!(f, "{}", expr),
        }
    }
}

/// An arithmetic expression.
///
/// Expressions can be variables, numbers, or binary operations between two expressions.
#[derive(Debug, Clone, PartialEq)]
pub enum ArithExpr {
    /// A variable.
    Var(Variable),
    /// A constant number.
    Num(Number),
    /// A binary arithmetic expression.
    Expr(Box<ArithExpr>, ArithOp, Box<ArithExpr>),
}

impl std::fmt::Display for ArithExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ArithExpr::Var(var) => write!(f, "{}", var),
            ArithExpr::Num(n) => write!(f, "{}", n),
            ArithExpr::Expr(left, op, right) => {
                write!(f, "({} {} {})", left, op, right)
            }
        }
    }
}

/// An arithmetic operator between two numbers.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArithOp {
    Add,
    Subtract,
    Multiply,
    Divide,
}

impl std::fmt::Display for ArithOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            ArithOp::Add => "+",
            ArithOp::Subtract => "-",
            ArithOp::Multiply => "*",
            ArithOp::Divide => "/",
        };

        write!(f, "{}", s)
    }
}
