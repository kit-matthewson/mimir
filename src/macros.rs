//! Macros for constructing the various components of a Mimir program, such as variables and clauses.
//!
//! # Example
//! ```
//! # use mimir::{assign, clause, check, conjunction, query, truth_expression, var, var_vec, lit};
//! # use mimir::engine::RHSTerm;
//! let program = vec![
//!    clause!(edge(t1, t2) {} :- conjunction!(
//!        assign!(t1, RHSTerm::Sym(lit!(a))),
//!        assign!(t2, RHSTerm::Sym(lit!(b))),
//!        truth_expression!(1.0)
//!    )),
//!    clause!(edge(t1, t2) {} :- conjunction!(
//!        assign!(t1, RHSTerm::Sym(lit!(b))),
//!        assign!(t2, RHSTerm::Sym(lit!(c))),
//!        truth_expression!(1.0)
//!    )),
//!    clause!(edge(t1, t2) {} :- conjunction!(
//!        assign!(t1, RHSTerm::Sym(lit!(c))),
//!        assign!(t2, RHSTerm::Sym(lit!(d))),
//!        truth_expression!(1.0)
//!    )),
//!    clause!(path(A, B) {} :- check!(edge, A, B)),
//!    clause!(path(A, B) {} :- conjunction!(
//!        check!(edge, A, X),
//!        check!(path, X, B)
//!    )),
//! ];
//! let query = query!(path, a, X);
//! ```

/// Constructs a variable with the given name.
///
/// # Example
/// ```
/// # use mimir::engine::Variable;
/// # use mimir::var;
/// let x = var!(X);
/// assert_eq!(x, Variable::new("X"));
/// ```
#[macro_export]
macro_rules! var {
    ($x:expr) => {
        $crate::engine::Variable::new(stringify!($x))
    };
}

/// Constructs a vector of variables with the given names.
///
/// # Example
/// ```
/// # use mimir::engine::Variable;
/// # use mimir::var_vec;
/// let vars = var_vec![A, B, C];
/// assert_eq!(vars, vec![Variable::new("A"), Variable::new("B"), Variable::new("C")]);
/// ```
#[macro_export]
macro_rules! var_vec {
    ( $($x:expr),*) => {
        vec![$(
            $crate::var!($x),
        )*]
    };
}

/// Macro for constructing an expression
///
/// # Example
/// ```
/// # use mimir::engine::{Expression, Variable, ArithmeticOp};
/// # use mimir::{var, expr};
/// # use ordered_float::OrderedFloat;
/// let expr = expr!((X + 1) * (Y - 2));
///
/// assert_eq!(expr, Expression::Expr(
///     Box::new(Expression::Expr(
///         Box::new(Expression::Var(var!(X))),
///         Box::new(Expression::Num(OrderedFloat::from(1.0))),
///         ArithmeticOp::Add
///     )),
///     Box::new(Expression::Expr(
///         Box::new(Expression::Var(var!(Y))),
///         Box::new(Expression::Num(OrderedFloat::from(2.0))),
///         ArithmeticOp::Subtract
///     )),
///     ArithmeticOp::Multiply
/// ));
/// ```
#[macro_export]
macro_rules! expr {
    // Pass through parenthesis
    ( ( $($inner:tt)+ ) ) => {
        $crate::expr!($($inner)+)
    };

    // Addition
    ( $left:tt + $($right:tt)+ ) => {
        $crate::engine::Expression::Expr(
            Box::new($crate::expr!($left)),
            Box::new($crate::expr!($($right)+)),
            $crate::engine::ArithmeticOp::Add,
        )
    };
    ( $left:tt + $right:tt ) => {
        $crate::engine::Expression::Expr(
            Box::new($crate::expr!($left)),
            Box::new($crate::expr!($right)),
            $crate::engine::ArithmeticOp::Add,
        )
    };

    // Subtraction
    ( $left:tt - $($right:tt)+ ) => {
        $crate::engine::Expression::Expr(
            Box::new($crate::expr!($left)),
            Box::new($crate::expr!($($right)+)),
            $crate::engine::ArithmeticOp::Subtract,
        )
    };
    ( $left:tt - $right:tt ) => {
        $crate::engine::Expression::Expr(
            Box::new($crate::expr!($left)),
            Box::new($crate::expr!($right)),
            $crate::engine::ArithmeticOp::Subtract,
        )
    };

    // Multiplication
    ( $left:tt * $($right:tt)+ ) => {
        $crate::engine::Expression::Expr(
            Box::new($crate::expr!($left)),
            Box::new($crate::expr!($($right)+)),
            $crate::engine::ArithmeticOp::Multiply,
        )
    };
    ( $left:tt * $right:tt ) => {
        $crate::engine::Expression::Expr(
            Box::new($crate::expr!($left)),
            Box::new($crate::expr!($right)),
            $crate::engine::ArithmeticOp::Multiply,
        )
    };

    // Division
    ( $left:tt / $($right:tt)+ ) => {
        $crate::engine::Expression::Expr(
            Box::new($crate::expr!($left)),
            Box::new($crate::expr!($($right)+)),
            $crate::engine::ArithmeticOp::Divide,
        )
    };
    ( $left:tt / $right:tt ) => {
        $crate::engine::Expression::Expr(
            Box::new($crate::expr!($left)),
            Box::new($crate::expr!($right)),
            $crate::engine::ArithmeticOp::Divide,
        )
    };

    // Variable
    ( $var:ident ) => {
        $crate::engine::Expression::Var($crate::var!($var))
    };

    // Number literal
    ( $num:literal ) => {
        $crate::engine::Expression::Num(ordered_float::OrderedFloat::from($num as f64))
    };
}

/// Constructs a 'literal'.
///
/// Literals are just symbols with no parameters.
#[macro_export]
macro_rules! lit {
    ( $name:expr ) => {
        $crate::engine::Symbol::new(stringify!($name), vec![], vec![])
    };
}

mod goal {
    //! Macros for conveniently constructing the various goals

    /// Constructs a conjunction goal from multiple subgoals.
    ///
    /// Handles the folding of multiple goals into a single conjunction goal, so that you don't have to manually nest them.
    #[macro_export]
    macro_rules! conjunction {
        // Base case for two goals.
        ( $goal1:expr, $goal2:expr ) => {
            $crate::engine::Goal::Conjunction(Box::new($goal1), Box::new($goal2))
        };
        // Recursive case for more than two goals.
        ( $goal1:expr, $($rest:expr),+ ) => {
            $crate::engine::Goal::Conjunction(Box::new($goal1), Box::new($crate::conjunction!($($rest),+)))
        };
    }

    /// Constructs a disjunction goal from multiple subgoals.
    ///
    /// Handles the folding of multiple goals into a single disjunction goal, so that you don't have to manually nest them.
    #[macro_export]
    macro_rules! disjunction {
        // Base case for two goals.
        ( $goal1:expr, $goal2:expr ) => {
            $crate::engine::Goal::Disjunction(Box::new($goal1), Box::new($goal2))
        };
        // Recursive case for more than two goals.
        ( $goal1:expr, $($rest:expr),+ ) => {
            $crate::engine::Goal::Disjunction(Box::new($goal1), Box::new($crate::disjunction!($($rest),+)))
        };
    }

    /// Constructs an equivalence goal between two terms.
    #[macro_export]
    macro_rules! equivalence {
        ( $term1:expr, $term2:expr ) => {
            $crate::engine::Goal::Equivalence($term1, $term2)
        };
    }

    /// Constructs a check goal from a functor and a vector of terms.
    #[macro_export]
    macro_rules! check {
        ( $functor:expr, $($term:expr),* ) => {
            $crate::engine::Goal::Check { functor: stringify!($functor).into(), params: $crate::var_vec![$($term),*] }
        };
    }

    /// Constructs a relation goal from two variables and a relational operator.
    #[macro_export]
    macro_rules! relation {
        ( $var1:tt < $var2:tt ) => {
            $crate::engine::Goal::Relation(
                $crate::var!(stringify!($var1)),
                $crate::var!(stringify!($var2)),
                $crate::engine::RelationalOp::LessThan,
            )
        };
        ( $var1:tt <= $var2:tt ) => {
            $crate::engine::Goal::Relation(
                $crate::var!(stringify!($var1)),
                $crate::var!(stringify!($var2)),
                $crate::engine::RelationalOp::LessThanOrEqual,
            )
        };
        ( $var1:tt > $var2:tt ) => {
            $crate::engine::Goal::Relation(
                $crate::var!(stringify!($var1)),
                $crate::var!(stringify!($var2)),
                $crate::engine::RelationalOp::GreaterThan,
            )
        };
        ( $var1:tt >= $var2:tt ) => {
            $crate::engine::Goal::Relation(
                $crate::var!(stringify!($var1)),
                $crate::var!(stringify!($var2)),
                $crate::engine::RelationalOp::GreaterThanOrEqual,
            )
        };
    }

    /// Constructs an assignment goal between a variable and a term.
    #[macro_export]
    macro_rules! assign {
        ( $var:expr, $term:expr ) => {
            $crate::engine::Goal::Assign(stringify!($var).into(), $term)
        };
    }

    /// Constructs a truth expression goal from an expression.
    #[macro_export]
    macro_rules! truth_expression {
        ( $expr:expr ) => {
            $crate::engine::Goal::TruthExpr($crate::expr!($expr))
        };
    }
}

/// A macro for defining clauses.
///
/// # Example
/// ```
/// # use mimir::engine::{Clause, Symbol, Variable, Goal, RHSTerm};
/// # use mimir::clause;
/// # use ordered_float::OrderedFloat;
///
/// let is_ten = clause!(
///     is_ten(T1) { T2 } :- Goal::Conjunction(
///         Box::new(Goal::Assign(Variable::new("T2"), RHSTerm::Num(OrderedFloat::from(10.0)))),
///         Box::new(Goal::Equivalence(Variable::new("T1"), Variable::new("T2")))
///     )
/// );
///
/// assert_eq!(is_ten.head().functor(), "is_ten");
/// assert_eq!(is_ten.arity(), 1);
/// ```
#[macro_export]
macro_rules! clause {
    ($name:ident ( $($p:ident),* ) { $($l:ident),* } :- $goal:expr) => {
        $crate::engine::Clause::new(
            $crate::engine::Symbol::new(
                stringify!($name),
                vec![$( $crate::engine::Variable::new(stringify!($p)) ),*],
                vec![$( $crate::engine::Variable::new(stringify!($l)) ),*],
            ),
            $goal
        )
    };
}

/// Creates a query goal from a functor and a vector of terms.
#[macro_export]
macro_rules! query {
    ( $functor:expr, $($term:expr),* ) => {
        $crate::engine::Query {
            local_vars: vec![$( $crate::var!($term) ),*],
            goal: $crate::engine::Goal::Check { functor: stringify!($functor).into(), params: vec![$( $crate::var!($term) ),*] },
        }
    };
}
