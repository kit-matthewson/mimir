//! # Mimir: A Prolog Interpreter in Rust
//!
//! Mimir is a simple Mini-Prolog interpreter implemented in Rust.

#![warn(missing_docs)]
#![allow(clippy::module_inception)]

pub mod engine;
pub mod error;
pub mod parser;

pub use error::MimirError;

/// A macro for conveniently constructing Vecs of variables.
///
/// # Example
/// ```
/// # use mimir::engine::Variable;
/// # use mimir::var_vec;
/// let vars = var_vec!["A", "B", "C"];
/// assert_eq!(vars, vec![Variable::new("A"), Variable::new("B"), Variable::new("C")]);
/// ```
#[macro_export]
macro_rules! var_vec {
    ( $($x:expr),*) => {
        vec![$(
            Variable::new($x),
        )*]
    };
}

/// A macro for defining clauses.
///
/// # Example
/// ```
/// # use mimir::engine::{Clause, Symbol, Variable, Goal, RHSTerm};
/// # use mimir::clause;
///
/// let is_ten = clause!(
///     is_ten(T1) { T2 } :- Goal::Conjunction(
///         Box::new(Goal::Assign(Variable::new("T2"), RHSTerm::Num(10))),
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
        Clause::new(
            Symbol::new(
                stringify!($name),
                vec![$( Variable::new(stringify!($p)) ),*],
                vec![$( Variable::new(stringify!($l)) ),*],
            ),
            $goal
        )
    };
}
