//! # Mimir: A Prolog Interpreter in Rust
//!
//! Mimir is a simple Mini-Prolog interpreter implemented in Rust.

#![warn(missing_docs)]
#![allow(clippy::module_inception)]

pub mod engine;
pub mod error;
pub mod parser;
pub mod translator;

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
            $crate::engine::Variable::new($x),
        )*]
    };
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

/// The response from executing a query, which may contain multiple solutions.
pub struct Solution {
    /// The variable bindings for this solution, mapping variables to their values.
    bindings: Vec<(engine::Variable, engine::Value)>,
    /// The truth value of the solution, which is a number between 0 and 1.
    truth_value: f64,
}

impl Solution {
    /// Get the variable bindings for this solution.
    pub fn bindings(&self) -> &Vec<(engine::Variable, engine::Value)> {
        &self.bindings
    }

    /// Get the truth value of this solution.
    pub fn truth_value(&self) -> f64 {
        self.truth_value
    }
}

/// A Mini-Prolog program, on which queries can be executed.
pub struct Program {
    engine: engine::Engine,
    program_ast: Vec<parser::ast::Clause>,
}

impl Program {
    /// Parses and translates a Mini-Prolog program from a string, returning a `Program` that can be executed.
    pub fn new(program: &str) -> Result<Self, MimirError> {
        let clauses = parser::program(program)?;

        let translated_clauses = clauses
            .clone()
            .into_iter()
            .map(translator::translate_clause)
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Program {
            engine: engine::Engine::new(translated_clauses),
            program_ast: clauses,
        })
    }

    /// Executes a query against the program, returning a vector of solutions.
    /// Performs a crisp query, treating any solution with a truth value >= 0.5 as true and any solution with a truth value < 0.5 as false.
    pub fn crisp_query(&self, query: &str) -> Result<Vec<Solution>, MimirError> {
        let solutions = self
            .fuzzy_query(query, 0.5)?
            .iter()
            .map(|solution| Solution {
                bindings: solution.bindings.clone(),
                truth_value: if solution.truth_value >= 0.5 {
                    1.0
                } else {
                    0.0
                },
            })
            .collect();

        Ok(solutions)
    }

    /// Executes a query against the program, returning a vector of solutions.
    pub fn fuzzy_query(
        &self,
        query: &str,
        truth_threshold: f64,
    ) -> Result<Vec<Solution>, MimirError> {
        let goal = parser::query(query)?;

        let internal_query = translator::translate_query(goal)?;

        let engine_solutions = self
            .engine
            .execute(internal_query.clone(), truth_threshold)
            .map_err(MimirError::from)?;

        // Find the variables in the query so we know which bindings to return in the solutions
        let mut vars = Vec::new();
        for var in internal_query.local_vars {
            if !var.name().starts_with("_") {
                vars.push(var.clone());
            }
        }

        let mut solutions = Vec::new();

        for engine_solution in engine_solutions {
            let mut bindings = Vec::new();
            for var in &vars {
                if let Some(value) = engine_solution.get(var) {
                    bindings.push((var.clone(), value.clone()));
                }
            }

            solutions.push(Solution {
                bindings,
                truth_value: engine_solution.truth_value(),
            });
        }

        Ok(solutions)
    }
}

impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for clause in &self.program_ast {
            writeln!(f, "{}", clause)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_program() -> Program {
        let program = r"
edge(a, b).
edge(b, c).
edge(c, d).
edge(c, e).

path(A, B) :- edge(A, B).
path(A, B) :- edge(A, X), path(X, B).
";

        Program::new(program).expect("sample program should parse")
    }

    #[test]
    fn simple_edge_query_succeeds() {
        let program = sample_program();

        let solutions = program
            .crisp_query("edge(a, b)")
            .expect("query should execute");

        assert!(!solutions.is_empty(), "expected edge(a, b) to succeed");
    }

    #[test]
    fn recursive_path_with_constants_succeeds() {
        let program = sample_program();

        let solutions = program
            .crisp_query("path(a, d)")
            .expect("query should execute");

        assert!(!solutions.is_empty(), "expected path(a, d) to succeed");
    }

    #[test]
    fn recursive_path_with_variable_reaches_d() {
        let program = sample_program();

        let solutions = program
            .crisp_query("path(a, X)")
            .expect("query should execute");

        let has_d = solutions.iter().any(|solution| {
            solution.bindings().iter().any(|(var, val)| {
                var.name() == "X" && matches!(val, engine::Value::Ground(functor, args) if functor == "d" && args.is_empty())
            })
        });

        assert!(has_d, "expected path(a, X) to include X = d");
    }
}
