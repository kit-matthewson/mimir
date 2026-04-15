//! # Mimir
//!
//! Mimir is a Mini-Prolog interpreter written in Rust, extended with support for fuzzy logic.
//!
//! - Facts and rules can be written with standard Prolog syntax.
//! - Fuzzy rules can be defined using `:~` instead of `:-`, and the last goal in the body is treated as a 'truth expression', evaluated to a float and used as the truth value of the clause.
//!
//! # Crisp Execution
//!
//! Use [`Program::crisp_query`] to execute queries in a classical true/false manner.
//! Predicates written in the standard Prolog style (using `:-`) have a truth value of 1.0 if they can be derived and 0.0 if they cannot.
//! This allows you to write traditional Prolog programs and execute them as normal.
//!
//! If the program contains fuzzy clauses (using `:~`), they will be discarded if their truth value is below 0.5. Solutions returned from a crisp query will have their truth values rounded to either 0.0 or 1.0 accordingly.
//!
//! ```
//! use mimir::Program;
//!
//! // A standard Prolog program defining edges of a graph and a recursive path predicate.
//! let program_src = r"
//! edge(a, b).
//! edge(b, c).
//! edge(c, d).
//!
//! path(A, B) :- edge(A, B).
//! path(A, B) :- edge(A, X), path(X, B).
//! ";
//!
//! let program = Program::new(program_src)?;
//!
//! // Solutions to path(a, X) should include X = b, X = c, and X = d.
//! let solutions = program.crisp_query("path(a, X)")?;
//! assert!(!solutions.is_empty());
//! # return Ok::<(), mimir::MimirError>(())
//! ```
//!
//! # Fuzzy Execution
//!
//! Use [`Program::fuzzy_query`] when your program contains uncertain knowledge.
//! Provide a `truth_threshold` to discard weak derivations during evaluation and avoid floating point precision issues.
//!
//! ```
//! use mimir::Program;
//!
//! // A program with some fuzzy edges.
//! // Rules without a specified truth value have an implied value of 1.0.
//! let program_src = r"
//! edge(a, b).
//! edge(b, c) :~ 0.9.
//! edge(c, d).
//! edge(c, e) :~ 0.8.
//!
//! path(A, B) :- edge(A, B).
//! path(A, B) :- edge(A, X), path(X, B).
//! ";
//!
//! let program = Program::new(program_src)?;
//!
//! // Keep any solution whose evolving truth value stays >= 0.01.
//! let solutions = program.fuzzy_query("path(a, X)", 0.01)?;
//! assert!(!solutions.is_empty());
//!
//! # return Ok::<(), mimir::MimirError>(())
//! ```
//!
//! # Macros
//! Mimir provides a set of macros for conveniently constructing the various components of a Mimir program, such as variables and clauses. See the documentation for the [`macros`] module for details.

#![warn(missing_docs)]
#![allow(clippy::module_inception)]

pub mod engine;
pub mod error;
mod macros;
pub mod parser;
pub mod translator;

pub use error::MimirError;

/// The response from executing a query, which may contain multiple solutions.
#[derive(Debug, Clone)]
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
