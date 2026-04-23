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

/// A value in a solution, which can be a number, a compound term, an atom, or a list.
#[derive(Debug, Clone)]
pub enum Value {
    /// A numeric value.
    Num(f64),
    /// A compound term, consisting of a functor and a list of argument values.
    Term(String, Vec<Value>),
    /// An atom, a term with no arguments.
    Atom(String),
    /// A list, from a term with functor '.' and two arguments (head and tail).
    List(Vec<Value>),
    /// A placeholder value
    Placeholder,
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Num(n) => write!(f, "{}", n),
            Value::Atom(s) => write!(f, "{}", s),
            Value::Term(functor, args) => {
                if args.is_empty() {
                    write!(f, "{}", functor)
                } else {
                    let args_str = args
                        .iter()
                        .map(|arg| format!("{}", arg))
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "{}({})", functor, args_str)
                }
            }
            Value::List(values) => {
                let values_str = values
                    .iter()
                    .map(|value| format!("{}", value))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "[{}]", values_str)
            }
            Value::Placeholder => write!(f, "_"),
        }
    }
}

impl From<engine::Value> for Value {
    fn from(value: engine::Value) -> Self {
        match value {
            engine::Value::Number(ordered_float) => Self::Num(ordered_float.into_inner()),
            engine::Value::Ground(functor, values) => {
                if values.is_empty() {
                    Self::Atom(functor)
                } else if functor == "." && values.len() == 2 {
                    // Special case for lists, which are ./2
                    let head = Value::from(values[0].clone());
                    let tail = Value::from(values[1].clone());

                    match tail {
                        Value::List(mut tail_values) => {
                            tail_values.insert(0, head);
                            Self::List(tail_values)
                        }
                        Value::Atom(ref s) if s == "nil" => Self::List(vec![head]),
                        other => Self::List(vec![head, other]),
                    }
                } else {
                    Self::Term(
                        functor,
                        values.into_iter().map(Value::from).collect::<Vec<_>>(),
                    )
                }
            }

            engine::Value::Placeholder(_) => Self::Placeholder,
        }
    }
}

impl TryInto<f64> for Value {
    type Error = MimirError;

    fn try_into(self) -> Result<f64, Self::Error> {
        match self {
            Value::Num(n) => Ok(n),
            _ => Err(MimirError::InvalidValueType("number".to_string())),
        }
    }
}

impl TryInto<Vec<f64>> for Value {
    type Error = MimirError;

    fn try_into(self) -> Result<Vec<f64>, Self::Error> {
        match self {
            Value::List(values) => values
                .into_iter()
                .map(|value| match value {
                    Value::Num(n) => Ok(n),
                    _ => Err(MimirError::InvalidValueType("number".to_string())),
                })
                .collect(),
            _ => Err(MimirError::InvalidValueType("list".to_string())),
        }
    }
}

/// The response from executing a query, which may contain multiple solutions.
#[derive(Debug, Clone)]
pub struct Solution {
    /// The variable bindings for this solution, mapping variables to their values.
    bindings: Vec<(String, Value)>,
    /// The truth value of the solution, which is a number between 0 and 1.
    truth_value: f64,
}

impl Solution {
    /// Create a user-facing solution from an engine solution.
    pub fn from_engine_solution(
        engine_solution: &engine::Solution,
        vars: &Vec<engine::Variable>,
    ) -> Self {
        let mut engine_bindings = Vec::new();
        for var in vars {
            if let Some(value) = engine_solution.get(var) {
                engine_bindings.push((var.clone(), value.clone()));
            }
        }

        let bindings = engine_bindings
            .into_iter()
            .map(|(var, value)| (var.name().to_string(), Value::from(value)))
            .collect::<Vec<_>>();

        Solution {
            bindings,
            truth_value: engine_solution.truth_value(),
        }
    }

    /// Get the variable bindings for this solution.
    pub fn bindings_vec(&self) -> &Vec<(String, Value)> {
        &self.bindings
    }

    /// Get the variable bindings for this solution as a HashMap.
    pub fn bindings(&self) -> std::collections::HashMap<String, Value> {
        self.bindings
            .iter()
            .cloned()
            .collect::<std::collections::HashMap<_, _>>()
    }

    /// Get the value of a specific variable in this solution, if it exists.
    pub fn get(&self, var_name: &str) -> Option<Value> {
        self.bindings().get(var_name).cloned()
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

        let solutions = engine_solutions
            .into_iter()
            .map(|solution| Solution::from_engine_solution(&solution, &vars))
            .collect::<Vec<_>>();

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
            solution
                .get("X")
                .is_some_and(|value| matches!(value, Value::Atom(ref s) if s == "d"))
        });

        assert!(has_d, "expected path(a, X) to include X = d");
    }
}
