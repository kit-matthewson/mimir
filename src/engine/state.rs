//! State management for the execution engine.
//!
//! This includes the representation of goals and choices, as well as the environment, clause database, and equivalence relations.
//!
//! # TODO
//! - Consider combining `Environment` and `Equivalence`

use std::collections::HashMap;

use crate::{engine::representation::*, error::EngineError};

/// Possible goals. These act as the body of clauses and the elements of the goal stack.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Goal {
    /// A conjunction of two goals: both must be true.
    Conjunction(Box<Goal>, Box<Goal>),
    /// A disjunction of two goals: at least one must be true.
    Disjunction(Box<Goal>, Box<Goal>),
    /// Two variables that must be unified.
    Equivalence(Variable, Variable),
    /// Check that the given clause is true.
    Check {
        /// The name of the clause.
        functor: String,
        /// The parameters of the clause.
        params: Vec<Variable>,
    },
    /// A special goal that restores a previous environment.
    Restore(Environment),
    /// Relational statements for numbers.
    Relation(Variable, Variable, RelationalOp),
    /// Make a variable equivilant to some term.
    Assign(Variable, RHSTerm),
    /// A boolean goal: true always succeeds, false always fails.
    Bool(bool),
}

impl std::fmt::Display for Goal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Goal::Conjunction(g1, g2) => write!(f, "({} , {})", g1, g2),
            Goal::Disjunction(g1, g2) => write!(f, "({} ; {})", g1, g2),
            Goal::Equivalence(v1, v2) => write!(f, "{} == {}", v1, v2),
            Goal::Check { functor, params } => {
                let args_str = params
                    .iter()
                    .map(|arg| format!("{}", arg))
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "{}({})", functor, args_str)
            }
            Goal::Restore(_) => write!(f, "<restore env>"),
            Goal::Relation(v1, v2, op) => {
                let op_str = match op {
                    RelationalOp::LessThan => "<",
                    RelationalOp::LessThanEqual => "<=",
                    RelationalOp::GreaterThan => ">",
                    RelationalOp::GreaterThanEqual => ">=",
                    RelationalOp::Equal => "==",
                    RelationalOp::NotEqual => "!=",
                };
                write!(f, "{} {} {}", v1, op_str, v2)
            }
            Goal::Assign(var, term) => write!(f, "{} := {:?}", var, term),
            Goal::Bool(b) => write!(f, "{}", b),
        }
    }
}

/// A choice contains the information needed to recover from a backtrack.
///
/// Choices are created when the engine needs to branch, such as when handling disjunctions.
/// They store the environment, equivalence, and goal stack at the point of the choice.
pub struct Choice {
    /// The goal to pursue on backtrack.
    pub goal: Goal,
    /// The environment when the choice was made.
    pub env: Environment,
    /// The equivalence when the choice was made.
    pub equiv: Equivalence,
    /// The goal stack when the choice was made.
    pub goal_stack: Vec<Goal>,
}

impl Choice {
    /// Create a new choice when a decision has been made.
    pub fn new(goal: Goal, env: Environment, equiv: Equivalence, goal_stack: Vec<Goal>) -> Self {
        Choice {
            goal,
            env,
            equiv,
            goal_stack,
        }
    }
}

/// An environment maps variables to values.
///
/// Variables always need to be mapped to some value, so placeholders are used for unassigned variables.
/// When a variable is looked up, its value's set representative is returned according to the current equivalence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Environment {
    mapping: HashMap<Variable, Value>,
}

impl Environment {
    /// Create an empty environment.
    pub fn empty() -> Self {
        Environment {
            mapping: HashMap::new(),
        }
    }

    /// Create an environemt for a symbol with the given arguments.
    ///
    /// Mappings are made for the symbol's parameters to the given arguments, and placeholders are created for local variables.
    pub fn for_symbol(
        symbol: &Symbol,
        arguments: &Vec<Value>,
        placeholder_gen: &mut PlaceholderGenerator,
    ) -> Result<Self, EngineError> {
        // The number of parameters must match the number of arguments
        if symbol.parameters.len() != arguments.len() {
            return Err(EngineError::UnexpectedParamNum {
                expected: symbol.parameters.len(),
                got: arguments.len(),
            });
        }

        // Allocate a hash map with space for parameters and local variables
        let mut mapping = HashMap::with_capacity(symbol.parameters.len() + symbol.local_vars.len());

        // Map parameters to arguments
        for (var, value) in symbol.parameters.iter().zip(arguments) {
            mapping.insert(var.clone(), value.clone());
        }

        // Map local variables to new placeholders
        for var in symbol.local_vars.iter() {
            mapping.insert(var.clone(), placeholder_gen.new_placeholder());
        }

        Ok(Environment { mapping })
    }

    /// Create a new environment from a given clause and existing environent.
    ///
    /// Because this method takes the symbol's parameters (instead of arguments, like `for_symbol`), it requires an environment and equivalence to look up the argument values.
    pub fn for_symbol_with_params(
        symbol: &Symbol,
        params: &[Variable],
        env: &Environment,
        equiv: &Equivalence,
        placeholder_gen: &mut PlaceholderGenerator,
    ) -> Result<Self, EngineError> {
        // Get the values for each argument variable from the existing environment
        let values = params
            .iter()
            .map(|var| env.get(var, equiv))
            .collect::<Result<Vec<Value>, EngineError>>()?;

        // Use these values to create the new environment for the clause
        Environment::for_symbol(symbol, &values, placeholder_gen)
    }

    /// Create an environment for a query.
    ///
    /// Queries have no parameters, only local variables.
    /// Placeholders are created for each local variable using the given placeholder generator.
    pub fn for_query(query: &Query, placeholder_gen: &mut PlaceholderGenerator) -> Self {
        // Allocate a hash map with space for local variables
        let mut mapping = HashMap::with_capacity(query.local_vars.len());

        // Map local variables to new placeholders
        for var in query.local_vars.iter() {
            mapping.insert(var.clone(), placeholder_gen.new_placeholder());
        }

        Environment { mapping }
    }

    /// Clear all variable mappings in this environment.
    pub fn clear(&mut self) {
        self.mapping.clear();
    }

    /// Check if this environment is empty.
    pub fn is_empty(&self) -> bool {
        self.mapping.is_empty()
    }

    /// Get the value of the given variable.
    /// This actually returns the set representative of the variable's value.
    pub fn get(&self, variable: &Variable, equiv: &Equivalence) -> Result<Value, EngineError> {
        let value = self
            .mapping
            .get(variable)
            .ok_or_else(|| EngineError::UndefinedVar(variable.clone()))?;

        equiv.set_representative(value)
    }

    /// Assign a value to a variable in this environment.
    ///
    /// Will overwrite any existing assignment.
    pub fn assign(&mut self, variable: &Variable, value: Value) {
        self.mapping.insert(variable.clone(), value);
    }
}

impl std::fmt::Display for Environment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Handle empty environment
        if self.mapping.is_empty() {
            write!(f, "<empty>")?;
            return Ok(());
        }

        let mut first = true;

        for (var, value) in self.mapping.iter() {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{} = {:?}", var, value)?;
            first = false;
        }

        Ok(())
    }
}

/// The Clause Database provides a mapping from clause names and arities to a list clauses.
/// Clauses are returned in the same order that they are defined in the program.
pub struct ClauseDatabase {
    clauses: HashMap<(String, usize), Vec<Clause>>,
}

impl ClauseDatabase {
    /// Create a new clause database.
    /// Clauses will always be returned in the same order as they appear in `program`.
    pub fn new(program: Vec<Clause>) -> Self {
        let mut clauses: HashMap<(String, usize), Vec<Clause>> = HashMap::new();

        for clause in program {
            let key = (clause.functor().to_string(), clause.arity());

            if let Some(vec) = clauses.get_mut(&key) {
                vec.push(clause);
            } else {
                clauses.insert(key, vec![clause]);
            }
        }

        ClauseDatabase { clauses }
    }

    /// Get the clauses associated with the given functor and arity.
    /// Will return an empty list if functor/arity does not exist in the database.
    pub fn get(&self, functor: &str, arity: usize) -> Vec<Clause> {
        self.clauses
            .get(&(functor.to_string(), arity))
            .unwrap_or(&Vec::new())
            .to_vec()
    }
}

impl Default for ClauseDatabase {
    fn default() -> Self {
        ClauseDatabase::new(Vec::new())
    }
}

/// Stores the equivalence relations for values in the environment.
///
/// The equivalence relation allows us to unify terms and track which terms are considered equal.
/// Each value has a 'set representative', which is the canonical value for that equivalence class.
#[derive(Clone)]
pub struct Equivalence {
    equiv: HashMap<Value, Value>,
}

impl Equivalence {
    /// Create a new equivalence.
    pub fn new() -> Self {
        Equivalence {
            equiv: HashMap::new(),
        }
    }

    /// Get the set representative of a value.
    ///
    /// The set representative of a value is the canonical value for its equivalence class.
    /// It is found by following the chain of mappings until a value that maps to itself is found.
    /// For instance, if `A -> B` and `B -> C`, then the representative of all three values is `C`.
    pub fn set_representative(&self, value: &Value) -> Result<Value, EngineError> {
        if let Some(value) = self.equiv.get(value) {
            self.set_representative(value)
        } else {
            Ok(value.clone())
        }
    }

    /// Attempt to unify two values.
    pub fn unify(&mut self, val1: &Value, val2: &Value) -> Result<(), EngineError> {
        // The values are literally the same
        if val1 == val2 {
            return Ok(());
        }

        // A placeholder can be unified with any value
        if matches!(val1, Value::Placeholder(_)) {
            // Value 1 is a placeholder, so make it equivalent to value 2
            self.equiv.insert(val1.clone(), val2.clone());

            return Ok(());
        } else if matches!(val2, Value::Placeholder(_)) {
            // Value 2 is a placeholder, so make it equivalent to value 1
            self.equiv.insert(val2.clone(), val1.clone());

            return Ok(());
        }

        // For a compound, we unify each term
        if let Value::Ground(functor1, args1) = val1
            && let Value::Ground(functor2, args2) = val2
        {
            // Terms with different functors or arities cannot be unified
            if functor1 != functor2 || args1.len() != args2.len() {
                return Err(EngineError::CannotUnifyTerms(val1.clone(), val2.clone()));
            }

            // Attempt to unify each argument
            for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                self.unify(arg1, arg2)?;
            }

            return Ok(());
        }

        // Otherwise, cannot unify
        Err(EngineError::CannotUnifyTerms(val1.clone(), val2.clone()))
    }
}

impl Default for Equivalence {
    fn default() -> Self {
        Equivalence::new()
    }
}
