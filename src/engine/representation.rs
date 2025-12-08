//! Internal Mini-Prolog representation

use std::collections::HashMap;

use crate::error::EngineError;

/// A reference to a variable by name.
///
/// Currently stored as an owned `String`, but feel this could be optimised.
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct Variable {
    name: String,
}

impl std::fmt::Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// The value of a variable.
///
/// This may be uninitialised.
#[derive(Clone)]
pub struct Value {}

impl Value {
    /// Create a new, uninitialised, value.
    pub fn uninitialised() -> Self {
        todo!()
    }

    /// Create a new value from a number.
    pub fn from_number(_n: i64) -> Self {
        todo!()
    }

    /// Attempt to get a number from this value.
    pub fn number(&self) -> Option<i64> {
        todo!();
    }
}

/// The head of a clause with a name, parameters, and list of local variables.
#[allow(missing_docs)]
#[derive(Clone)]
pub struct Symbol {
    pub functor: String,
    pub parameters: Vec<Variable>,
    pub local_vars: Vec<Variable>,
}

/// Possible relational operations.
#[allow(missing_docs)]
#[derive(Clone, Copy)]
pub enum RelationalOp {
    LessThan,
    LessThanEqual,
    GreaterThan,
    GreaterThanEqual,
    Equal,
    NotEqual,
}

impl RelationalOp {
    /// Use this operator to evaluate two numbers
    pub fn evaluate(&self, a: i64, b: i64) -> bool {
        match self {
            RelationalOp::LessThan => a < b,
            RelationalOp::LessThanEqual => a <= b,
            RelationalOp::GreaterThan => a > b,
            RelationalOp::GreaterThanEqual => a >= b,
            RelationalOp::Equal => a == b,
            RelationalOp::NotEqual => a != b,
        }
    }
}

/// Possible arithmetic operations.
#[allow(missing_docs)]
#[derive(Clone, Copy)]
pub enum ArithmeticOp {
    Add,
    Subtract,
    Multiply,
    Divide,
}

/// A term that can appear on the right-hand side of an assignment.
#[derive(Clone)]
pub enum RHSTerm {
    /// A literal number
    Number(i64),
    /// An arithmetic expression
    Expression(Expression),
    /// A symbol (clause head)
    Symbol(Symbol),
}

impl RHSTerm {
    /// Evaluate this term to a value given the environment
    pub fn evaluate(&self, _env: &Environment) -> Value {
        match self {
            RHSTerm::Number(n) => Value::from_number(*n),
            RHSTerm::Expression(_expr) => {
                todo!()
            }
            RHSTerm::Symbol(_sym) => {
                todo!()
            }
        }
    }
}

/// An arithmetic expression.
#[derive(Clone)]
pub enum Expression {
    /// A variable in the expression
    Var(Variable),
    /// A binary expression with two sub-expressions and an operator
    Expr(Box<Expression>, Box<Expression>, ArithmeticOp),
}

/// Possible goals. These act as the body of clauses and the elements of the goal stack.
#[derive(Clone)]
pub enum Goal {
    /// A conjunction of two goals: both must be true
    Conjunction(Box<Goal>, Box<Goal>),
    /// A disjunction of two goals: at least one must be true
    Disjunction(Box<Goal>, Box<Goal>),
    /// Two variables that must be unified
    Equivalence(Variable, Variable),
    /// Check that the given clause is true
    Check {
        /// The name of the clause
        functor: String,
        /// The variable arguments of the clause
        arguments: Vec<Variable>,
    },
    /// A special goal that restores a previous environment
    Restore(Environment),
    /// Relational statements for numbers
    Relation(Variable, Variable, RelationalOp),
    /// Make a variable equivilant to some term
    Assign(Variable, RHSTerm),
    /// A boolean goal: true always succeeds, false always fails
    Bool(bool),
}

/// A clause with head and body.
///
/// The body is a single `Goal`, which can be a conjunction or disjunction.
#[allow(missing_docs)]
pub struct Clause {
    pub head: Symbol,
    pub body: Goal,
}

/// A choice contains the information needed to recover from a backtrack.
#[allow(missing_docs)]
pub struct Choice {
    pub goal: Goal,
    pub env: Environment,
    pub equiv: Equivalence,
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

/// The Environment maps variables to values, local to a specific clause.
#[derive(Clone)]
pub struct Environment {
    mapping: HashMap<Variable, Value>,
}

impl Environment {
    /// Create an environemt for a symbol with the given arguments.
    ///
    /// Local variables to the clause are assigned `None`.
    pub fn new(symbol: &Symbol, arguments: &Vec<Value>) -> Result<Self, EngineError> {
        if symbol.parameters.len() != arguments.len() {
            return Err(EngineError::UnexpectedParamNum(
                symbol.parameters.len(),
                arguments.len(),
            ));
        }

        let mut mapping = HashMap::with_capacity(symbol.parameters.len() + symbol.local_vars.len());

        for (var, value) in symbol.parameters.iter().zip(arguments) {
            mapping.insert(var.clone(), value.clone());
        }

        for var in symbol.local_vars.iter() {
            mapping.insert(var.clone(), Value::uninitialised());
        }

        Ok(Environment { mapping })
    }

    /// Creates an empty environment.
    pub fn clear(&mut self) {
        self.mapping.clear();
    }

    /// Check if this environment is empty
    pub fn is_empty(&self) -> bool {
        self.mapping.is_empty()
    }

    /// Create a new environment from a given clause and existing environent
    ///
    /// The other environment is used to get paramater values
    pub fn from_clause(clause: &Clause, env: &Environment) -> Result<Self, EngineError> {
        let clause_args = clause
            .head
            .parameters
            .iter()
            .map(|var| env.get(var))
            .collect();

        match clause_args {
            Ok(args) => Environment::new(&clause.head, &args),
            Err(err) => Err(err),
        }
    }

    /// Get the value of the given variable.
    pub fn get(&self, _variable: &Variable) -> Result<Value, EngineError> {
        todo!()
    }
}

/// The Clause Database provides a mapping from clause names and arities to a list clauses.
/// Clauses are returned in the same order that they are defined in the program.
pub struct ClauseDatabase {}

impl ClauseDatabase {
    /// Create a new clause database.
    pub fn new(_program: Vec<Clause>) -> Self {
        todo!()
    }

    /// Get the clauses associated with the given functor and arity.
    /// Will return an empty list if functor/arity does not exist in the database.
    pub fn get(&self, _functor: &str, _arity: usize) -> Vec<Clause> {
        todo!()
    }
}

impl Default for ClauseDatabase {
    fn default() -> Self {
        ClauseDatabase::new(Vec::new())
    }
}

/// Stores the equivalence relations for variables in the environment.
#[derive(Clone, Copy)]
pub struct Equivalence {}

impl Equivalence {
    /// Create a new equivalence.
    pub fn new() -> Self {
        todo!();
    }

    /// Attempt to unify two values.
    pub fn unify(&self, _val1: &Value, _val2: &Value) -> Result<(), EngineError> {
        todo!();
    }
}

impl Default for Equivalence {
    fn default() -> Self {
        Equivalence::new()
    }
}
