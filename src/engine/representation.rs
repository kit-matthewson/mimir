//! Internal Mini-Prolog representation

use std::collections::HashMap;

use crate::error::EngineError;

/// Type for placeholder value IDs
type PlaceholderID = u32;
/// Type of numbers
type Number = i64;

/// A reference to a variable by name.
///
/// Currently stored as an owned `String`, but this could be optimised.
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
/// This may be an uninitialised 'placeholder' value.
#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum Value {
    /// An i64 'Number' value.
    Number(Number),
    /// A ground term. A ground term is a term that does not contain any variables.
    /// Essentially, a functor a list of argument values.
    Ground(String, Vec<Value>),
    /// A placeholder value.
    Placeholder(PlaceholderID),
}

impl Value {
    /// Attempt to get a number from this value.
    pub fn number(&self) -> Option<Number> {
        match self {
            Value::Number(n) => Some(*n),
            _ => None,
        }
    }

    /// Attempt to get the placeholder ID of this value.
    pub fn placeholder_id(&self) -> Option<PlaceholderID> {
        match self {
            Value::Placeholder(id) => Some(*id),
            _ => None,
        }
    }
}

/// Manages the generation of unique placeholder values.
///
/// # Example
/// ```
/// # use mimir::engine::PlaceholderGenerator;
/// let mut pgen = PlaceholderGenerator::new();
///
/// let a = pgen.new_placeholder();
/// let b = pgen.new_placeholder();
///
/// assert!(a != b);
/// ```
pub struct PlaceholderGenerator {
    next: PlaceholderID,
}

impl PlaceholderGenerator {
    /// Creates a new generator for IDs starting at 0.
    pub fn new() -> Self {
        PlaceholderGenerator {
            next: PlaceholderID::MIN,
        }
    }

    /// Generates a new placeholder value with a unique ID.
    pub fn new_placeholder(&mut self) -> Value {
        let id = self.next;
        self.next += 1;

        Value::Placeholder(id)
    }
}

impl Default for PlaceholderGenerator {
    fn default() -> Self {
        PlaceholderGenerator::new()
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
    /// Use this operator to evaluate two numbers.
    pub fn evaluate(&self, a: Number, b: Number) -> bool {
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

impl ArithmeticOp {
    /// Evaluates two numbers with this operator.
    /// Uses saturating addition, subtraction, and multiplication so numbers are clamped to the range of `i64`.
    /// Division by zero returns an error.
    pub fn evaluate(&self, a: Number, b: Number) -> Result<Number, EngineError> {
        match self {
            ArithmeticOp::Add => Ok(a.saturating_add(b)),
            ArithmeticOp::Subtract => Ok(a.saturating_sub(b)),
            ArithmeticOp::Multiply => Ok(a.saturating_mul(b)),
            ArithmeticOp::Divide => match a.checked_div(b) {
                Some(n) => Ok(n),
                None => Err(EngineError::DivByZero),
            },
        }
    }
}

/// A term that can appear on the right-hand side of an assignment.
#[derive(Clone)]
pub enum RHSTerm {
    /// A literal number.
    Number(Number),
    /// An arithmetic expression.
    Expression(Expression),
    /// A symbol (clause head).
    Symbol(Symbol),
}

impl RHSTerm {
    /// Evaluate this term to a value given the environment.
    pub fn evaluate(&self, env: &Environment, equiv: &Equivalence) -> Result<Value, EngineError> {
        match self {
            RHSTerm::Number(n) => Ok(Value::Number(*n)),
            RHSTerm::Expression(expr) => {
                let result = expr.evaluate(env, equiv)?;
                Ok(Value::Number(result))
            }
            RHSTerm::Symbol(sym) => {
                // Get the value of each parameter
                let values = sym
                    .parameters
                    .iter()
                    .map(|param| env.get(param, equiv))
                    .collect::<Result<Vec<Value>, EngineError>>()?;

                Ok(Value::Ground(sym.functor.clone(), values))
            }
        }
    }
}

/// An arithmetic expression.
#[derive(Clone)]
pub enum Expression {
    /// A number.
    Num(Number),
    /// A variable in the expression.
    Var(Variable),
    /// A binary expression with two sub-expressions and an operator.
    Expr(Box<Expression>, Box<Expression>, ArithmeticOp),
}

impl Expression {
    /// Evaluate this expression to a number.
    pub fn evaluate(&self, env: &Environment, equiv: &Equivalence) -> Result<Number, EngineError> {
        match self {
            Expression::Num(n) => Ok(*n),
            Expression::Var(var) => {
                let val = env.get(var, equiv)?;

                if let Some(n) = val.number() {
                    Ok(n)
                } else {
                    Err(EngineError::NotANumber(var.clone()))
                }
            }

            Expression::Expr(expr1, expr2, op) => {
                let a = expr1.evaluate(env, equiv)?;
                let b = expr2.evaluate(env, equiv)?;
                let result = op.evaluate(a, b)?;

                Ok(result)
            }
        }
    }
}

/// Possible goals. These act as the body of clauses and the elements of the goal stack.
#[derive(Clone)]
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
        /// The variable arguments of the clause.
        arguments: Vec<Variable>,
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

/// A clause with head and body.
///
/// The body is a single `Goal`, which can be a conjunction or disjunction.
#[derive(Clone)]
#[allow(missing_docs)]
pub struct Clause {
    pub head: Symbol,
    pub body: Goal,
}

impl Clause {
    /// Gets the arity (number of arguments) of this clause.
    pub fn arity(&self) -> usize {
        self.head.parameters.len()
    }

    /// Gets the functor (name) of this clause.
    pub fn functor(&self) -> &str {
        &self.head.functor
    }
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
    pub fn new(
        symbol: &Symbol,
        arguments: &Vec<Value>,
        placeholder_gen: &mut PlaceholderGenerator,
    ) -> Result<Self, EngineError> {
        if symbol.parameters.len() != arguments.len() {
            return Err(EngineError::UnexpectedParamNum {
                expected: symbol.parameters.len(),
                got: arguments.len(),
            });
        }

        let mut mapping = HashMap::with_capacity(symbol.parameters.len() + symbol.local_vars.len());

        for (var, value) in symbol.parameters.iter().zip(arguments) {
            mapping.insert(var.clone(), value.clone());
        }

        for var in symbol.local_vars.iter() {
            mapping.insert(var.clone(), placeholder_gen.new_placeholder());
        }

        Ok(Environment { mapping })
    }

    /// Creates an empty environment.
    pub fn clear(&mut self) {
        self.mapping.clear();
    }

    /// Check if this environment is empty.
    pub fn is_empty(&self) -> bool {
        self.mapping.is_empty()
    }

    /// Create a new environment from a given clause and existing environent.
    ///
    /// The other environment is used to get paramater values.
    pub fn from_clause(
        clause: &Clause,
        env: &Environment,
        equiv: &Equivalence,
        placeholder_gen: &mut PlaceholderGenerator,
    ) -> Result<Self, EngineError> {
        let clause_args = clause
            .head
            .parameters
            .iter()
            .map(|var| env.get(var, equiv))
            .collect();

        match clause_args {
            Ok(args) => Environment::new(&clause.head, &args, placeholder_gen),
            Err(err) => Err(err),
        }
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

/// Stores the equivalence relations for variables in the environment.
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
    pub fn set_representative(&self, value: &Value) -> Result<Value, EngineError> {
        if let Some(value) = self.equiv.get(value) {
            self.set_representative(value)
        } else {
            Ok(value.clone())
        }
    }

    /// Attempt to unify two values.
    pub fn unify(&mut self, val1: &Value, val2: &Value) -> Result<(), EngineError> {
        if val1 == val2 {
            return Ok(());
        }

        // A placeholder (unassigned) value always unifies
        if matches!(val1, Value::Placeholder(_)) {
            self.equiv.insert(val1.clone(), val2.clone());

            return Ok(());
        } else if matches!(val2, Value::Placeholder(_)) {
            self.equiv.insert(val2.clone(), val1.clone());

            return Ok(());
        }

        // For a compound, we unify each term
        if let Value::Ground(functor1, args1) = val1
            && let Value::Ground(functor2, args2) = val2
        {
            if functor1 != functor2 || args1.len() != args2.len() {
                return Err(EngineError::CannotUnifyTerms(val1.clone(), val2.clone()));
            }

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
