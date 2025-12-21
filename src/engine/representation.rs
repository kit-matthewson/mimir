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

impl Variable {
    /// Create a new variable with the given name.
    pub fn new<T: Into<String>>(name: T) -> Self {
        Variable { name: name.into() }
    }
}

impl From<&str> for Variable {
    fn from(s: &str) -> Self {
        Variable::new(s)
    }
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
    /// Essentially, a functor and a list of argument values.
    Ground(String, Vec<Value>),
    /// A placeholder value.
    Placeholder(PlaceholderID),
}

impl Value {
    /// Create a new number value.
    pub fn num<T: Into<Number>>(n: T) -> Self {
        Value::Number(n.into())
    }

    /// Create a new ground value.
    pub fn ground<T: Into<String>>(functor: T, args: Vec<Value>) -> Self {
        Value::Ground(functor.into(), args)
    }

    /// Create a new placeholder value using the provided [PlaceholderGenerator].
    pub fn placeholder(pgen: &mut PlaceholderGenerator) -> Self {
        pgen.new_placeholder()
    }

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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Symbol {
    /// The string functor name.
    pub functor: String,
    /// Vector of parameter variables.
    pub parameters: Vec<Variable>,
    /// Vector of local variables.
    pub local_vars: Vec<Variable>,
}

impl Symbol {
    /// Create a new symbol.
    pub fn new<T: Into<String>, V1: Into<Vec<Variable>>, V2: Into<Vec<Variable>>>(
        functor: T,
        parameters: V1,
        local_vars: V2,
    ) -> Self {
        Symbol {
            functor: functor.into(),
            parameters: parameters.into(),
            local_vars: local_vars.into(),
        }
    }

    /// Helper for creating symbols for facts.
    /// Facts have no local variables.
    pub fn fact<T: Into<String>, V: Into<Vec<Variable>>>(functor: T, parameters: V) -> Self {
        Symbol {
            functor: functor.into(),
            parameters: parameters.into(),
            local_vars: Vec::new(),
        }
    }
}

/// Possible relational operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelationalOp {
    /// Less than: `<`.
    LessThan,
    /// Less than or equal to: `<=`.
    LessThanEqual,
    /// Greater than: `>`.
    GreaterThan,
    /// Greater than or equal to: `>=`.
    GreaterThanEqual,
    /// Equal to: `==`.
    Equal,
    /// Not equal to: `!=`.
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArithmeticOp {
    /// Saturating addition.
    Add,
    /// Saturating subtraction.
    Subtract,
    /// Saturating multiplication.
    Multiply,
    /// Checked integer division. Overflows or division by zero result in an error.
    Divide,
}

impl ArithmeticOp {
    /// Evaluates two numbers with this operator.
    /// Uses saturating addition, subtraction, and multiplication so numbers are clamped to the range of `Number`.
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

/// An arithmetic expression.
#[derive(Debug, Clone, PartialEq, Eq)]
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

    /// Create a number expression.
    pub fn number<T: Into<Number>>(n: T) -> Self {
        Expression::Num(n.into())
    }

    /// Create a variable expression.
    pub fn variable<T: Into<Variable>>(var: T) -> Self {
        Expression::Var(var.into())
    }

    /// Create a binary expression.
    pub fn binary<E1: Into<Expression>, E2: Into<Expression>>(
        expr1: E1,
        expr2: E2,
        op: ArithmeticOp,
    ) -> Self {
        Expression::Expr(Box::new(expr1.into()), Box::new(expr2.into()), op)
    }
}

impl From<Number> for Expression {
    fn from(n: Number) -> Self {
        Expression::Num(n)
    }
}

impl From<Variable> for Expression {
    fn from(var: Variable) -> Self {
        Expression::Var(var)
    }
}

/// A term that can appear on the right-hand side of an assignment.
#[derive(Debug, Clone, PartialEq, Eq)]
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

impl std::fmt::Display for Goal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Goal::Conjunction(g1, g2) => write!(f, "({} , {})", g1, g2),
            Goal::Disjunction(g1, g2) => write!(f, "({} ; {})", g1, g2),
            Goal::Equivalence(v1, v2) => write!(f, "{} == {}", v1, v2),
            Goal::Check { functor, arguments } => {
                let args_str = arguments
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

/// A clause with head and body.
///
/// The body is a single `Goal`, which can be a conjunction or disjunction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    /// The symbol (functor, parameters, and local vars) of the clause.
    pub head: Symbol,
    /// The body goal of the clause.
    pub body: Goal,
}

impl Clause {
    /// Create a new clause.
    pub fn new<T: Into<String>>(
        functor: T,
        parameters: Vec<Variable>,
        local_vars: Vec<Variable>,
        body: Goal,
    ) -> Self {
        Clause {
            head: Symbol {
                functor: functor.into(),
                parameters,
                local_vars,
            },
            body,
        }
    }

    /// Gets the arity (number of arguments) of this clause.
    pub fn arity(&self) -> usize {
        self.head.parameters.len()
    }

    /// Gets the functor (name) of this clause.
    pub fn functor(&self) -> &str {
        &self.head.functor
    }
}

impl std::fmt::Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let params_str = self
            .head
            .parameters
            .iter()
            .map(|param| format!("{}", param))
            .collect::<Vec<String>>()
            .join(", ");

        let local_vars_str = if self.head.local_vars.is_empty() {
            String::new()
        } else {
            let vars_str = self
                .head
                .local_vars
                .iter()
                .map(|var| format!("{}", var))
                .collect::<Vec<String>>()
                .join(", ");
            format!("{{ {} }} ", vars_str)
        };

        write!(
            f,
            "{}({}) {}:- {}.",
            self.head.functor, params_str, local_vars_str, self.body
        )
    }
}

/// A choice contains the information needed to recover from a backtrack.
pub struct Choice {
    /// The goal that led to this choice.
    pub goal: Goal,
    /// The environment to restore after a backtrack.
    pub env: Environment,
    /// The equivalence to restore after a backtrack.
    pub equiv: Equivalence,
    /// The goal stack to restore after a backtrack.
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
    /// Local variables to the clause are assigned to placeholders.
    pub fn for_symbol(
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

    /// Create an environment for a query.
    pub fn for_query(
        local_vars: Vec<Variable>,
        placeholder_gen: &mut PlaceholderGenerator,
    ) -> Self {
        let mut mapping = HashMap::with_capacity(local_vars.len());

        for var in local_vars.iter() {
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

    /// Create a new environment from a given clause and existing environent.
    ///
    /// The other environment is used to get parameter values.
    pub fn from_clause(
        clause: &Clause,
        arguments: &[Variable],
        env: &Environment,
        equiv: &Equivalence,
        placeholder_gen: &mut PlaceholderGenerator,
    ) -> Result<Self, EngineError> {
        let values = arguments
            .iter()
            .map(|var| env.get(var, equiv))
            .collect::<Result<Vec<Value>, EngineError>>()?;

        Environment::for_symbol(&clause.head, &values, placeholder_gen)
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

/// A macro for conveniently constructing Vecs of variables
#[macro_export]
macro_rules! var_vec {
    ( $($x:expr),*) => {
        vec![$(
            Variable::new($x),
        )*]
    };
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;

    #[test]
    fn test_var_creation() {
        let vars = var_vec!["A", "B", "C"];

        assert_eq!(
            vars,
            vec![Variable::new("A"), Variable::new("B"), Variable::new("C")]
        )
    }

    #[test]
    fn test_variable() {
        let a1 = Variable::new("A");
        let a2 = Variable::new("A");
        let b = Variable::new("B");

        assert_eq!(a1, a2);
        assert_ne!(a1, b);
    }

    #[test]
    fn test_value_creation() {
        let n1 = Value::num(2);
        let n2 = Value::num(2);
        let n3 = Value::num(4);

        assert_eq!(n1, n2);
        assert_ne!(n1, n3);

        let g1 = Value::ground("func", vec![n1.clone(), n2.clone()]);
        let g2 = Value::ground("func", vec![n1.clone(), n2.clone()]);
        let g3 = Value::ground("different_func", vec![n1.clone(), n2.clone()]);

        assert_eq!(g1, g2);
        assert_ne!(g1, g3);

        let p1 = Value::Placeholder(1);
        let p2 = Value::Placeholder(1);
        let p3 = Value::Placeholder(2);

        assert_eq!(p1, p2);
        assert_ne!(p1, p3);
    }

    #[test]
    fn test_value_reading() {
        let n = Value::num(10);
        let p = Value::Placeholder(5);

        assert_eq!(n.number(), Some(10));
        assert_eq!(p.number(), None);

        assert_eq!(n.placeholder_id(), None);
        assert_eq!(p.placeholder_id(), Some(5));
    }

    #[test]
    fn test_placeholder_gen() {
        let mut used = HashSet::new();

        let mut pgen = PlaceholderGenerator::new();

        for _ in 0..100 {
            let new = pgen.new_placeholder();
            assert!(!used.contains(&new));
            used.insert(new);
        }
    }

    #[test]
    fn test_symbol() {
        let sym1 = Symbol::new(
            "functor",
            vec![Variable::new("A"), Variable::new("B")],
            vec![Variable::new("X")],
        );

        let sym2 = Symbol::new("functor", var_vec!["A", "B"], var_vec!["X"]);

        assert_eq!(sym1.functor, "functor");
        assert_eq!(sym1.parameters, sym2.parameters);
        assert_eq!(sym1.local_vars, sym2.local_vars);
    }

    #[test]
    fn test_relational_ops() {
        let a = 10;
        let b = 15;

        assert!(RelationalOp::LessThan.evaluate(a, b));
        assert!(RelationalOp::LessThanEqual.evaluate(a, b));
        assert!(!RelationalOp::GreaterThan.evaluate(a, b));
        assert!(!RelationalOp::GreaterThanEqual.evaluate(a, b));
        assert!(!RelationalOp::Equal.evaluate(a, b));
        assert!(RelationalOp::NotEqual.evaluate(a, b));
    }

    #[test]
    fn test_arithmetic_ops() {
        let a = 20;
        let b = 5;

        assert_eq!(ArithmeticOp::Add.evaluate(a, b).unwrap(), 25);
        assert_eq!(ArithmeticOp::Subtract.evaluate(a, b).unwrap(), 15);
        assert_eq!(ArithmeticOp::Multiply.evaluate(a, b).unwrap(), 100);
        assert_eq!(ArithmeticOp::Divide.evaluate(a, b).unwrap(), 4);

        let max = Number::MAX;
        let min = Number::MIN;

        assert_eq!(ArithmeticOp::Add.evaluate(max, 1).unwrap(), max);
        assert_eq!(ArithmeticOp::Subtract.evaluate(min, 1).unwrap(), min);
        assert_eq!(ArithmeticOp::Multiply.evaluate(max, 2).unwrap(), max);
        assert!(ArithmeticOp::Divide.evaluate(a, 0).is_err());
    }

    #[test]
    fn test_expr_evaluation() {
        let env = Environment::empty();
        let equiv = Equivalence::new();

        let expr = Expression::binary(
            10,
            Expression::binary(5, 2, ArithmeticOp::Multiply),
            ArithmeticOp::Add,
        );

        let result = expr.evaluate(&env, &equiv).unwrap();
        assert_eq!(result, 20);

        let mut env = Environment::empty();
        env.mapping.insert(Variable::new("X"), Value::num(3));

        let expr = Expression::binary(
            Expression::binary(20, 5, ArithmeticOp::Subtract),
            Expression::variable("X"),
            ArithmeticOp::Divide,
        );

        let result = expr.evaluate(&env, &equiv).unwrap();
        assert_eq!(result, 5);
    }

    #[test]
    fn test_rhs_term() {
        let mut env = Environment::empty();
        env.mapping.insert(Variable::new("A"), Value::num(1));
        env.mapping.insert(Variable::new("B"), Value::num(2));

        let equiv = Equivalence::new();

        let term = RHSTerm::Number(42);
        let value = term.evaluate(&env, &equiv).unwrap();
        assert_eq!(value, Value::num(42));

        let term = RHSTerm::Expression(Expression::binary(10, 5, ArithmeticOp::Add));
        let value = term.evaluate(&env, &equiv).unwrap();
        assert_eq!(value, Value::num(15));

        let symbol = Symbol::new("func", var_vec!["A", "B"], vec![]);
        let term = RHSTerm::Symbol(symbol);
        let value = term.evaluate(&env, &equiv).unwrap();
        assert_eq!(
            value,
            Value::ground("func", vec![Value::num(1), Value::num(2)])
        );
    }

    #[test]
    fn test_clause() {
        let clause = Clause {
            head: Symbol::new("my_clause", var_vec!["X", "Y"], var_vec!["Z"]),
            body: Goal::Bool(true),
        };

        assert_eq!(clause.arity(), 2);
        assert_eq!(clause.functor(), "my_clause");
    }

    #[test]
    fn test_environment() {
        let mut pgen = PlaceholderGenerator::new();

        let symbol = Symbol::new("test_clause", var_vec!["A", "B"], var_vec!["X", "Y"]);

        let args = vec![Value::num(10), Value::num(20)];
        let env = Environment::for_symbol(&symbol, &args, &mut pgen).unwrap();
        let equiv = Equivalence::new();

        assert_eq!(
            env.get(&Variable::new("A"), &equiv).unwrap(),
            Value::num(10)
        );
        assert_eq!(
            env.get(&Variable::new("B"), &equiv).unwrap(),
            Value::num(20)
        );

        let x_value = env.get(&Variable::new("X"), &equiv).unwrap();
        let y_value = env.get(&Variable::new("Y"), &equiv).unwrap();

        assert!(x_value.placeholder_id().is_some());
        assert!(y_value.placeholder_id().is_some());
        assert_ne!(x_value, y_value);
    }

    #[test]
    fn test_clause_database() {
        let clause1 = Clause {
            head: Symbol::new("clause", var_vec!["A"], vec![]),
            body: Goal::Bool(true),
        };

        let clause2 = Clause {
            head: Symbol::new("clause", var_vec!["A", "B"], vec![]),
            body: Goal::Bool(false),
        };

        let clause3 = Clause {
            head: Symbol::new("clause", var_vec!["X"], vec![]),
            body: Goal::Bool(true),
        };

        let db = ClauseDatabase::new(vec![clause1.clone(), clause2.clone(), clause3.clone()]);
        let clauses_arity1 = db.get("clause", 1);
        let clauses_arity2 = db.get("clause", 2);
        let clauses_arity3 = db.get("clause", 3);

        assert_eq!(clauses_arity1, vec![clause1, clause3]);
        assert_eq!(clauses_arity2, vec![clause2]);
        assert!(clauses_arity3.is_empty());

        assert!(db.get("nonexistent", 1).is_empty());
    }

    #[test]
    fn test_set_representative() {
        let mut equiv = Equivalence::new();
        let mut pgen = PlaceholderGenerator::new();

        let x = Value::num(5);
        let y = Value::placeholder(&mut pgen);
        let z = Value::placeholder(&mut pgen);

        assert_eq!(equiv.set_representative(&x).unwrap(), x);
        assert_eq!(equiv.set_representative(&y).unwrap(), y);
        assert_eq!(equiv.set_representative(&z).unwrap(), z);

        equiv.unify(&y, &x).unwrap();

        assert_eq!(equiv.set_representative(&x).unwrap(), x);
        assert_eq!(equiv.set_representative(&y).unwrap(), x);
        assert_eq!(equiv.set_representative(&z).unwrap(), z);

        equiv.unify(&z, &y).unwrap();

        assert_eq!(equiv.set_representative(&x).unwrap(), x);
        assert_eq!(equiv.set_representative(&y).unwrap(), x);
        assert_eq!(equiv.set_representative(&z).unwrap(), x);
    }

    #[test]
    fn test_unification() {
        let mut equiv = Equivalence::new();
        let mut pgen = PlaceholderGenerator::new();

        let x = pgen.new_placeholder();
        let y = pgen.new_placeholder();

        equiv.unify(&x, &Value::Number(42)).unwrap();
        equiv.unify(&y, &x).unwrap();

        assert_eq!(equiv.set_representative(&y).unwrap(), Value::Number(42));
    }

    #[test]
    fn test_unification_fails() {
        let mut equiv = Equivalence::new();

        let x = Value::Number(5);
        let y = Value::Number(10);

        assert!(equiv.unify(&x, &y).is_err());
    }
}
