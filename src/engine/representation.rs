//! Internal Mini-Prolog representation.

use crate::{engine::state::*, error::EngineError};

/// Type for placeholder value IDs
type PlaceholderID = u32;
/// Type of numbers
type Number = i64;

/// A reference to a variable by name.
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

/// The value that a variable can take.
///
/// This may be an uninitialised 'placeholder' value, a number, or a ground term.
#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum Value {
    /// An i64 'Number' value.
    Number(Number),
    /// A ground term. A ground term is a term that does not contain any variables.
    /// Essentially, a functor and a list of parameter values.
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
    ///
    /// Returns `None` if this value is not a number.
    pub fn get_number(&self) -> Option<Number> {
        match self {
            Value::Number(n) => Some(*n),
            _ => None,
        }
    }

    /// Attempt to get the placeholder ID of this value.
    ///
    /// Returns `None` if this value is not a placeholder.
    pub fn get_placeholder_id(&self) -> Option<PlaceholderID> {
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
    ///
    /// # Example
    /// ```
    /// # use mimir::engine::RelationalOp;
    /// let op = RelationalOp::LessThan;
    /// assert!(op.evaluate(5, 10));
    /// assert!(!op.evaluate(10, 5));
    /// ```
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
    ///
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
///
/// Expressions can be numbers, variables, or binary expressions combining two sub-expressions with an operator.
///
/// # Example
/// ```
/// # use mimir::engine::{Expression, ArithmeticOp, Variable, Environment, Equivalence};
/// // 10 + (5 * 2)
/// let expr = Expression::binary(
///     Expression::number(10),
///     Expression::binary(
///         Expression::number(5),
///         Expression::number(2),
///         ArithmeticOp::Multiply,
///     ),
///     ArithmeticOp::Add,
/// );
/// let env = Environment::empty();
/// let equiv = Equivalence::new();
/// let result = expr.evaluate(&env, &equiv).unwrap();
/// assert_eq!(result, 20);
/// ```
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
    ///
    /// An environment and equivalence mapping are required to resolve variable values.
    pub fn evaluate(&self, env: &Environment, equiv: &Equivalence) -> Result<Number, EngineError> {
        match self {
            Expression::Num(n) => Ok(*n),
            Expression::Var(var) => {
                let val = env.get(var, equiv)?;

                if let Some(n) = val.get_number() {
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

/// Allows easy conversion from Number to Expression.
impl From<Number> for Expression {
    fn from(n: Number) -> Self {
        Expression::Num(n)
    }
}

/// Allows easy conversion from Variable to Expression.
impl From<Variable> for Expression {
    fn from(var: Variable) -> Self {
        Expression::Var(var)
    }
}

/// A term that can appear on the right-hand side of an assignment.
///
/// This can be a literal number, an arithmetic expression, or a symbol (clause head).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RHSTerm {
    /// A literal number.
    Num(Number),
    /// An arithmetic expression.
    Expr(Expression),
    /// A symbol (clause head).
    Sym(Symbol),
}

impl RHSTerm {
    /// Evaluate this term to a value given the environment.
    pub fn evaluate(&self, env: &Environment, equiv: &Equivalence) -> Result<Value, EngineError> {
        match self {
            RHSTerm::Num(n) => Ok(Value::Number(*n)),
            RHSTerm::Expr(expr) => {
                let result = expr.evaluate(env, equiv)?;
                Ok(Value::Number(result))
            }
            RHSTerm::Sym(sym) => {
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

/// The head of a clause with a name, parameters, and list of local variables.
///
/// Symbols are used to represent clause heads.
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

    /// Gets the arity (number of parameters) of this clause.
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

/// A Prolog query.
///
/// Queries contain a list of local variables (the variables to return) and a goal to execute.
#[derive(Clone, Debug)]
pub struct Query {
    /// Local variables of the query.
    pub local_vars: Vec<Variable>,
    /// The goal of the query.
    pub goal: Goal,
}

impl std::fmt::Display for Query {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?- {}", self.goal)
    }
}

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

        assert_eq!(n.get_number(), Some(10));
        assert_eq!(p.get_number(), None);

        assert_eq!(n.get_placeholder_id(), None);
        assert_eq!(p.get_placeholder_id(), Some(5));
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
        env.assign(&Variable::new("X"), Value::num(3));

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
        env.assign(&Variable::new("A"), Value::num(1));
        env.assign(&Variable::new("B"), Value::num(2));

        let equiv = Equivalence::new();

        let term = RHSTerm::Num(42);
        let value = term.evaluate(&env, &equiv).unwrap();
        assert_eq!(value, Value::num(42));

        let term = RHSTerm::Expr(Expression::binary(10, 5, ArithmeticOp::Add));
        let value = term.evaluate(&env, &equiv).unwrap();
        assert_eq!(value, Value::num(15));

        let symbol = Symbol::new("func", var_vec!["A", "B"], vec![]);
        let term = RHSTerm::Sym(symbol);
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

        assert!(x_value.get_placeholder_id().is_some());
        assert!(y_value.get_placeholder_id().is_some());
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
