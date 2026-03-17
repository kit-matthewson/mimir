//! Execution engine.
//!
//! Contains the internal representation definitions and engine itself.

mod representation;
mod state;

use crate::error::EngineError;

pub use representation::*;
pub use state::*;

/// An execution engine.
pub struct Engine {
    db: ClauseDatabase,
    /// Truth values below this threshold are considered false
    truth_threshold: f64,
}

/// The current state of the engine during execution.
///
/// Contains:
/// - The current environment, which maps variables to values.
/// - The current equivalence, which maps terms to their unified representatives.
struct State {
    env: Environment,
    equiv: Equivalence,
    goal_stack: Vec<Goal>,
    choice_stack: Vec<Choice>,
    truth_value: f64,
    placeholder_gen: PlaceholderGenerator,
}

impl State {
    pub fn restore_choice(&mut self, choice: Choice) {
        self.env = choice.env;
        self.equiv = choice.equiv;
        self.goal_stack = choice.goal_stack;
        self.goal_stack.push(choice.goal);
    }
}

impl Engine {
    /// Create a new engine from a given program. Initialises the clause database.
    pub fn new(program: Vec<Clause>, truth_threshold: f64) -> Self {
        let db = ClauseDatabase::new(program);

        Engine {
            db,
            truth_threshold,
        }
    }

    /// Execute the engine on the given query.
    pub fn execute(&self, query: Query) -> Result<Vec<(Environment, Equivalence)>, EngineError> {
        let mut placeholder_gen = PlaceholderGenerator::new();

        let mut state = State {
            env: Environment::for_query(&query, &mut placeholder_gen),
            equiv: Equivalence::new(),
            goal_stack: vec![query.goal],
            choice_stack: Vec::new(),
            truth_value: 1.0,
            placeholder_gen,
        };

        let mut solutions = Vec::new();

        loop {
            if let Some(goal) = state.goal_stack.pop() {
                self.handle_goal(goal, &mut state)?;
            } else {
                // Goal stack is empty, check termination conditions
                if state.env.is_empty() {
                    // All valid assignments found
                    break;
                } else {
                    solutions.push((state.env.clone(), state.equiv.clone()));

                    // We might be able to find another assignment
                    state.goal_stack.push(Goal::TruthValue(0.0));
                }
            }
        }

        Ok(solutions)
    }

    fn handle_goal(&self, goal: Goal, state: &mut State) -> Result<(), EngineError> {
        match goal {
            Goal::Conjunction(goal1, goal2) => {
                state.goal_stack.push(*goal2);
                state.goal_stack.push(*goal1);
            }

            Goal::Disjunction(goal1, goal2) => {
                let choice = Choice::new(
                    *goal2,
                    state.env.clone(),
                    state.equiv.clone(),
                    state.truth_value,
                    state.goal_stack.clone(),
                );

                state.choice_stack.push(choice);
                state.goal_stack.push(*goal1);
            }

            Goal::Equivalence(var1, var2) => {
                let val1 = state.env.get(&var1, &state.equiv)?;
                let val2 = state.env.get(&var2, &state.equiv)?;

                if state.equiv.unify(&val1, &val2).is_err() {
                    state.goal_stack.push(Goal::TruthValue(0.0));
                }
            }

            Goal::Check { functor, params } => {
                self.handle_check(state, functor, params)?;
            }

            Goal::Restore(new_env) => state.env = new_env,

            Goal::Relation(var1, var2, op) => {
                self.handle_relation(state, var1, var2, op)?;
            }

            Goal::Assign(var, rhs) => {
                let val1 = state.env.get(&var, &state.equiv)?;
                let val2 = rhs.evaluate(&state.env, &state.equiv)?;
                state.equiv.unify(&val1, &val2)?;
            }

            Goal::TruthValueExpr(expr) => {
                let val = expr.evaluate(&state.env, &state.equiv)?;
                state.goal_stack.push(Goal::TruthValue(*val));
            }

            Goal::TruthValue(t) => {
                // Update the current truth value
                state.truth_value = state.truth_value.min(t);

                if state.truth_value < self.truth_threshold {
                    // Backtrack if there are choices available, otherwise clear the environment and goal stack to terminate
                    if let Some(choice) = state.choice_stack.pop() {
                        state.restore_choice(choice);
                    } else {
                        state.env.clear();
                        state.goal_stack.clear();
                    }
                }
            }
        }

        Ok(())
    }

    fn handle_relation(
        &self,
        state: &mut State,
        var1: Variable,
        var2: Variable,
        op: RelationalOp,
    ) -> Result<(), EngineError> {
        // Get the values of both variables
        let val1 = state.env.get(&var1, &state.equiv)?;
        let val2 = state.env.get(&var2, &state.equiv)?;

        // Ensure both are numbers
        let num1 = if let Some(num) = val1.get_number() {
            num
        } else {
            return Err(EngineError::NotANumber(var1));
        };

        let num2 = if let Some(num) = val2.get_number() {
            num
        } else {
            return Err(EngineError::NotANumber(var2));
        };

        // Evaluate the relation
        let result = op.evaluate(num1, num2);

        // If the relation is false, push a failure goal
        if !result {
            state.goal_stack.push(Goal::TruthValue(0.0));
        }

        Ok(())
    }

    fn handle_check(
        &self,
        state: &mut State,
        functor: String,
        params: Vec<Variable>,
    ) -> Result<(), EngineError> {
        // Try and get clauses for the given functor and arity
        let clauses = self.db.get(&functor, params.len());
        if clauses.is_empty() {
            return Err(EngineError::ClauseNotFound(functor, params.len()));
        }

        // Push a restore goal to revert the environment after trying all clauses
        state.goal_stack.push(Goal::Restore(state.env.clone()));

        // Push choices for all but the first clause
        // The first clause is handled directly so we do not have not make an extra choice
        for clause in clauses.iter().skip(1).rev() {
            let clause_env = Environment::for_symbol_with_params(
                clause.head(),
                &params,
                &state.env,
                &state.equiv,
                &mut state.placeholder_gen,
            )?;

            let choice = Choice::new(
                clause.body().clone(),
                clause_env,
                state.equiv.clone(),
                state.truth_value,
                state.goal_stack.clone(),
            );

            state.choice_stack.push(choice);
        }

        // Handle the first clause directly
        let first_clause = clauses.first().unwrap();

        state.env = Environment::for_symbol_with_params(
            first_clause.head(),
            &params,
            &state.env,
            &state.equiv,
            &mut state.placeholder_gen,
        )?;

        state.goal_stack.push(first_clause.body().clone());

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ordered_float::OrderedFloat;

    use crate::{clause, var_vec};

    use super::*;

    #[test]
    fn test_restore_choice() {
        let mut state = State {
            env: Environment::empty(),
            equiv: Equivalence::new(),
            goal_stack: vec![Goal::Check {
                functor: "some_goal".to_string(),
                params: var_vec!["X"],
            }],
            choice_stack: Vec::new(),
            truth_value: 1.0,
            placeholder_gen: PlaceholderGenerator::new(),
        };

        let choice = Choice::new(
            Goal::Assign(Variable::new("X"), RHSTerm::Num(OrderedFloat::from(10.0))),
            Environment::empty(),
            Equivalence::new(),
            1.0,
            vec![Goal::Check {
                functor: "some_goal".to_string(),
                params: var_vec!["X"],
            }],
        );

        state.restore_choice(choice);

        assert_eq!(state.goal_stack.len(), 2);
        assert!(matches!(state.goal_stack[0], Goal::Check { .. }));
        assert!(matches!(state.goal_stack[1], Goal::Assign(_, _)));
    }

    #[test]
    fn test_engine_simple_query() {
        let program = vec![clause!(is_ten(T1) { T2 } :- Goal::Conjunction(
            Box::new(Goal::Assign(Variable::new("T2"), RHSTerm::Num(OrderedFloat::from(10.0)))),
            Box::new(Goal::Equivalence(Variable::new("T1"), Variable::new("T2")))
        ))];

        let engine = Engine::new(program, 0.01);

        // Query: is_ten(X)
        let query = Query {
            local_vars: var_vec!["X"],
            goal: Goal::Check {
                functor: "is_ten".to_string(),
                params: var_vec!["X"],
            },
        };

        let solutions = engine.execute(query.clone()).unwrap();

        let mut results = vec![];
        for (env, equiv) in solutions.iter() {
            let value = env.get(&Variable::new("X"), equiv).unwrap();
            results.push(value);
        }

        assert_eq!(results.len(), 1);
        assert!(results.contains(&Value::Number(OrderedFloat::from(10.0))));

        // Query: is_ten(5)
        let query_fail = Query {
            local_vars: var_vec!["X"],
            goal: Goal::Conjunction(
                Box::new(Goal::Check {
                    functor: "is_ten".to_string(),
                    params: var_vec!["X"],
                }),
                Box::new(Goal::Assign(
                    Variable::new("X"),
                    RHSTerm::Num(OrderedFloat::from(5.0)),
                )),
            ),
        };

        // The engine currently returns an error if terms cannot be unified
        let solutions = engine.execute(query_fail.clone());
        assert!(solutions.is_err());
    }

    #[test]
    fn test_engine_disjunction() {
        // Program:
        // is_ten_or_five(T1) { T2, T3 } :-
        //     (T2 = 10, T1 = T2) ;
        //     (T3 = 5, T1 = T3).
        let program = vec![clause!(is_ten_or_five(T1) { T2, T3 } :- Goal::Disjunction(
        Box::new(Goal::Conjunction(
            Box::new(Goal::Assign(Variable::new("T2"), RHSTerm::Num(OrderedFloat::from(10.0)))),
            Box::new(Goal::Equivalence(Variable::new("T1"), Variable::new("T2")))
        )),
        Box::new(Goal::Conjunction(
            Box::new(Goal::Assign(Variable::new("T3"), RHSTerm::Num(OrderedFloat::from(5.0)))),
            Box::new(Goal::Equivalence(Variable::new("T1"), Variable::new("T3")))
        ))))];

        let engine = Engine::new(program, 0.01);

        // Query: is_ten_or_five(X)
        let query = Query {
            local_vars: var_vec!["X"],
            goal: Goal::Check {
                functor: "is_ten_or_five".to_string(),
                params: var_vec!["X"],
            },
        };

        let solutions = engine.execute(query.clone()).unwrap();

        let mut results = vec![];
        for (env, equiv) in solutions.iter() {
            let value = env.get(&Variable::new("X"), equiv).unwrap();
            results.push(value);
        }

        assert_eq!(results.len(), 2);
        assert!(results.contains(&Value::Number(OrderedFloat::from(10.0))));
        assert!(results.contains(&Value::Number(OrderedFloat::from(5.0))));
    }

    #[test]
    fn test_equivalence_goals() {
        let mut pgen = PlaceholderGenerator::new();

        let mut env = Environment::empty();
        env.assign(&Variable::new("X"), Value::num(10));
        env.assign(&Variable::new("Y"), Value::num(10));
        env.assign(&Variable::new("Z"), pgen.new_placeholder());

        let engine = Engine::new(vec![], 0.01);

        let mut state = State {
            env,
            equiv: Equivalence::new(),
            goal_stack: Vec::new(),
            choice_stack: Vec::new(),
            truth_value: 1.0,
            placeholder_gen: PlaceholderGenerator::new(),
        };

        // 10 = 10
        let result = engine.handle_goal(
            Goal::Equivalence(Variable::new("X"), Variable::new("Y")),
            &mut state,
        );
        assert!(result.is_ok());
        assert_eq!(state.goal_stack.len(), 0);

        // Placeholder should unify with 10
        let result = engine.handle_goal(
            Goal::Equivalence(Variable::new("Z"), Variable::new("X")),
            &mut state,
        );
        assert!(result.is_ok());
        assert_eq!(state.goal_stack.len(), 0);
    }

    #[test]
    fn test_invalid_equivalence_goals() {
        // Setup environment with X and Y
        let mut env = Environment::empty();
        env.assign(&Variable::new("X"), Value::num(10));
        env.assign(&Variable::new("Y"), Value::num(5));

        let engine = Engine::new(vec![], 0.01);

        let mut state = State {
            env,
            equiv: Equivalence::new(),
            goal_stack: Vec::new(),
            choice_stack: Vec::new(),
            truth_value: 1.0,
            placeholder_gen: PlaceholderGenerator::new(),
        };

        // 5 cannot equal 10
        let result = engine.handle_goal(
            Goal::Equivalence(Variable::new("X"), Variable::new("Y")),
            &mut state,
        );
        println!("{:?}", result);
        assert!(result.is_ok());
        assert_eq!(state.goal_stack.len(), 1);
        assert!(matches!(state.goal_stack[0], Goal::TruthValue(0.0)));

        // Variable Z does not exist in the environment
        let result = engine.handle_goal(
            Goal::Equivalence(Variable::new("Z"), Variable::new("X")),
            &mut state,
        );
        assert!(result.is_err());

        let result = engine.handle_goal(
            Goal::Equivalence(Variable::new("X"), Variable::new("Z")),
            &mut state,
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_truth_expr_eval() {
        // Setup environment with X = 0.1 and Y = 0.3
        let mut env = Environment::empty();
        env.assign(&Variable::new("X"), Value::num(0.1));
        env.assign(&Variable::new("Y"), Value::num(0.3));

        let engine = Engine::new(vec![], 0.01);
        let mut state = State {
            env,
            equiv: Equivalence::new(),
            goal_stack: Vec::new(),
            choice_stack: Vec::new(),
            truth_value: 1.0,
            placeholder_gen: PlaceholderGenerator::new(),
        };

        // Evaluate the truth value expression
        // Set X=0.3 and Y=0.1

        let result = engine.handle_goal(
            Goal::TruthValueExpr(Expression::Expr(
                Box::new(Expression::variable("X")),
                Box::new(Expression::variable("Y")),
                ArithmeticOp::Add,
            )),
            &mut state,
        );

        assert!(result.is_ok());
        assert_eq!(state.goal_stack.len(), 1);
        assert!(
            matches!(state.goal_stack[0], Goal::TruthValue(t) if (t - 0.4).abs() < f64::EPSILON)
        );
    }

    #[test]
    fn test_handle_relation() {
        let mut env = Environment::empty();
        env.assign(&Variable::new("X"), Value::num(10));
        env.assign(&Variable::new("Y"), Value::num(5));

        let engine = Engine::new(vec![], 0.01);

        let mut state = State {
            env,
            equiv: Equivalence::new(),
            goal_stack: Vec::new(),
            choice_stack: Vec::new(),
            truth_value: 1.0,
            placeholder_gen: PlaceholderGenerator::new(),
        };

        // Test X > Y
        let result = engine.handle_relation(
            &mut state,
            Variable::new("X"),
            Variable::new("Y"),
            RelationalOp::GreaterThan,
        );
        assert!(result.is_ok());
        assert_eq!(state.goal_stack.len(), 0);
        assert!((state.truth_value - 1.0).abs() < f64::EPSILON);

        // Test X < Y
        let result = engine.handle_relation(
            &mut state,
            Variable::new("X"),
            Variable::new("Y"),
            RelationalOp::LessThan,
        );
        assert!(result.is_ok());
        assert_eq!(state.goal_stack.len(), 1);
        assert!(matches!(state.goal_stack[0], Goal::TruthValue(0.0)));
    }

    #[test]
    fn test_handle_relation_nan() {
        let mut pgen = PlaceholderGenerator::new();

        let mut env = Environment::empty();
        env.assign(&Variable::new("X"), Value::num(10));
        env.assign(&Variable::new("Y"), pgen.new_placeholder());

        let engine = Engine::new(vec![], 0.01);

        let mut state = State {
            env,
            equiv: Equivalence::new(),
            goal_stack: Vec::new(),
            choice_stack: Vec::new(),
            truth_value: 1.0,
            placeholder_gen: PlaceholderGenerator::new(),
        };

        // X > Y and Y > X
        let result = engine.handle_relation(
            &mut state,
            Variable::new("X"),
            Variable::new("Y"),
            RelationalOp::GreaterThan,
        );
        assert!(result.is_err());

        let result = engine.handle_relation(
            &mut state,
            Variable::new("Y"),
            Variable::new("X"),
            RelationalOp::GreaterThan,
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_handle_check() {
        let program = vec![
            clause!(clause(X) { Y } :- Goal::Equivalence(Variable::new("X"), Variable::new("Y"))),
            clause!(clause(X) {Y} :- Goal::Relation(Variable::new("X"), Variable::new("Y"), RelationalOp::GreaterThan)),
        ];

        let mut env = Environment::empty();
        env.assign(&Variable::new("X"), Value::num(10));
        env.assign(&Variable::new("Y"), Value::num(5));

        let engine = Engine::new(program, 0.01);

        let mut state = State {
            env,
            equiv: Equivalence::new(),
            goal_stack: Vec::new(),
            choice_stack: Vec::new(),
            truth_value: 1.0,
            placeholder_gen: PlaceholderGenerator::new(),
        };

        let result = engine.handle_check(&mut state, "clause".to_string(), var_vec!["X"]);
        println!("{:?}", result);
        assert!(result.is_ok());
        assert_eq!(state.choice_stack.len(), 1);
        assert_eq!(state.goal_stack.len(), 2);
        assert!(matches!(state.goal_stack[1], Goal::Equivalence(_, _)));

        // Should fail if we ask for the wrong arity
        let result = engine.handle_check(&mut state, "clause".to_string(), var_vec!["X", "Y"]);
        assert!(result.is_err());
    }
}
