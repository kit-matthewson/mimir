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
}

/// A solution returned by the engine after executing a query.
#[derive(Debug, Clone)]
pub struct Solution {
    env: Environment,
    equiv: Equivalence,
    truth_value: f64,
}

impl Solution {
    /// Create a solution from a given state.
    fn from_state(state: &State) -> Self {
        Solution {
            env: state.env.clone(),
            equiv: state.equiv.clone(),
            truth_value: state.truth_value,
        }
    }

    /// Gets the value of a variable in this solution.
    pub fn get(&self, var: &Variable) -> Option<Value> {
        self.env.get(var, &self.equiv).ok()
    }

    /// Gets the truth value of this solution.
    pub fn truth_value(&self) -> f64 {
        self.truth_value
    }
}

/// The current state of the engine during execution.
///
/// Contains:
/// - The current environment, which maps variables to values.
/// - The current equivalence, which maps terms to their unified representatives.
/// - The current truth value of the state, which is updated as goals are processed.
/// - A placeholder generator for creating new placeholders during execution.
#[derive(Debug, Clone)]
struct State {
    pub env: Environment,
    pub equiv: Equivalence,
    pub truth_value: f64,
    pub truth_threshold: f64,
    pub placeholder_gen: PlaceholderGenerator,
}

impl Default for State {
    fn default() -> Self {
        State {
            env: Environment::empty(),
            equiv: Equivalence::new(),
            truth_value: 1.0,
            truth_threshold: 0.01,
            placeholder_gen: PlaceholderGenerator::new(),
        }
    }
}

impl Engine {
    /// Create a new engine for a given program. Initialises the clause database.
    pub fn new(program: Vec<Clause>) -> Self {
        let db = ClauseDatabase::new(program);

        Engine { db }
    }

    /// Returns the clauses in the engine's database.
    pub fn clauses(&self) -> Vec<Clause> {
        self.db.clauses()
    }

    /// Execute the engine on the given query.
    pub fn execute(
        &self,
        query: Query,
        truth_threshold: f64,
    ) -> Result<Vec<Solution>, EngineError> {
        let mut placeholder_gen = PlaceholderGenerator::new();

        let state = State {
            env: Environment::for_query(&query, &mut placeholder_gen),
            equiv: Equivalence::new(),
            truth_value: 1.0,
            truth_threshold,
            placeholder_gen,
        };

        let final_states = self.handle_goal(query.goal, state)?;

        // Solutions are actually just variable bindings from the final states
        let mut solutions = final_states
            .iter()
            .map(Solution::from_state)
            .collect::<Vec<_>>();

        // Order solutions by truth value, highest first
        solutions.sort_by(|s1, s2| s2.truth_value.partial_cmp(&s1.truth_value).unwrap());

        Ok(solutions)
    }

    fn handle_goal(&self, goal: Goal, state: State) -> Result<Vec<State>, EngineError> {
        match goal {
            Goal::Conjunction(goal1, goal2) => {
                // Get all states from goal1
                let goal1_states = self.handle_goal(*goal1, state)?;

                // We now evaluate goal2 for each state returned by goal1, and combine all the results
                let mut all_states = Vec::new();
                for state1 in goal1_states {
                    let goal2_states = self.handle_goal(*goal2.clone(), state1)?;
                    all_states.extend(goal2_states);
                }

                Ok(all_states)
            }

            Goal::Disjunction(goal1, goal2) => {
                // Evaluate both branches independently
                let goal1_states = self.handle_goal(*goal1, state.clone())?;
                let goal2_states = self.handle_goal(*goal2, state)?;

                // Combine all states from both branches
                let mut all_states = goal1_states;
                all_states.extend(goal2_states);

                Ok(all_states)
            }

            Goal::Equivalence(var1, var2) => {
                let val1 = state.env.get(&var1, &state.equiv)?;
                let val2 = state.env.get(&var2, &state.equiv)?;

                let mut new_equiv = state.equiv.clone();

                match new_equiv.unify(&val1, &val2) {
                    Ok(_) => {
                        let mut new_state = state;
                        new_state.equiv = new_equiv;
                        Ok(vec![new_state])
                    }
                    Err(_) => Ok(vec![]),
                }
            }

            Goal::Check { functor, params } => self.handle_check(state, functor, params),

            Goal::Relation(var1, var2, op) => {
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

                if result { Ok(vec![state]) } else { Ok(vec![]) }
            }

            // Assignment is very similar to unification, only the second term is an expression that evaluates to a value rather than a variable.
            Goal::Assign(var, rhs) => {
                let val1 = state.env.get(&var, &state.equiv)?;
                let val2 = rhs.evaluate(&state.env, &state.equiv)?;

                let mut new_equiv = state.equiv.clone();

                match new_equiv.unify(&val1, &val2) {
                    Ok(_) => {
                        let mut new_state = state;
                        new_state.equiv = new_equiv;
                        Ok(vec![new_state])
                    }
                    Err(_) => Ok(vec![]),
                }
            }

            Goal::TruthExpr(expr) => {
                let val = expr.evaluate(&state.env, &state.equiv)?;

                let new_truth_value = state.truth_value.min(*val);

                if new_truth_value < state.truth_threshold {
                    Ok(vec![]) // Below threshold
                } else {
                    let mut new_state = state;
                    new_state.truth_value = new_truth_value;
                    Ok(vec![new_state])
                }
            }
        }
    }

    fn handle_check(
        &self,
        state: State,
        functor: String,
        params: Vec<Variable>,
    ) -> Result<Vec<State>, EngineError> {
        // Try and get clauses for the given functor and arity
        let clauses = self.db.get(&functor, params.len());
        if clauses.is_empty() {
            return Err(EngineError::ClauseNotFound(functor, params.len()));
        }

        let mut resultant_states = Vec::new();

        for clause in clauses {
            let mut clause_placeholder_gen = state.placeholder_gen.clone();

            let clause_env = Environment::for_symbol_with_params(
                clause.head(),
                &params,
                &state.env,
                &state.equiv,
                &mut clause_placeholder_gen,
            )?;

            let clause_state = State {
                env: clause_env,
                equiv: state.equiv.clone(),
                truth_value: state.truth_value,
                placeholder_gen: clause_placeholder_gen,
                truth_threshold: state.truth_threshold,
            };

            match self.handle_goal(clause.body().clone(), clause_state) {
                Ok(clause_result_states) => {
                    // The equivalent to Dewey's 'Restore' goal for the recursive method
                    for clause_result_state in clause_result_states {
                        let mut result_state = state.clone();
                        // Keep the equivalence from the clause execution
                        result_state.equiv = clause_result_state.equiv;
                        // Keep the truth value from the clause execution
                        result_state.truth_value = clause_result_state.truth_value;
                        resultant_states.push(result_state);
                    }
                }
                Err(_) => {
                    // This clause failed, try the next one
                    continue;
                }
            }
        }

        Ok(resultant_states)
    }
}

#[cfg(test)]
mod tests {
    use ordered_float::OrderedFloat;

    use crate::{assign, clause, lit, query, truth_expression, var, var_vec};

    use super::*;

    #[test]
    fn test_engine_simple_query() {
        let program = vec![clause!(is_ten(T1) { T2 } :- Goal::Conjunction(
            Box::new(Goal::Assign(Variable::new("T2"), RHSTerm::Num(OrderedFloat::from(10.0)))),
            Box::new(Goal::Equivalence(Variable::new("T1"), Variable::new("T2")))
        ))];

        let engine = Engine::new(program);

        // Query: is_ten(X)
        let query = Query {
            local_vars: var_vec![X],
            goal: Goal::Check {
                functor: "is_ten".to_string(),
                params: var_vec![X],
            },
        };

        let solutions = engine.execute(query.clone(), 0.01).unwrap();

        let mut results = vec![];
        for solution in solutions.iter() {
            let value = solution.get(&Variable::new("X")).unwrap();
            results.push(value);
        }

        assert_eq!(results.len(), 1);
        assert!(results.contains(&Value::Number(OrderedFloat::from(10.0))));

        // Query: is_ten(5) - should return no solutions because X can't be both 10 and 5
        let query_fail = Query {
            local_vars: var_vec![X],
            goal: Goal::Conjunction(
                Box::new(Goal::Check {
                    functor: "is_ten".to_string(),
                    params: var_vec![X],
                }),
                Box::new(Goal::Assign(
                    Variable::new("X"),
                    RHSTerm::Num(OrderedFloat::from(5.0)),
                )),
            ),
        };

        // The engine returns no solutions if unification fails
        let solutions = engine.execute(query_fail.clone(), 0.01).unwrap();
        assert_eq!(solutions.len(), 0);
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

        let engine = Engine::new(program);

        // Query: is_ten_or_five(X)
        let query = Query {
            local_vars: var_vec![X],
            goal: Goal::Check {
                functor: "is_ten_or_five".to_string(),
                params: var_vec![X],
            },
        };

        let solutions = engine.execute(query.clone(), 0.01).unwrap();

        let mut results = vec![];
        for solution in solutions.iter() {
            let value = solution.get(&Variable::new("X")).unwrap();
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

        let engine = Engine::new(vec![]);

        let state = State {
            env,
            equiv: Equivalence::new(),
            truth_value: 1.0,
            truth_threshold: 0.01,
            placeholder_gen: PlaceholderGenerator::new(),
        };

        // 10 = 10
        let result = engine.handle_goal(
            Goal::Equivalence(Variable::new("X"), Variable::new("Y")),
            state.clone(),
        );
        assert!(result.is_ok());
        assert!(!result.unwrap().is_empty());

        // Placeholder should unify with 10
        let result = engine.handle_goal(
            Goal::Equivalence(Variable::new("Z"), Variable::new("X")),
            state,
        );
        assert!(result.is_ok());
        assert!(!result.unwrap().is_empty());
    }

    #[test]
    fn test_invalid_equivalence_goals() {
        let engine = Engine::new(vec![]);
        let mut state = State::default();
        state.env.assign(&Variable::new("X"), Value::num(10));
        state.env.assign(&Variable::new("Y"), Value::num(5));

        // 5 cannot equal 10
        let result = engine.handle_goal(
            Goal::Equivalence(Variable::new("X"), Variable::new("Y")),
            state.clone(),
        );
        println!("{:?}", result);
        assert!(result.is_ok());
        assert!(result.unwrap().is_empty());

        // Variable Z does not exist in the environment
        let result = engine.handle_goal(
            Goal::Equivalence(Variable::new("Z"), Variable::new("X")),
            state.clone(),
        );
        assert!(result.is_err());

        let result = engine.handle_goal(
            Goal::Equivalence(Variable::new("X"), Variable::new("Z")),
            state,
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_truth_expr_eval() {
        // Setup environment with X = 0.1 and Y = 0.3
        let engine = Engine::new(vec![]);
        let mut state = State::default();
        state.env.assign(&Variable::new("X"), Value::num(0.1));
        state.env.assign(&Variable::new("Y"), Value::num(0.3));

        // Evaluate the truth value expression
        // Set X=0.3 and Y=0.1

        let result = engine.handle_goal(
            Goal::TruthExpr(Expression::Expr(
                Box::new(Expression::variable("X")),
                Box::new(Expression::variable("Y")),
                ArithmeticOp::Add,
            )),
            state,
        );

        assert!(result.is_ok());
        let states = result.unwrap();
        assert!(!states.is_empty());
        // Resultant truth value should be 0.4
        assert!((states.first().unwrap().truth_value - 0.4).abs() < f64::EPSILON);
    }

    #[test]
    fn test_handle_relation() {
        let engine = Engine::new(vec![]);

        let mut state = State::default();
        state.env.assign(&Variable::new("X"), Value::num(10));
        state.env.assign(&Variable::new("Y"), Value::num(5));

        // Test X > Y
        let result = engine.handle_goal(
            Goal::Relation(
                Variable::new("X"),
                Variable::new("Y"),
                RelationalOp::GreaterThan,
            ),
            state.clone(),
        );
        assert!(result.is_ok());
        assert!(!result.unwrap().is_empty());

        // Test X < Y
        let result = engine.handle_goal(
            Goal::Relation(
                Variable::new("X"),
                Variable::new("Y"),
                RelationalOp::LessThan,
            ),
            state,
        );
        assert!(result.is_ok());
        assert!(result.unwrap().is_empty());
    }

    #[test]
    fn test_handle_relation_nan() {
        let engine = Engine::new(vec![]);
        let mut pgen = PlaceholderGenerator::new();
        let mut state = State::default();
        state.env.assign(&Variable::new("X"), Value::num(10));
        state
            .env
            .assign(&Variable::new("Y"), pgen.new_placeholder());

        // X > Y and Y > X
        let result = engine.handle_goal(
            Goal::Relation(
                Variable::new("X"),
                Variable::new("Y"),
                RelationalOp::GreaterThan,
            ),
            state.clone(),
        );
        assert!(result.is_err());

        let result = engine.handle_goal(
            Goal::Relation(
                Variable::new("Y"),
                Variable::new("X"),
                RelationalOp::GreaterThan,
            ),
            state,
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_handle_check() {
        let program = vec![
            clause!(clause(X) { Y } :- Goal::Equivalence(Variable::new("X"), Variable::new("Y"))),
            clause!(clause(X) {Y} :- Goal::Relation(Variable::new("X"), Variable::new("Y"), RelationalOp::GreaterThan)),
        ];

        let engine = Engine::new(program);

        let mut state = State::default();
        state.env.assign(&Variable::new("X"), Value::num(10));
        state.env.assign(&Variable::new("Y"), Value::num(5));

        let result = engine.handle_check(state, "clause".to_string(), var_vec![X]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_program() {
        use crate::{check, clause, conjunction};

        let program = vec![
            clause!(edge(t1, t2) {} :- conjunction!(
                assign!(t1, RHSTerm::Sym(lit!(a))),
                assign!(t2, RHSTerm::Sym(lit!(b))),
                truth_expression!(1.0)
            )),
            clause!(edge(t1, t2) {} :- conjunction!(
                assign!(t1, RHSTerm::Sym(lit!(b))),
                assign!(t2, RHSTerm::Sym(lit!(c))),
                truth_expression!(1.0)
            )),
            clause!(edge(t1, t2) {} :- conjunction!(
                assign!(t1, RHSTerm::Sym(lit!(c))),
                assign!(t2, RHSTerm::Sym(lit!(d))),
                truth_expression!(1.0)
            )),
            clause!(path(A, B) {} :- check!(edge, A, B)),
            clause!(path(A, B) {} :- conjunction!(
                check!(edge, A, X),
                check!(path, X, B)
            )),
        ];

        let query = query!(path, a, X);

        let engine = Engine::new(program);

        let solutions = engine.execute(query.clone(), 0.01).unwrap();

        let mut results = vec![];
        for solution in solutions.iter() {
            let value = solution.get(&var!(X)).unwrap();
            results.push(value);
        }

        assert_eq!(
            results,
            vec![
                Value::Ground("b".into(), vec![]),
                Value::Ground("c".into(), vec![]),
                Value::Ground("d".into(), vec![])
            ]
        );
    }
}
