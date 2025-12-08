//! Mini-Prolo Execution engine
//!
//! Based on that from Dewey and Hardekopf in 'The Mini-Prolog Language'.

use crate::{engine::representation::*, error::EngineError};

/// An execution engine.
pub struct Engine {
    db: ClauseDatabase,
}

impl Engine {
    /// Create a new engine from a given program. Initialises the clause database.
    pub fn new(program: Vec<Clause>) -> Self {
        let db = ClauseDatabase::new(program);

        Engine { db }
    }

    /// Execute the engine on the given query.
    pub fn execute(&self, query: Symbol) -> Result<Vec<Environment>, EngineError> {
        let mut env = Environment::new(&query, &Vec::new())
            .expect("could not construct environment for query");
        let mut equiv = Equivalence::new();
        let mut goal_stack: Vec<Goal> = Vec::new();
        let mut choice_stack: Vec<Choice> = Vec::new();

        let mut solutions = Vec::new();
        let mut finished = false;

        while !finished {
            if let Some(goal) = goal_stack.pop() {
                match goal {
                    Goal::Conjunction(goal1, goal2) => {
                        goal_stack.push(*goal2);
                        goal_stack.push(*goal1);
                    }

                    Goal::Disjunction(goal1, goal2) => {
                        let choice = Choice::new(*goal2, env.clone(), equiv, goal_stack.clone());
                        choice_stack.push(choice);
                        goal_stack.push(*goal1);
                    }

                    Goal::Equivalence(var1, var2) => {
                        let val1 = env.get(&var1)?;
                        let val2 = env.get(&var2)?;

                        if equiv.unify(&val1, &val2).is_err() {
                            goal_stack.push(Goal::Bool(false));
                        }
                    }

                    Goal::Check { functor, arguments } => {
                        let clauses = self.db.get(&functor, arguments.len());
                        if clauses.is_empty() {
                            return Err(EngineError::ClauseNotFound(functor, arguments.len()));
                        }

                        goal_stack.push(Goal::Restore(env.clone()));

                        let clause = clauses.get(1).unwrap();
                        goal_stack.push(clause.body.clone());

                        for clause in clauses.iter().rev() {
                            let clause_env = Environment::from_clause(clause, &env)
                                .expect("could not construct environment");

                            let choice = Choice::new(
                                clause.body.clone(),
                                clause_env,
                                equiv,
                                goal_stack.clone(),
                            );

                            choice_stack.push(choice);
                        }

                        env = Environment::from_clause(clause, &env)
                            .expect("could not construct environment");
                        goal_stack.push(clause.body.clone());
                    }
                    Goal::Restore(new_env) => env = new_env,

                    Goal::Relation(var1, var2, op) => {
                        let val1 = env.get(&var1)?;
                        let val2 = env.get(&var2)?;

                        let num1 = if let Some(num) = val1.number() {
                            num
                        } else {
                            return Err(EngineError::NotANumber(var1));
                        };

                        let num2 = if let Some(num) = val2.number() {
                            num
                        } else {
                            return Err(EngineError::NotANumber(var2));
                        };

                        if !op.evaluate(num1, num2) {
                            goal_stack.push(Goal::Bool(false));
                        }
                    }

                    Goal::Assign(var, rhs) => {
                        let val1 = env.get(&var)?;
                        let val2 = rhs.evaluate(&env);

                        equiv.unify(&val1, &val2)?;
                    }

                    Goal::Bool(true) => (),
                    Goal::Bool(false) => {
                        if choice_stack.is_empty() {
                            env.clear();
                            goal_stack.clear();
                        } else {
                            let choice = choice_stack.pop().unwrap(); // Unwrap is ok since we just check for empty
                            env = choice.env;
                            equiv = choice.equiv;
                            goal_stack = choice.goal_stack;
                            goal_stack.push(choice.goal);
                        }
                    }
                }
            } else {
                // Goal stack is empty, check termination conditions
                if env.is_empty() {
                    // All valid assignments found
                    finished = true;
                } else {
                    solutions.push(env.clone());
                    // We might be able to find another assignment
                    goal_stack.push(Goal::Bool(false));
                }
            }
        }

        Ok(solutions)
    }
}
