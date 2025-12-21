//! Execution engine.
//!
//! Contains the internal representation definitions and engine itself.

pub mod representation;

use crate::error::EngineError;
pub use representation::*;

/// An execution engine.
pub struct Engine {
    db: ClauseDatabase,
}

struct State {
    env: Environment,
    equiv: Equivalence,
    goal_stack: Vec<Goal>,
    choice_stack: Vec<Choice>,
    placeholder_gen: PlaceholderGenerator,
}

/// A Prolog query.
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
    pub fn new(program: Vec<Clause>) -> Self {
        let db = ClauseDatabase::new(program);

        Engine { db }
    }

    /// Execute the engine on the given query.
    pub fn execute(&self, query: Query) -> Result<Vec<(Environment, Equivalence)>, EngineError> {
        let mut placeholder_gen = PlaceholderGenerator::new();

        let mut state = State {
            env: Environment::for_query(query.local_vars, &mut placeholder_gen),
            equiv: Equivalence::new(),
            goal_stack: vec![query.goal],
            choice_stack: Vec::new(),
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
                    state.goal_stack.push(Goal::Bool(false));
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
                    state.goal_stack.clone(),
                );

                state.choice_stack.push(choice);
                state.goal_stack.push(*goal1);
            }

            Goal::Equivalence(var1, var2) => {
                let val1 = state.env.get(&var1, &state.equiv)?;
                let val2 = state.env.get(&var2, &state.equiv)?;

                if state.equiv.unify(&val1, &val2).is_err() {
                    state.goal_stack.push(Goal::Bool(false));
                }
            }

            Goal::Check { functor, arguments } => {
                self.handle_check(state, functor, arguments)?;
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

            Goal::Bool(true) => (),
            Goal::Bool(false) => {
                if let Some(choice) = state.choice_stack.pop() {
                    state.restore_choice(choice);
                } else {
                    state.env.clear();
                    state.goal_stack.clear();
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
        let val1 = state.env.get(&var1, &state.equiv)?;
        let val2 = state.env.get(&var2, &state.equiv)?;

        // Ensure both are numbers
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

        let result = op.evaluate(num1, num2);

        if !result {
            state.goal_stack.push(Goal::Bool(false));
        }

        Ok(())
    }

    fn handle_check(
        &self,
        state: &mut State,
        functor: String,
        arguments: Vec<Variable>,
    ) -> Result<(), EngineError> {
        let clauses = self.db.get(&functor, arguments.len());
        if clauses.is_empty() {
            return Err(EngineError::ClauseNotFound(functor, arguments.len()));
        }

        state.goal_stack.push(Goal::Restore(state.env.clone()));

        let clause = clauses.first().unwrap();

        for clause in clauses.iter().skip(1).rev() {
            let clause_env = Environment::from_clause(
                clause,
                &arguments,
                &state.env,
                &state.equiv,
                &mut state.placeholder_gen,
            )?;

            let choice = Choice::new(
                clause.body.clone(),
                clause_env,
                state.equiv.clone(),
                state.goal_stack.clone(),
            );

            state.choice_stack.push(choice);
        }

        state.env = Environment::from_clause(
            clause,
            &arguments,
            &state.env,
            &state.equiv,
            &mut state.placeholder_gen,
        )?;
        state.goal_stack.push(clause.body.clone());

        Ok(())
    }
}

#[cfg(test)]
mod tests {}
