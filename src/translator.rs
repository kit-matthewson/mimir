//! Provides functions to translate a Prolog AST into the internal Mini-Prolog representation.
//!
//! This module implements the translation phase that converts user-facing Prolog syntax
//! into the simplified internal representation used by the Mini-Prolog engine.

use crate::{engine, error::TranslationError, parser::ast};
use std::collections::HashSet;

/// Translation state for managing unique variable names.
struct TranslationState {
    /// Counter for generating unique temporary variable names.
    temp_var_counter: usize,
    /// Counter for generating unique wildcard variable names.
    wildcard_counter: usize,
}

/// Translates a single AST clause into the internal engine representation.
pub fn translate_clause(clause: ast::Clause) -> Result<engine::Clause, TranslationError> {
    let mut state = TranslationState {
        temp_var_counter: 0,
        wildcard_counter: 0,
    };

    // Normalise head by replacing non-variable terms with temp variables and generating unification goals
    let (params, head_unification_goals) = translate_clause_head(&clause.head, &mut state)?;

    // Translate body goals, potentially creating more temporary variables
    let body_goals = translate_clause_body(&clause.body, &clause.fuzzy_expr, &mut state)?;

    // Combine head unification goals with body by prefixing generated
    // assignments in front of the translated body goal.
    let combined_body = head_unification_goals
        .into_iter()
        .rev()
        .fold(body_goals, |acc, goal| {
            engine::Goal::Conjunction(Box::new(goal), Box::new(acc))
        });

    // Create local and wild variable names for the clause
    let temp_vars = (0..state.temp_var_counter).map(|i| format!("_T{}", i));
    let wildcard_vars = (0..state.wildcard_counter).map(|i| format!("_W{}", i));

    let mut local_vars: Vec<engine::Variable> = temp_vars
        .chain(wildcard_vars)
        .map(engine::Variable::new)
        .collect();

    // Add any variables used in the body that aren't in the head parameters
    let body_vars = collect_body_variables(&clause.body);
    let param_names: HashSet<String> = params.iter().map(|v| v.to_string()).collect();
    for var_name in body_vars {
        if !param_names.contains(&var_name) {
            local_vars.push(engine::Variable::new(&var_name));
        }
    }

    // Create the final clause
    let head_symbol = engine::Symbol::new(&clause.head.functor, params, local_vars);

    Ok(engine::Clause::new(head_symbol, combined_body))
}

/// Translate a query (goal) from an AST goal to an engine query.
pub fn translate_query(query: ast::Goal) -> Result<engine::Query, TranslationError> {
    let mut state = TranslationState {
        temp_var_counter: 0,
        wildcard_counter: 0,
    };

    let goal = translate_goal(&query, &mut state)?;

    let goal_vars = collect_body_variables(&[query]);
    let temp_vars = (0..state.temp_var_counter).map(|i| format!("_T{}", i));
    let wildcard_vars = (0..state.wildcard_counter).map(|i| format!("_W{}", i));

    let local_vars: Vec<engine::Variable> = temp_vars
        .chain(wildcard_vars)
        .map(engine::Variable::new)
        .chain(goal_vars.into_iter().map(engine::Variable::new))
        .collect();

    Ok(engine::Query { local_vars, goal })
}

/// Translate the clause head by replacing non-variable terms with temporary variables and generating unification goals.
fn translate_clause_head(
    head: &ast::Compound,
    state: &mut TranslationState,
) -> Result<(Vec<engine::Variable>, Vec<engine::Goal>), TranslationError> {
    let mut params = Vec::new();
    let mut unification_goals = Vec::new();

    for param in &head.params {
        match param {
            ast::Term::Var(var) => {
                // Variables go directly into parameters
                match var {
                    ast::Variable::Var(name) => {
                        params.push(engine::Variable::new(name.clone()));
                    }
                    ast::Variable::Wildcard => {
                        // Each wildcard gets a unique variable
                        let wildcard_var = format!("_W{}", state.wildcard_counter);
                        state.wildcard_counter += 1;
                        params.push(engine::Variable::new(wildcard_var));
                    }
                }
            }
            _ => {
                // Non-variable terms: create a temp variable and add unification goal
                let temp_var = format!("_T{}", state.temp_var_counter);
                state.temp_var_counter += 1;
                let temp_engine_var = engine::Variable::new(&temp_var);

                params.push(temp_engine_var.clone());

                // Convert the term to an RHSTerm and create an assignment goal
                let rhs_term = term_to_rhs_term(param, state)?;
                unification_goals.push(engine::Goal::Assign(temp_engine_var, rhs_term));
            }
        }
    }

    Ok((params, unification_goals))
}

/// Translate the clause body goals, handling any necessary temporary variable generation.
fn translate_clause_body(
    body: &[ast::Goal],
    fuzzy_expr: &Option<ast::ArithExpr>,
    state: &mut TranslationState,
) -> Result<engine::Goal, TranslationError> {
    let fuzzy_goal = fuzzy_expr
        .as_ref()
        .map(|expr| engine::Goal::TruthExpr(translate_arith_expr(expr, state)));

    if body.is_empty() {
        return Ok(
            fuzzy_goal.unwrap_or_else(|| engine::Goal::TruthExpr(engine::Expression::num(1.0)))
        );
    }

    // Convert each goal and combine with conjunction
    let mut goals_iter = body.iter();
    let first_goal = translate_goal(goals_iter.next().expect("body is not empty"), state)?;

    goals_iter
        .try_fold(first_goal, |acc, goal| {
            let translated = translate_goal(goal, state)?;
            Ok(engine::Goal::Conjunction(
                Box::new(acc),
                Box::new(translated),
            ))
        })
        .map(|combined_body| {
            if let Some(fuzzy_goal) = fuzzy_goal {
                engine::Goal::Conjunction(Box::new(combined_body), Box::new(fuzzy_goal))
            } else {
                combined_body
            }
        })
}

/// Translate a single AST goal to an engine goal.
fn translate_goal(
    goal: &ast::Goal,
    state: &mut TranslationState,
) -> Result<engine::Goal, TranslationError> {
    match goal {
        ast::Goal::Relation(left, relational_op, right) => {
            // Relation operands must be variables for the engine. Non-variable
            // terms are normalised into temp variables with assignment goals.
            let (left_var, mut left_pre_goals) = term_to_variable_for_relation(left, state)?;
            let (right_var, right_pre_goals) = term_to_variable_for_relation(right, state)?;
            let engine_op = translate_relational_op(relational_op);
            let mut relation_goal = engine::Goal::Relation(left_var, right_var, engine_op);

            left_pre_goals.extend(right_pre_goals);

            // Preserve source order: evaluate generated assignments first,
            // then evaluate the relation itself.
            for pre_goal in left_pre_goals.into_iter().rev() {
                relation_goal =
                    engine::Goal::Conjunction(Box::new(pre_goal), Box::new(relation_goal));
            }

            Ok(relation_goal)
        }
        ast::Goal::Assign(variable, rhs) => {
            let engine_var = ast_variable_to_engine(variable, state);
            let rhs_term = translate_rhs(rhs, state)?;
            Ok(engine::Goal::Assign(engine_var, rhs_term))
        }
        ast::Goal::Check(compound) => {
            let functor = compound.functor.clone();
            let mut params = Vec::new();
            let mut pre_goals = Vec::new();

            // When a compound term is used as a goal, we need to ensure all its parameters are variables.
            // Produce assignment goals for non-variable parameters
            for term in &compound.params {
                let (var, param_pre_goals) = term_to_variable_for_relation(term, state)?;
                params.push(var);
                pre_goals.extend(param_pre_goals);
            }

            let mut check_goal = engine::Goal::Check { functor, params };
            for pre_goal in pre_goals.into_iter().rev() {
                check_goal = engine::Goal::Conjunction(Box::new(pre_goal), Box::new(check_goal));
            }

            Ok(check_goal)
        }
    }
}

/// Convert a term used in a relation to a variable.
///
/// If the term is not already a variable, this allocates a temporary variable
/// and emits an assignment goal so the relation can reference that variable.
fn term_to_variable_for_relation(
    term: &ast::Term,
    state: &mut TranslationState,
) -> Result<(engine::Variable, Vec<engine::Goal>), TranslationError> {
    match term {
        ast::Term::Var(var) => Ok((ast_variable_to_engine(var, state), vec![])),
        _ => {
            let temp_var = format!("_T{}", state.temp_var_counter);
            state.temp_var_counter += 1;

            let temp_engine_var = engine::Variable::new(&temp_var);
            let rhs_term = term_to_rhs_term(term, state)?;
            let assign_goal = engine::Goal::Assign(temp_engine_var.clone(), rhs_term);

            Ok((temp_engine_var, vec![assign_goal]))
        }
    }
}

/// Convert an AST term to a variable, creating a temp variable if needed.
/// Lists are desugared to cons structures inline.
fn term_to_variable(term: &ast::Term, state: &mut TranslationState) -> engine::Variable {
    match term {
        ast::Term::Var(var) => ast_variable_to_engine(var, state),
        ast::Term::List(_) | ast::Term::Compound(_) | ast::Term::Atom(_) | ast::Term::Num(_) => {
            // Any non-variable term gets a temp variable
            let temp_var = format!("_T{}", state.temp_var_counter);
            state.temp_var_counter += 1;
            engine::Variable::new(temp_var)
        }
    }
}

/// Convert a list to a cons-cell term recursively.
fn desugar_list_to_term(items: &[ast::Term]) -> ast::Term {
    items.iter().rfold(
        ast::Term::Atom(ast::Atom {
            name: "nil".to_string(),
        }),
        |acc, item| {
            ast::Term::Compound(ast::Compound {
                functor: ".".to_string(),
                params: vec![item.clone(), acc],
            })
        },
    )
}

/// Convert an AST variable to an engine variable.
fn ast_variable_to_engine(var: &ast::Variable, state: &mut TranslationState) -> engine::Variable {
    match var {
        ast::Variable::Var(name) => engine::Variable::new(name.clone()),
        ast::Variable::Wildcard => {
            let wildcard_var = format!("_W{}", state.wildcard_counter);
            state.wildcard_counter += 1;
            engine::Variable::new(wildcard_var)
        }
    }
}

/// Convert an AST term to an engine RHSTerm.
/// Lists are desugared to cons structures inline during this conversion.
fn term_to_rhs_term(
    term: &ast::Term,
    state: &mut TranslationState,
) -> Result<engine::RHSTerm, TranslationError> {
    match term {
        ast::Term::Num(n) => Ok(engine::RHSTerm::Num(*n)),
        ast::Term::Atom(atom) => {
            // An atom is a symbol with no parameters
            let symbol = engine::Symbol::new(&atom.name, vec![], vec![]);
            Ok(engine::RHSTerm::Sym(symbol))
        }
        ast::Term::Var(var) => {
            // A variable is wrapped in a symbol
            let engine_var = ast_variable_to_engine(var, state);
            let symbol = engine::Symbol::new("", vec![engine_var], vec![]);
            Ok(engine::RHSTerm::Sym(symbol))
        }
        ast::Term::Compound(compound) => {
            let params: Vec<engine::Variable> = compound
                .params
                .iter()
                .map(|t| term_to_variable(t, state))
                .collect();

            let symbol = engine::Symbol::new(&compound.functor, params, vec![]);
            Ok(engine::RHSTerm::Sym(symbol))
        }
        ast::Term::List(items) => {
            // Desugar list into cons structure and convert to RHSTerm
            let desugared = desugar_list_to_term(items);
            term_to_rhs_term(&desugared, state)
        }
    }
}

/// Translate an AST RHS to an engine RHSTerm.
fn translate_rhs(
    rhs: &ast::RHS,
    state: &mut TranslationState,
) -> Result<engine::RHSTerm, TranslationError> {
    match rhs {
        ast::RHS::Compound(compound) => {
            let params: Vec<engine::Variable> = compound
                .params
                .iter()
                .map(|t| term_to_variable(t, state))
                .collect();

            let symbol = engine::Symbol::new(&compound.functor, params, vec![]);
            Ok(engine::RHSTerm::Sym(symbol))
        }
        ast::RHS::Expr(expr) => {
            let engine_expr = translate_arith_expr(expr, state);
            Ok(engine::RHSTerm::Expr(engine_expr))
        }
    }
}

/// Translate an AST arithmetic expression to an engine expression.
fn translate_arith_expr(expr: &ast::ArithExpr, state: &mut TranslationState) -> engine::Expression {
    match expr {
        ast::ArithExpr::Num(n) => engine::Expression::Num(*n),
        ast::ArithExpr::Var(var) => {
            let engine_var = ast_variable_to_engine(var, state);
            engine::Expression::Var(engine_var)
        }
        ast::ArithExpr::Expr(left, op, right) => {
            let left_expr = translate_arith_expr(left, state);
            let right_expr = translate_arith_expr(right, state);
            let engine_op = translate_arith_op(op);
            engine::Expression::Expr(Box::new(left_expr), Box::new(right_expr), engine_op)
        }
    }
}

/// Translate an AST relational operator to an engine relational operator.
fn translate_relational_op(op: &ast::RelationalOp) -> engine::RelationalOp {
    match op {
        ast::RelationalOp::LessThan => engine::RelationalOp::LessThan,
        ast::RelationalOp::LessThanEqual => engine::RelationalOp::LessThanEqual,
        ast::RelationalOp::GreaterThan => engine::RelationalOp::GreaterThan,
        ast::RelationalOp::GreaterThanEqual => engine::RelationalOp::GreaterThanEqual,
        ast::RelationalOp::Equal => engine::RelationalOp::Equal,
        ast::RelationalOp::NotEqual => engine::RelationalOp::NotEqual,
    }
}

/// Translate an AST arithmetic operator to an engine arithmetic operator.
fn translate_arith_op(op: &ast::ArithOp) -> engine::ArithmeticOp {
    match op {
        ast::ArithOp::Add => engine::ArithmeticOp::Add,
        ast::ArithOp::Subtract => engine::ArithmeticOp::Subtract,
        ast::ArithOp::Multiply => engine::ArithmeticOp::Multiply,
        ast::ArithOp::Divide => engine::ArithmeticOp::Divide,
    }
}

/// Collect all variables used in a body (AST goals).
fn collect_body_variables(body: &[ast::Goal]) -> HashSet<String> {
    let mut vars = HashSet::new();
    for goal in body {
        match goal {
            ast::Goal::Relation(left, _, right) => {
                collect_term_variables(left, &mut vars);
                collect_term_variables(right, &mut vars);
            }
            ast::Goal::Assign(variable, rhs) => {
                match variable {
                    ast::Variable::Var(name) => {
                        vars.insert(name.clone());
                    }
                    ast::Variable::Wildcard => {
                        // Wildcards don't count as "used" in the traditional sense
                    }
                }
                collect_rhs_variables(rhs, &mut vars);
            }
            ast::Goal::Check(compound) => {
                for param in &compound.params {
                    collect_term_variables(param, &mut vars);
                }
            }
        }
    }
    vars
}

/// Collect variables from an AST term.
fn collect_term_variables(term: &ast::Term, vars: &mut HashSet<String>) {
    match term {
        ast::Term::Var(ast::Variable::Var(name)) => {
            vars.insert(name.clone());
        }
        ast::Term::Var(ast::Variable::Wildcard) => {
            // Wildcards don't count as "used" variables
        }
        ast::Term::Compound(compound) => {
            for param in &compound.params {
                collect_term_variables(param, vars);
            }
        }
        ast::Term::List(items) => {
            for item in items {
                collect_term_variables(item, vars);
            }
        }
        _ => {}
    }
}

/// Collect variables from an RHS expression.
fn collect_rhs_variables(rhs: &ast::RHS, vars: &mut HashSet<String>) {
    match rhs {
        ast::RHS::Compound(compound) => {
            for param in &compound.params {
                collect_term_variables(param, vars);
            }
        }
        ast::RHS::Expr(expr) => {
            collect_arith_expr_variables(expr, vars);
        }
    }
}

/// Collect variables from an arithmetic expression.
fn collect_arith_expr_variables(expr: &ast::ArithExpr, vars: &mut HashSet<String>) {
    match expr {
        ast::ArithExpr::Var(ast::Variable::Var(name)) => {
            vars.insert(name.clone());
        }
        ast::ArithExpr::Var(ast::Variable::Wildcard) => {
            // Wildcards don't count
        }
        ast::ArithExpr::Expr(left, _, right) => {
            collect_arith_expr_variables(left, vars);
            collect_arith_expr_variables(right, vars);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parseable;

    fn translate_input(input: &str) -> engine::Clause {
        let (_, clause) = ast::Clause::parse(input).unwrap();
        translate_clause(clause).unwrap()
    }

    #[test]
    fn translates_fuzzy_fact_with_head_normalisation() {
        let translated = translate_input("fuzzy(foo) :~ 0.8.");

        let expected = engine::Clause::new(
            engine::Symbol::new(
                "fuzzy",
                vec![engine::Variable::new("_T0")],
                vec![engine::Variable::new("_T0")],
            ),
            engine::Goal::Conjunction(
                Box::new(engine::Goal::Assign(
                    engine::Variable::new("_T0"),
                    engine::RHSTerm::Sym(engine::Symbol::new("foo", vec![], vec![])),
                )),
                Box::new(engine::Goal::TruthExpr(engine::Expression::num(0.8))),
            ),
        );

        assert_eq!(translated, expected);
        assert_eq!(translated.truth_value(), engine::Expression::num(0.8));
    }

    #[test]
    fn translates_fuzzy_clause_with_body_and_local_variable() {
        let translated = translate_input("score(X) :~ Y > 3, X + Y.");

        let expected = engine::Clause::new(
            engine::Symbol::new(
                "score",
                vec![engine::Variable::new("X")],
                vec![engine::Variable::new("_T0"), engine::Variable::new("Y")],
            ),
            engine::Goal::Conjunction(
                Box::new(engine::Goal::Conjunction(
                    Box::new(engine::Goal::Assign(
                        engine::Variable::new("_T0"),
                        engine::RHSTerm::Num(ordered_float::OrderedFloat::from(3.0)),
                    )),
                    Box::new(engine::Goal::Relation(
                        engine::Variable::new("Y"),
                        engine::Variable::new("_T0"),
                        engine::RelationalOp::GreaterThan,
                    )),
                )),
                Box::new(engine::Goal::TruthExpr(engine::Expression::binary(
                    engine::Expression::variable("X"),
                    engine::Expression::variable("Y"),
                    engine::ArithmeticOp::Add,
                ))),
            ),
        );

        assert_eq!(translated, expected);
        assert_eq!(
            translated.truth_value(),
            engine::Expression::binary(
                engine::Expression::variable("X"),
                engine::Expression::variable("Y"),
                engine::ArithmeticOp::Add,
            )
        );
    }

    #[test]
    fn translates_fuzzy_clause_body_before_truth_expression() {
        let translated = translate_input("weighted(X) :~ helper(X), X - 0.25.");

        let expected = engine::Clause::new(
            engine::Symbol::new("weighted", vec![engine::Variable::new("X")], vec![]),
            engine::Goal::Conjunction(
                Box::new(engine::Goal::Check {
                    functor: "helper".to_string(),
                    params: vec![engine::Variable::new("X")],
                }),
                Box::new(engine::Goal::TruthExpr(engine::Expression::binary(
                    engine::Expression::variable("X"),
                    engine::Expression::num(0.25),
                    engine::ArithmeticOp::Subtract,
                ))),
            ),
        );

        assert_eq!(translated, expected);
        assert_eq!(
            translated.truth_value(),
            engine::Expression::binary(
                engine::Expression::variable("X"),
                engine::Expression::num(0.25),
                engine::ArithmeticOp::Subtract,
            )
        );
    }

    #[test]
    fn translates_crisp_fact_with_head_normalisation() {
        let translated = translate_input("parent(john, X).");

        let expected = engine::Clause::new(
            engine::Symbol::new(
                "parent",
                vec![engine::Variable::new("_T0"), engine::Variable::new("X")],
                vec![engine::Variable::new("_T0")],
            ),
            engine::Goal::Conjunction(
                Box::new(engine::Goal::Assign(
                    engine::Variable::new("_T0"),
                    engine::RHSTerm::Sym(engine::Symbol::new("john", vec![], vec![])),
                )),
                Box::new(engine::Goal::TruthExpr(engine::Expression::num(1.0))),
            ),
        );

        assert_eq!(translated, expected);
        assert_eq!(translated.truth_value(), engine::Expression::num(1.0));
    }

    #[test]
    fn translates_crisp_clause_with_body() {
        let translated = translate_input("reachable(X) :- edge(X). ");

        let expected = engine::Clause::new(
            engine::Symbol::new("reachable", vec![engine::Variable::new("X")], vec![]),
            engine::Goal::Check {
                functor: "edge".to_string(),
                params: vec![engine::Variable::new("X")],
            },
        );

        assert_eq!(translated, expected);
        assert_eq!(translated.truth_value(), engine::Expression::num(1.0));
    }

    #[test]
    fn translates_check_goal_with_literal_arguments() {
        let translated = translate_input("p(X) :- q(X, 1, foo). ");

        let expected = engine::Clause::new(
            engine::Symbol::new(
                "p",
                vec![engine::Variable::new("X")],
                vec![engine::Variable::new("_T0"), engine::Variable::new("_T1")],
            ),
            engine::Goal::Conjunction(
                Box::new(engine::Goal::Assign(
                    engine::Variable::new("_T0"),
                    engine::RHSTerm::Num(ordered_float::OrderedFloat::from(1.0)),
                )),
                Box::new(engine::Goal::Conjunction(
                    Box::new(engine::Goal::Assign(
                        engine::Variable::new("_T1"),
                        engine::RHSTerm::Sym(engine::Symbol::new("foo", vec![], vec![])),
                    )),
                    Box::new(engine::Goal::Check {
                        functor: "q".to_string(),
                        params: vec![
                            engine::Variable::new("X"),
                            engine::Variable::new("_T0"),
                            engine::Variable::new("_T1"),
                        ],
                    }),
                )),
            ),
        );

        assert_eq!(translated, expected);
        assert_eq!(translated.truth_value(), engine::Expression::num(1.0));
    }

    #[test]
    fn translate_clause_head_tracks_counters_and_goals() {
        let head = ast::Compound {
            functor: "mix".to_string(),
            params: vec![
                ast::Term::Var(ast::Variable::Var("X".to_string())),
                ast::Term::Var(ast::Variable::Wildcard),
                ast::Term::Atom(ast::Atom {
                    name: "a".to_string(),
                }),
                ast::Term::Num(ordered_float::OrderedFloat::from(2.0)),
            ],
        };

        let mut state = TranslationState {
            temp_var_counter: 0,
            wildcard_counter: 0,
        };

        let (params, goals) = translate_clause_head(&head, &mut state).unwrap();

        assert_eq!(
            params,
            vec![
                engine::Variable::new("X"),
                engine::Variable::new("_W0"),
                engine::Variable::new("_T0"),
                engine::Variable::new("_T1"),
            ]
        );
        assert_eq!(
            goals,
            vec![
                engine::Goal::Assign(
                    engine::Variable::new("_T0"),
                    engine::RHSTerm::Sym(engine::Symbol::new("a", vec![], vec![])),
                ),
                engine::Goal::Assign(
                    engine::Variable::new("_T1"),
                    engine::RHSTerm::Num(ordered_float::OrderedFloat::from(2.0)),
                ),
            ]
        );
        assert_eq!(state.temp_var_counter, 2);
        assert_eq!(state.wildcard_counter, 1);
    }

    #[test]
    fn term_to_variable_for_relation_creates_assignment_for_atom() {
        let mut state = TranslationState {
            temp_var_counter: 0,
            wildcard_counter: 0,
        };

        let (var, pre_goals) = term_to_variable_for_relation(
            &ast::Term::Atom(ast::Atom {
                name: "foo".to_string(),
            }),
            &mut state,
        )
        .unwrap();

        assert_eq!(var, engine::Variable::new("_T0"));
        assert_eq!(
            pre_goals,
            vec![engine::Goal::Assign(
                engine::Variable::new("_T0"),
                engine::RHSTerm::Sym(engine::Symbol::new("foo", vec![], vec![])),
            )]
        );
        assert_eq!(state.temp_var_counter, 1);
    }

    #[test]
    fn translate_clause_body_non_fuzzy_preserves_goal_order() {
        let body = vec![
            ast::Goal::Check(ast::Compound {
                functor: "a".to_string(),
                params: vec![ast::Term::Var(ast::Variable::Var("X".to_string()))],
            }),
            ast::Goal::Assign(
                ast::Variable::Var("Y".to_string()),
                ast::RHS::Expr(ast::ArithExpr::Num(ordered_float::OrderedFloat::from(1.0))),
            ),
        ];

        let mut state = TranslationState {
            temp_var_counter: 0,
            wildcard_counter: 0,
        };

        let translated = translate_clause_body(&body, &None, &mut state).unwrap();

        assert_eq!(
            translated,
            engine::Goal::Conjunction(
                Box::new(engine::Goal::Check {
                    functor: "a".to_string(),
                    params: vec![engine::Variable::new("X")],
                }),
                Box::new(engine::Goal::Assign(
                    engine::Variable::new("Y"),
                    engine::RHSTerm::Expr(engine::Expression::num(1.0)),
                )),
            )
        );
    }
}
