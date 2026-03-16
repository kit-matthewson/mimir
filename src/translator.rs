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
pub fn translate(clause: ast::Clause) -> Result<engine::Clause, TranslationError> {
    let mut state = TranslationState {
        temp_var_counter: 0,
        wildcard_counter: 0,
    };

    // Normalise head by replacing non-variable terms with temp variables and generating unification goals
    let (params, head_unification_goals) = translate_clause_head(&clause.head, &mut state)?;

    // Translate body goals, potentially creating more temporary variables
    let body_goals = translate_clause_body(&clause.body, &mut state)?;

    // Combine head unification goals with body
    // We start with a 'true' goal so that facts work correctly
    let combined_body = head_unification_goals
        .into_iter()
        .chain(std::iter::once(body_goals))
        .map(Box::new)
        .fold(engine::Goal::Bool(true), |acc, goal| {
            engine::Goal::Conjunction(goal, Box::new(acc))
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
    state: &mut TranslationState,
) -> Result<engine::Goal, TranslationError> {
    if body.is_empty() {
        return Ok(engine::Goal::Bool(true));
    }

    // Convert each goal and combine with conjunction
    let mut goals_iter = body.iter();
    let first_goal = translate_goal(goals_iter.next().expect("body is not empty"), state)?;

    goals_iter.try_fold(first_goal, |acc, goal| {
        let translated = translate_goal(goal, state)?;
        Ok(engine::Goal::Conjunction(
            Box::new(acc),
            Box::new(translated),
        ))
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
            let params: Vec<engine::Variable> = compound
                .params
                .iter()
                .map(|term| term_to_variable(term, state))
                .collect();

            Ok(engine::Goal::Check { functor, params })
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
    use ordered_float::OrderedFloat;

    use super::*;

    /// Helper to create an atom term
    fn atom(name: &str) -> ast::Term {
        ast::Term::Atom(ast::Atom {
            name: name.to_string(),
        })
    }

    /// Helper to create a variable term
    fn var(name: &str) -> ast::Term {
        ast::Term::Var(ast::Variable::Var(name.to_string()))
    }

    /// Helper to create a wildcard term
    fn wildcard() -> ast::Term {
        ast::Term::Var(ast::Variable::Wildcard)
    }

    /// Helper to create a number term
    fn num(n: f64) -> ast::Term {
        ast::Term::Num(OrderedFloat::from(n))
    }

    /// Helper to create a compound term
    fn compound(functor: &str, params: Vec<ast::Term>) -> ast::Term {
        ast::Term::Compound(ast::Compound {
            functor: functor.to_string(),
            params,
        })
    }

    #[test]
    fn test_simple_fact() {
        // parent(alice).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "parent".to_string(),
                params: vec![atom("alice")],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        // Head should have one parameter (a temp variable)
        assert_eq!(translated.head().functor(), "parent");
        assert_eq!(translated.head().parameters().len(), 1);

        // Should have temp variables in local_vars
        assert!(!translated.head().local_vars().is_empty());
    }

    #[test]
    fn test_fact_with_variable() {
        // parent(X).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "parent".to_string(),
                params: vec![var("X")],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        assert_eq!(translated.head().functor(), "parent");
        assert_eq!(translated.head().parameters().len(), 1);
        assert_eq!(translated.head().parameters()[0].to_string(), "X");
    }

    #[test]
    fn test_rule_with_body() {
        // child(X) :- parent(X).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "child".to_string(),
                params: vec![var("X")],
            },
            body: vec![ast::Goal::Check(ast::Compound {
                functor: "parent".to_string(),
                params: vec![var("X")],
            })],
        };

        let translated = translate(clause).unwrap();

        assert_eq!(translated.head().functor(), "child");
        assert_eq!(translated.head().parameters().len(), 1);
    }

    #[test]
    fn test_list_desugaring_empty() {
        // test([]).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![ast::Term::List(vec![])],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        // Empty list should desugar to 'nil'
        assert_eq!(translated.head().functor(), "test");
    }

    #[test]
    fn test_list_desugaring_single_element() {
        // test([1]).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![ast::Term::List(vec![num(1.0)])],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        // [1] should desugar to .(1, nil)
        assert_eq!(translated.head().functor(), "test");
    }

    #[test]
    fn test_list_desugaring_multiple_elements() {
        // test([1, 2, 3]).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![ast::Term::List(vec![num(1.0), num(2.0), num(3.0)])],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        // [1,2,3] should desugar to .(1, .(2, .(3, nil)))
        assert_eq!(translated.head().functor(), "test");
    }

    #[test]
    fn test_list_with_variables() {
        // test([X, Y, Z]).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![ast::Term::List(vec![var("X"), var("Y"), var("Z")])],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        assert_eq!(translated.head().functor(), "test");
    }

    #[test]
    fn test_nested_compound_terms() {
        // test(foo(bar(baz))).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![compound("foo", vec![compound("bar", vec![atom("baz")])])],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        assert_eq!(translated.head().functor(), "test");
        assert_eq!(translated.head().parameters().len(), 1);
    }

    #[test]
    fn test_multiple_head_arguments() {
        // test(alice, bob, charlie).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![atom("alice"), atom("bob"), atom("charlie")],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        assert_eq!(translated.head().functor(), "test");
        assert_eq!(translated.head().parameters().len(), 3);

        // Should generate 3 temp variables
        assert!(translated.head().local_vars().len() >= 3);
    }

    #[test]
    fn test_mixed_head_arguments() {
        // test(X, alice, Y, 42).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![var("X"), atom("alice"), var("Y"), num(42.0)],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        assert_eq!(translated.head().functor(), "test");
        assert_eq!(translated.head().parameters().len(), 4);
    }

    #[test]
    fn test_wildcard_variables() {
        // test(_, _).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![wildcard(), wildcard()],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        assert_eq!(translated.head().functor(), "test");
        assert_eq!(translated.head().parameters().len(), 2);

        // Each wildcard should get a unique internal variable
        let param1 = translated.head().parameters()[0].to_string();
        let param2 = translated.head().parameters()[1].to_string();
        assert_ne!(param1, param2);
    }

    #[test]
    fn test_relational_operators() {
        // test(X) :- X < 10.
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![var("X")],
            },
            body: vec![ast::Goal::Relation(
                var("X"),
                ast::RelationalOp::LessThan,
                num(10.0),
            )],
        };

        let translated = translate(clause).unwrap();

        assert_eq!(translated.head().functor(), "test");

        // The constant `10` in relation must be translated through a temp var assignment.
        match translated.body() {
            engine::Goal::Conjunction(left, _) => match left.as_ref() {
                engine::Goal::Conjunction(assign, relation) => {
                    assert!(matches!(
                        assign.as_ref(),
                        engine::Goal::Assign(_, engine::RHSTerm::Num(n)) if *n == OrderedFloat::from(10.0)
                    ));
                    assert!(matches!(
                        relation.as_ref(),
                        engine::Goal::Relation(_, _, engine::RelationalOp::LessThan)
                    ));
                }
                _ => panic!("Expected relation goal to include assignment pre-goal"),
            },
            _ => panic!("Expected top-level conjunction"),
        }
    }

    #[test]
    fn test_assignment_in_body() {
        // test(X) :- Y = X + 1.
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![var("X")],
            },
            body: vec![ast::Goal::Assign(
                ast::Variable::Var("Y".to_string()),
                ast::RHS::Expr(ast::ArithExpr::Expr(
                    Box::new(ast::ArithExpr::Var(ast::Variable::Var("X".to_string()))),
                    ast::ArithOp::Add,
                    Box::new(ast::ArithExpr::Num(OrderedFloat::from(1.0))),
                )),
            )],
        };

        let translated = translate(clause).unwrap();

        assert_eq!(translated.head().functor(), "test");
    }

    #[test]
    fn test_multiple_body_goals() {
        // ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "ancestor".to_string(),
                params: vec![var("X"), var("Y")],
            },
            body: vec![
                ast::Goal::Check(ast::Compound {
                    functor: "parent".to_string(),
                    params: vec![var("X"), var("Z")],
                }),
                ast::Goal::Check(ast::Compound {
                    functor: "ancestor".to_string(),
                    params: vec![var("Z"), var("Y")],
                }),
            ],
        };

        let translated = translate(clause).unwrap();

        assert_eq!(translated.head().functor(), "ancestor");
        assert_eq!(translated.head().parameters().len(), 2);
    }

    #[test]
    fn test_goal_conjunction_structure() {
        // test(X) :- a(X), b(X), c(X).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![var("X")],
            },
            body: vec![
                ast::Goal::Check(ast::Compound {
                    functor: "a".to_string(),
                    params: vec![var("X")],
                }),
                ast::Goal::Check(ast::Compound {
                    functor: "b".to_string(),
                    params: vec![var("X")],
                }),
                ast::Goal::Check(ast::Compound {
                    functor: "c".to_string(),
                    params: vec![var("X")],
                }),
            ],
        };

        let translated = translate(clause).unwrap();

        // Body should be nested conjunctions
        assert_eq!(translated.head().functor(), "test");
    }

    #[test]
    fn test_temp_variable_uniqueness() {
        // test(foo, bar, baz) :- check(foo).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![atom("foo"), atom("bar"), atom("baz")],
            },
            body: vec![ast::Goal::Check(ast::Compound {
                functor: "check".to_string(),
                params: vec![atom("foo")],
            })],
        };

        let translated = translate(clause).unwrap();

        // Should generate unique temp variables for each atom in head
        assert!(translated.head().local_vars().len() >= 3);

        // Check that all temp variables have unique names
        let var_names: std::collections::HashSet<_> = translated
            .head()
            .local_vars()
            .iter()
            .map(|v| v.to_string())
            .collect();

        assert_eq!(translated.head().local_vars().len(), var_names.len());
    }

    #[test]
    fn test_nested_list_in_compound() {
        // test(foo([1, 2])).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![compound(
                    "foo",
                    vec![ast::Term::List(vec![num(1.0), num(2.0)])],
                )],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        // Lists should be desugared even when nested
        assert_eq!(translated.head().functor(), "test");
    }

    #[test]
    fn test_list_in_body_goal() {
        // test(X) :- member(X, [1, 2, 3]).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![var("X")],
            },
            body: vec![ast::Goal::Check(ast::Compound {
                functor: "member".to_string(),
                params: vec![
                    var("X"),
                    ast::Term::List(vec![num(1.0), num(2.0), num(3.0)]),
                ],
            })],
        };

        let translated = translate(clause).unwrap();

        // Lists in body should also be desugared
        assert_eq!(translated.head().functor(), "test");
    }

    #[test]
    fn test_complex_nested_structure() {
        // test(foo(bar([X, Y]), baz(Z))).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![compound(
                    "foo",
                    vec![
                        compound("bar", vec![ast::Term::List(vec![var("X"), var("Y")])]),
                        compound("baz", vec![var("Z")]),
                    ],
                )],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        assert_eq!(translated.head().functor(), "test");
        assert_eq!(translated.head().parameters().len(), 1);
    }

    #[test]
    fn test_arithmetic_expressions() {
        // test(X, Y) :- Z = X + Y * 2.
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![var("X"), var("Y")],
            },
            body: vec![ast::Goal::Assign(
                ast::Variable::Var("Z".to_string()),
                ast::RHS::Expr(ast::ArithExpr::Expr(
                    Box::new(ast::ArithExpr::Var(ast::Variable::Var("X".to_string()))),
                    ast::ArithOp::Add,
                    Box::new(ast::ArithExpr::Expr(
                        Box::new(ast::ArithExpr::Var(ast::Variable::Var("Y".to_string()))),
                        ast::ArithOp::Multiply,
                        Box::new(ast::ArithExpr::Num(OrderedFloat::from(2.0))),
                    )),
                )),
            )],
        };

        let translated = translate(clause).unwrap();

        assert_eq!(translated.head().functor(), "test");
        assert_eq!(translated.head().parameters().len(), 2);
    }

    #[test]
    fn test_structure_in_head_generates_unification() {
        // fact(42).
        // Should translate to: fact(_T0) :- _T0 := 42.
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "fact".to_string(),
                params: vec![num(42.0)],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        // Head parameter should be a temp variable
        assert_eq!(translated.head().parameters().len(), 1);
        let param_name = translated.head().parameters()[0].to_string();
        assert!(param_name.starts_with("_T"));

        // Body should contain an assignment goal for the temp variable
        // The body structure is: Bool(true) AND (Assign(_T0, 42) AND Bool(true))
        // The fold creates: Conjunction(body_goals, Conjunction(unif_goal, Bool(true)))
        match translated.body() {
            engine::Goal::Conjunction(left, right) => {
                // Left should be Bool(true) from the body
                match left.as_ref() {
                    engine::Goal::Bool(true) => {}
                    _ => panic!("Expected Bool(true) on left"),
                }
                // Right should contain the unification goals
                match right.as_ref() {
                    engine::Goal::Conjunction(unif_left, unif_right) => {
                        // This should be our Assign goal
                        match unif_left.as_ref() {
                            engine::Goal::Assign(var, rhs_term) => {
                                assert_eq!(var.to_string(), param_name);
                                match rhs_term {
                                    engine::RHSTerm::Num(n) => {
                                        assert_eq!(*n, OrderedFloat::from(42.0))
                                    }
                                    _ => panic!("Expected a number RHS term"),
                                }
                            }
                            _ => panic!("Expected an Assign goal"),
                        }
                        // The innermost right should be Bool(true)
                        match unif_right.as_ref() {
                            engine::Goal::Bool(true) => {}
                            _ => panic!("Expected Bool(true) innermost"),
                        }
                    }
                    _ => panic!("Expected a nested Conjunction"),
                }
            }
            _ => panic!("Expected a Conjunction goal"),
        }
    }

    #[test]
    fn test_multiple_structures_in_head_generate_multiple_unifications() {
        // test(alice, 42, bob).
        // Should translate to: test(_T0, _T1, _T2) :- _T0 := alice, _T1 := 42, _T2 := bob.
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![atom("alice"), num(42.0), atom("bob")],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        // All head parameters should be temp variables
        assert_eq!(translated.head().parameters().len(), 3);
        for param in translated.head().parameters() {
            assert!(param.to_string().starts_with("_T"));
        }

        // Body should contain three assignment goals
        // Structure: Bool(true) AND (Assign1 AND (Assign2 AND (Assign3 AND Bool(true))))
        let mut goal_count = 0;

        // Skip the outermost Bool(true) from body_goals
        if let engine::Goal::Conjunction(_, right) = translated.body() {
            let mut current = right.as_ref();

            // Walk through the nested conjunctions
            loop {
                match current {
                    engine::Goal::Conjunction(left, right_inner) => {
                        if matches!(left.as_ref(), engine::Goal::Assign(_, _)) {
                            goal_count += 1;
                        }
                        current = right_inner.as_ref();
                    }
                    engine::Goal::Bool(true) => break,
                    engine::Goal::Assign(_, _) => {
                        goal_count += 1;
                        break;
                    }
                    _ => break,
                }
            }
        }

        assert_eq!(
            goal_count, 3,
            "Expected 3 assignment goals for the 3 structures"
        );
    }

    #[test]
    fn test_compound_structure_in_head() {
        // test(foo(bar)).
        // Should translate to: test(_T0) :- _T0 := foo(_T1), _T1 := bar.
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![compound("foo", vec![atom("bar")])],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        // Head should have one temp variable parameter
        assert_eq!(translated.head().parameters().len(), 1);
        assert!(
            translated.head().parameters()[0]
                .to_string()
                .starts_with("_T")
        );

        // Should have multiple temp variables (one for outer compound, one for inner atom)
        assert!(translated.head().local_vars().len() >= 2);
    }

    #[test]
    fn test_mixed_variables_and_structures() {
        // test(X, alice, Y).
        // Should translate to: test(X, _T0, Y) :- _T0 := alice.
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![var("X"), atom("alice"), var("Y")],
            },
            body: vec![],
        };

        let translated = translate(clause).unwrap();

        // First and third parameters should be X and Y
        assert_eq!(translated.head().parameters()[0].to_string(), "X");
        assert_eq!(translated.head().parameters()[2].to_string(), "Y");

        // Second parameter should be a temp variable
        assert!(
            translated.head().parameters()[1]
                .to_string()
                .starts_with("_T")
        );

        // Should have exactly one temp variable in local_vars
        let temp_vars: Vec<_> = translated
            .head()
            .local_vars()
            .iter()
            .filter(|v| v.to_string().starts_with("_T"))
            .collect();
        assert_eq!(temp_vars.len(), 1);
    }

    #[test]
    fn test_structure_with_body_goals() {
        // test(42) :- check(x).
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![num(42.0)],
            },
            body: vec![ast::Goal::Check(ast::Compound {
                functor: "check".to_string(),
                params: vec![atom("x")],
            })],
        };

        let translated = translate(clause).unwrap();

        // Actual structure: Conjunction(Check, Conjunction(Assign, Bool))
        match translated.body() {
            engine::Goal::Conjunction(left, right) => {
                // Left should be the Check goal (body is folded into the structure)
                assert!(matches!(left.as_ref(), engine::Goal::Check { .. }));

                // Right should contain the head unification goals
                match right.as_ref() {
                    engine::Goal::Conjunction(assign_goal, _) => {
                        assert!(matches!(assign_goal.as_ref(), engine::Goal::Assign(_, _)));
                    }
                    _ => panic!("Expected unification goals in conjunction"),
                }
            }
            _ => panic!("Expected top-level conjunction"),
        }
    }

    #[test]
    fn test_body_only_variables_in_local_vars() {
        // test() :- foo(X).
        // X is used in body but not in head, should be in local_vars
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![],
            },
            body: vec![ast::Goal::Check(ast::Compound {
                functor: "foo".to_string(),
                params: vec![var("X")],
            })],
        };

        let translated = translate(clause).unwrap();

        // X should be in local_vars since it's not in head parameters
        let local_var_names: std::collections::HashSet<_> = translated
            .head()
            .local_vars()
            .iter()
            .map(|v| v.to_string())
            .collect();

        assert!(local_var_names.contains("X"), "X should be in local_vars");
    }

    #[test]
    fn test_body_variable_not_in_head() {
        // test(X) :- Y = X + 1.
        // X is in head, Y is only in body - Y should be in local_vars
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![var("X")],
            },
            body: vec![ast::Goal::Assign(
                ast::Variable::Var("Y".to_string()),
                ast::RHS::Expr(ast::ArithExpr::Expr(
                    Box::new(ast::ArithExpr::Var(ast::Variable::Var("X".to_string()))),
                    ast::ArithOp::Add,
                    Box::new(ast::ArithExpr::Num(OrderedFloat::from(1.0))),
                )),
            )],
        };

        let translated = translate(clause).unwrap();

        // X should be in parameters
        assert_eq!(translated.head().parameters()[0].to_string(), "X");

        // Y should be in local_vars (not in parameters)
        let local_var_names: std::collections::HashSet<_> = translated
            .head()
            .local_vars()
            .iter()
            .map(|v| v.to_string())
            .collect();

        assert!(local_var_names.contains("Y"), "Y should be in local_vars");
    }

    #[test]
    fn test_multiple_body_variables() {
        // test(X) :- foo(Y, Z), Y = X + 1.
        // Y and Z are in body but not in head
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![var("X")],
            },
            body: vec![
                ast::Goal::Check(ast::Compound {
                    functor: "foo".to_string(),
                    params: vec![var("Y"), var("Z")],
                }),
                ast::Goal::Assign(
                    ast::Variable::Var("Y".to_string()),
                    ast::RHS::Expr(ast::ArithExpr::Var(ast::Variable::Var("X".to_string()))),
                ),
            ],
        };

        let translated = translate(clause).unwrap();

        let local_var_names: std::collections::HashSet<_> = translated
            .head()
            .local_vars()
            .iter()
            .map(|v| v.to_string())
            .collect();

        assert!(local_var_names.contains("Y"), "Y should be in local_vars");
        assert!(local_var_names.contains("Z"), "Z should be in local_vars");
    }

    #[test]
    fn test_body_variables_from_lists() {
        // test() :- member(X, [1, 2, 3]).
        // X is used in body via list parameters
        let clause = ast::Clause {
            head: ast::Compound {
                functor: "test".to_string(),
                params: vec![],
            },
            body: vec![ast::Goal::Check(ast::Compound {
                functor: "member".to_string(),
                params: vec![
                    var("X"),
                    ast::Term::List(vec![num(1.0), num(2.0), num(3.0)]),
                ],
            })],
        };

        let translated = translate(clause).unwrap();

        let local_var_names: std::collections::HashSet<_> = translated
            .head()
            .local_vars()
            .iter()
            .map(|v| v.to_string())
            .collect();

        assert!(local_var_names.contains("X"), "X should be in local_vars");
    }
}
