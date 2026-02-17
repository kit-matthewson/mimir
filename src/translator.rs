//! Provides functions to translate a Prolog AST into the internal Mini-Prolog representation.
//!
//! This module implements the translation phase that converts user-facing Prolog syntax
//! into the simplified internal representation used by the Mini-Prolog engine.

use crate::{engine, parser::ast};

/// Translates a single AST clause into the internal engine representation.
pub fn translate(clause: ast::Clause) -> engine::Clause {
    let mut temp_var_counter = 0;
    let mut wildcard_counter = 0;

    // Convert lists to cons structures throughout the clause
    let desugared_clause = desugar_lists(clause);

    // Normalize head to variables only, generating unification goals
    let (params, head_unification_goals) = translate_clause_head(
        &desugared_clause.head,
        &mut temp_var_counter,
        &mut wildcard_counter,
    );

    // Translate body goals, potentially creating more temporary variables
    let body_goals = translate_clause_body(
        &desugared_clause.body,
        &mut temp_var_counter,
        &mut wildcard_counter,
    );

    // Combine head unification goals with body
    // We start with a 'true' goal so that facts (clauses without a body) work correctly
    let combined_body = head_unification_goals
        .into_iter()
        .chain(std::iter::once(body_goals))
        .map(Box::new)
        .fold(engine::Goal::Bool(true), |acc, goal| {
            engine::Goal::Conjunction(goal, Box::new(acc))
        });

    // Extract local variables after all transformations including wildcards
    let temp_vars = (0..temp_var_counter)
        .map(|i| format!("_T{}", i))
        .map(engine::Variable::new);
    let wildcard_vars = (0..wildcard_counter)
        .map(|i| format!("_W{}", i))
        .map(engine::Variable::new);
    let local_vars: Vec<engine::Variable> = temp_vars.chain(wildcard_vars).collect();

    // Create the final clause
    let head_symbol = engine::Symbol::new(&desugared_clause.head.functor, params, local_vars);

    engine::Clause::new(head_symbol, combined_body)
}

/// Desugar list syntax in the given clause, converting list literals into cons structures.
fn desugar_lists(clause: ast::Clause) -> ast::Clause {
    todo!("Desugaring lists in clause: {}", clause)
}

/// Translat the clause head by replacing non-variable terms with temporary variables and generating unification goals.
fn translate_clause_head(
    head: &ast::Compound,
    temp_var_counter: &mut usize,
    wildcard_counter: &mut usize,
) -> (Vec<engine::Variable>, Vec<engine::Goal>) {
    todo!(
        "Normalising clause head: {} (temps: {}, wildcards: {})",
        head,
        temp_var_counter,
        wildcard_counter
    )
}

/// Translate the clause body goals, handling any necessary temporary variable generation.
fn translate_clause_body(
    body: &[ast::Goal],
    temp_var_counter: &mut usize,
    wildcard_counter: &mut usize,
) -> engine::Goal {
    todo!(
        "Translating clause body with {} goals (temps: {}, wildcards: {})",
        body.len(),
        temp_var_counter,
        wildcard_counter
    )
}
