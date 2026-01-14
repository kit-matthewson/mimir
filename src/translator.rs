//! Provides functions to translate a Prolog AST into the internal Mini-Prolog representation.

use crate::{engine, parser::ast};

/// Translate a single AST clause into the internal `engine::Clause` representation.
pub fn translate(_clause: ast::Clause) -> engine::Clause {
    // find local vars
    // convert lists and list operations
    // translate pattern-matching into unification
    // translate unification between values to variable bindings (only allow variable unification)
    todo!()
}
