//! Error definitions for Mimir.
//!
//! Errors are defined using [`thiserror`], which provides a derive macro for the std error trait.
use thiserror::Error;

use crate::engine::*;

/// Any possible error that can be produced.
#[allow(missing_docs)]
#[derive(Debug, Error)]
pub enum MimirError {
    #[error("engine error: {0}")]
    Engine(#[from] EngineError),
}

/// An error that may occur in the execution of the engine.
#[allow(missing_docs)]
#[derive(Debug, Error)]
pub enum EngineError {
    #[error("invalid clause: clause matching '{0}/{1}' not found.")]
    ClauseNotFound(String, usize),
    #[error("undefined variable: '{0}'")]
    UndefinedVar(Variable),
    #[error("unexpected number of params: expected {expected}, got {got}")]
    UnexpectedParamNum { expected: usize, got: usize },
    #[error("variable '{0}' is not a number")]
    NotANumber(Variable),
}
