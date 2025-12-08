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
    /// When an unexpected number of parameters is given for a clause.
    /// 
    /// `UnexpectedParamNum(expected, got)`
    #[error("unexpected number of params: expected {0}, got {1}")]
    UnexpectedParamNum(usize, usize),
    #[error("variable is not a number")]
    NotANumber,
}
