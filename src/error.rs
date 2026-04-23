//! Error definitions for Mimir.
//!
//! Errors are defined using [`thiserror`], which provides a derive macro for the std error trait.
use thiserror::Error;

use crate::engine::*;

/// Any possible error that can be produced.
#[allow(missing_docs)]
#[derive(Debug, Error)]
pub enum MimirError {
    #[error("{0}")]
    Parsing(#[from] ParsingError),
    #[error("{0}")]
    Translation(#[from] TranslationError),
    #[error("{0}")]
    Engine(#[from] EngineError),
    #[error("invalid cons list structure")]
    InvalidListStructure,
    #[error("invalid value type: expected {0}")]
    InvalidValueType(String),
}

/// An error that may occur during parsing.
#[allow(missing_docs)]
#[derive(Debug, Error)]
pub enum ParsingError {
    #[error("syntax error:\n{0}")]
    VerboseError(String),
    #[error("unexpected chars: {0}")]
    TrailingCharacters(String),
}

/// An error that may occur during AST to internal representation translation.
#[allow(missing_docs)]
#[derive(Debug, Error)]
pub enum TranslationError {
    #[error("list term found after desugaring - invariant violation")]
    ListNotDesugared,
}

/// An error that may occur in the execution of the engine.
#[allow(missing_docs)]
#[derive(Debug, Error)]
pub enum EngineError {
    #[error("invalid clause: clause matching '{0}/{1}' not found.")]
    ClauseNotFound(String, usize),
    #[error("failed to start execution worker thread: {0}")]
    ThreadSpawn(std::io::Error),
    #[error("execution worker thread panicked")]
    ThreadPanicked,
    #[error("undefined variable: '{0}'")]
    UndefinedVar(Variable),
    #[error("unexpected number of parameters: expected {expected}, got {got}")]
    UnexpectedParamNum { expected: usize, got: usize },
    #[error("variable '{0}' is not a number")]
    NotANumber(Variable),
    #[error("attempted to perform invalid arithmetic operation: {0} {1:?} {2}")]
    InvalidArithOp(f64, ArithmeticOp, f64),
    #[error("attempted to find set representative of non-placeholder value '{0:?}'")]
    SetReprNonPlaceholder(Value),
    #[error("cannot unify the terms '{0:?}' and '{1:?}'")]
    CannotUnifyTerms(Value, Value),
}
