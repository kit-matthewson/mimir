//! # Mimir: A Prolog Interpreter in Rust
//!
//! Mimir is a simple Mini-Prolog interpreter implemented in Rust.

#![warn(missing_docs)]
#![allow(clippy::module_inception)]

pub mod engine;
pub mod error;
pub mod parser;

pub use error::MimirError;
