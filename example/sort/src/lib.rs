//! Human-owned glue. Trusted, but there is nothing to trust: it only wires
//! the two modules together and forbids `unsafe` in the LLM's module.

pub mod spec;
pub mod bench;

#[forbid(unsafe_code)]
#[path = "../djinn/solution/mod.rs"]
pub mod solution;

pub use spec::{max, run, sort};
