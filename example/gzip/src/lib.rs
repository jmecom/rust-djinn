pub mod bench;
pub mod bench_decompress;
pub mod spec;

#[forbid(unsafe_code)]
#[path = "../djinn/solution/mod.rs"]
pub mod solution;

pub use spec::*;
