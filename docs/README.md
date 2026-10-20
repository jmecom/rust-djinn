# Documentation

Start with [onboarding](FIRST_STEPS.md), then work through
[writing specifications](WRITING_SPECS.md). The first guide gets you editing and
checking Djinn; the second teaches how to decide what to write. Keep the
[language tour](LANGUAGE_TOUR.md) nearby for syntax and semantics, and use
[installation](INSTALL.md) to add tools as you need them. Editor integration
and coding agents are not prerequisites for reading or drafting specifications.

The guides describe the implementation in this checkout. Djinn resembles Rust,
but code inside `djinn!` is a constraint language with its own semantics and a
limited set of supported operations. A passing proof establishes the written
contract, so reviewing that contract remains the author's responsibility.

## Examples by topic

Read each example's README for its commands and reported proof status. The
presence of an example does not mean every declaration has been verified.
For Djinn crates, `cargo djinn status` reports the saved state, and
`cargo djinn verify` performs a fresh check when the full toolchain is installed.
The historical `calib` crate has its own manual verification commands.

| Example | What to inspect |
|---|---|
| [clamp](../example/clamp/README.md) | Scalar constraints, preconditions, counting, and an ordinary Rust caller; the onboarding example |
| [sort](../example/sort/README.md) | Ordering and permutation constraints over a vector, plus a benchmark workload |
| [broken](../example/broken/README.md) | Deliberately flawed specifications and counterexamples from smoke testing |
| [strmap](../example/strmap/README.md) | Strings, structs, map operations, and calls to modeled ordinary Rust functions |
| [calib](../example/calib/README.md) | Historical plain-Rust sort/max example with manually emitted Lean obligations and proofs |
| [sudoku](../example/sudoku/README.md) | A larger relational specification with multiple proof obligations |
| [lz77](../example/lz77/README.md) | Recursive compression and decompression specifications from the paper |
| [choice](../example/choice/README.md) | `any` and `#[weakly_specified]`, including the extra review those choices require |
| [gzip](../example/gzip/README.md) | A larger compression example with implementation choices and performance workloads |

## Understanding the implementation

Writing specifications does not require writing Lean. When diagnosing unsupported
syntax or contributing to the tools, these are useful starting points:

| Source | Responsibility |
|---|---|
| [parse.rs](../rust-djinn/syntax/src/parse.rs) | Accepted syntax inside a specification |
| [lower.rs](../rust-djinn/syntax/src/lower.rs) | Translation of constraints into Lean propositions |
| [gate.rs](../rust-djinn/macros/src/gate.rs) | What an ordinary Cargo build checks in the saved report |
| [config.rs](../rust-djinn/cargo-djinn/src/config.rs) | Crate metadata, environment variables, and path resolution |
| [verify.rs](../rust-djinn/cargo-djinn/src/verify.rs) | Translation, proof checking, and report generation |
| [guide.rs](../rust-djinn/cargo-djinn/src/guide.rs) | Instructions supplied to the implementation agent |

For editor commands and configuration, see [editor integration](../editors/README.md).
