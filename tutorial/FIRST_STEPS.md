# First steps with Djinn

Djinn specifications describe the relationship between a Rust function's
inputs and outputs. The author determines which inputs are allowed, what
the result means, and how boundary cases are handled. An implementation
supplies the algorithm, and Lean proofs establish that its translated
behavior satisfies the written conditions.

This guide develops a small specification from a working example. It
distinguishes specification design, bounded checks for errors, and proof
of an implementation, then introduces the files and commands needed to
create a crate. It assumes basic Rust knowledge but no prior knowledge
of Lean.

The Rust-tools section of [Installation](INSTALL.md) is sufficient to run
the supplied example. The specification exercise additionally requires Z3;
regenerating and checking proofs requires Charon, Aeneas, and Lean. Editor
integration and agent-assisted implementation are optional later steps.

The commands assume `DJINN_REPO` points to the checkout, as set in the
installation guide. They run in the example crate unless a command
explicitly changes directories:

```sh
cd "$DJINN_REPO/example/clamp"
```

## An existing implementation

The clamp example includes an implementation, proofs, and a verification
report. Its ordinary Rust command-line program can be run directly:

```sh
printf '3\n-4\n12\n' | cargo run --quiet -- 0 10
```

The output is:

```text
1 negative input(s); clamped to [0, 10]: [3, 0, 10]; smallest: Some(0)
```

The program reads integers from standard input and takes the lower and upper
bounds as arguments. It counts negative inputs, clamps each input to the
requested range, and reports the smallest result. These operations call
functions declared in [`src/spec.rs`](../example/clamp/src/spec.rs). Their
recorded proof status is available through:

```sh
cargo djinn status
```

`status` distinguishes missing implementations, draft proofs, locally checked
proofs, and proofs accepted by the verifier. A fresh check of the supplied
implementation and proofs requires the full toolchain and this command:

```sh
cargo djinn verify
```

A successful run ends with:

```text
PASS: every obligation is proved and the axiom audit is clean.
```

Verification invokes local tools and makes no model requests. Missing tools
or mismatched paths are installation failures; their configuration is
described in [Installation](INSTALL.md).

## Inputs, outputs, and constraints

The first declaration in `src/spec.rs` specifies clamping:

```rust
use djinn::djinn;

djinn! {
    #[requires(lo <= hi)]
    pub fn clamp(x: i32, lo: i32, hi: i32) -> r: i32 {
        lo <= r <= hi;
        x < lo => r == lo;
        x > hi => r == hi;
        lo <= x <= hi => r == x;
    }
}
```

`x`, `lo`, and `hi` are inputs. `r` names the result so the body can describe
it. The body contains logical constraints, not Rust instructions: `r == lo`
states an equality; it does not assign a value. Every statement must hold.
The expression `a => b` means that whenever `a` holds, `b` must also hold.

For example, with `x = -4`, `lo = 0`, and `hi = 10`, the second constraint
requires `r = 0`. With `x = 3`, the last constraint requires `r = 3`. The
first constraint also requires the result to stay inside the range.

The clauses separate the requirement into cases. A value below the range
becomes its lower bound, a value above becomes its upper bound, and an
already valid value stays unchanged. The range constraint alone,
`lo <= r <= hi;`, would generally permit several answers. The remaining
clauses identify the intended answer in each case, including `x == lo`,
`x == hi`, and the single-value range `lo == hi`.

`#[requires(lo <= hi)]` states a **precondition**: the guarantee applies only
when the caller supplies an ordered range. Ordinary Rust callers must check
or otherwise establish it. Djinn does not insert a runtime assertion for
this attribute. The example's `run` function, below the macro block, returns
an error when `lo > hi` before calling `clamp`. This is a design decision:
the specification excludes reversed ranges rather than defining a result
for them.

After implementation, the macro exposes an ordinary Rust function that
delegates to `crate::solution::clamp`. Its Rust signature is effectively:

```rust
pub fn clamp(x: i32, lo: i32, hi: i32) -> i32
```

The named result is part of the specification language; a caller
uses `clamp(x, lo, hi)`. The parser, input validation, and formatting in the
example driver are ordinary Rust outside the verified entry points.

## Proof obligations and scope

For an ordinary deterministic function such as `clamp`, the main proof
obligations are:

| Obligation | Meaning |
|---|---|
| `unambiguous` | For fixed valid inputs, two results satisfying the specification must be equal. This establishes uniqueness, not existence by itself. |
| `impl_correct` | On inputs satisfying the precondition, the translated implementation terminates successfully and returns a result satisfying the specification. Successful termination excludes a modeled panic. |
| `exists` | A valid result exists. For implemented functions, Djinn derives this from `impl_correct`. |
| `wf`, when needed | Partial operations in the specification, such as indexing, are in their domains, and specification calls meet their preconditions. |

The verifier builds the Rust crate, extracts the selected functions with
Charon, translates them to Lean with Aeneas, regenerates the specification
and obligations, checks the proofs, and audits their axioms. A `sorry`
placeholder is not an accepted proof.

These obligations concern the written specification and the translated
model. Assessing whether the specification expresses the intended behavior
remains the author's responsibility, as does establishing preconditions
in ordinary Rust callers. The surrounding CLI is outside the verified
entry points. The tutorial's [assumptions and limitations](README.md#assumptions-and-limitations)
describe the translation tools, library models, and proof-checking
foundation on which the result depends.

## Project files

The example separates the specification, the implementation, and the
evidence used to check it:

| Path, relative to `example/clamp` | Role |
|---|---|
| `Cargo.toml` | Authored dependency, specification, tool-path, and benchmark configuration. |
| `src/spec.rs` | Authored `djinn!` declarations and the ordinary Rust driver beside them. |
| `src/lib.rs` | Authored module wiring and public exports. |
| `src/main.rs` | Authored command-line entry point. |
| `djinn/solution/mod.rs` | Rust implementation, normally written by the agent and included in code review. |
| `djinn/proofs/ClampDemo/Proofs.lean` | Proofs, normally written by the agent. Djinn creates and extends the initial skeleton. |
| `djinn/proofs/ClampDemo/Spec.lean`, `Obligations.lean`, `Vocab.lean`, `Audit.lean` | Generated files; change the specification or generator rather than editing these outputs. |
| `djinn/proofs/ClampDemo/Code/` | Aeneas-generated Lean model of the Rust code, regenerated during verification. |
| `djinn/report.toml` | Generated record of the last verification attempt, including failures. |
| `.djinnscratch/` | Local job logs, agent working directories, generated guide, intermediates, and backups. It is not source material to commit. |

The specification, implementation, and proofs belong under version control.
The examples also commit the generated Lean project and report, making
their state available for inspection and for the normal Rust build gate.
A review should include relevant generated changes alongside authored ones.

## Specification design and bounded checking

Consider a function that returns the absolute value of an `i32`. Its input
domain is every `i32`, so it needs no precondition. Its result must be
nonnegative and equal either to the input or to its negation. The return
type also matters: the magnitude of `i32::MIN` is `2147483648`, which
requires a wider type such as `i64`.

The following deliberately incomplete declaration omits one part of that
requirement. Add it inside the existing `djinn!` block in `src/spec.rs`:

```rust
    pub fn abs(x: i32) -> r: i64 {
        r == x || r == -x;
    }
```

The smoke tester can inspect this declaration independently:

```sh
cargo djinn smoke-test --only abs
```

The expected result is an `AMBIGUOUS` finding with an input and two distinct
permitted outputs. The specific counterexample may vary. With `x = -1`,
both `r = -1` and `r = 1` satisfy the constraint. The declaration says either
sign is acceptable, but an ordinary `fn` must determine a unique result.

The same reasoning explains why individual examples can conceal the error.
For `x = 0`, both alternatives give the same answer, so zero alone does not
expose the ambiguity. For `x = 5`, the declaration permits both signs.
Examining distinct input cases therefore helps identify missing constraints
before invoking verification.

Add the missing nonnegative constraint:

```rust
    pub fn abs(x: i32) -> r: i64 {
        r >= 0;
        r == x || r == -x;
    }
```

Re-running the smoke test checks the repaired declaration. Its constraints
now identify exactly one magnitude for every input: nonnegativity rules
out the wrong sign, and the second clause excludes unrelated nonnegative
numbers. Either clause alone would be insufficient. This argument explains
the repair; the bounded check provides a separate search for counterexamples.

Specification arithmetic uses mathematical values; the eventual Rust
implementation must still use machine arithmetic safely, for example by
widening to `i64` before negating. If the result type were `i32`, even the
repaired constraints would have no representable answer for `i32::MIN`.
That is a missing result, which is different from having several results.

Smoke testing uses Z3 to search for problems within its supported checks
and bounds. It starts with small integer values and sequences up to length
4 by default, and repeats suitable checks with full machine integer ranges.
A clean result establishes only that the completed searches found no
counterexample within their bounds. Skipped checks and timeouts provide no
such result. Smoke testing neither implements the function nor produces
an accepted verification report, and must be invoked explicitly because
`implement` and `verify` do not run it.

[Writing specifications](WRITING_SPECS.md) develops this design process
through further examples and exercises. The remaining sections explain
how an authored specification becomes part of a usable crate.

## Implementation and verification

Agent-assisted implementation supplies Rust code and Lean proofs for an
authored specification. It requires an authenticated Codex or Claude Code
installation and may use paid tokens. With Codex configured as described
in [Installation](INSTALL.md), the command is:

```sh
cargo djinn implement --agent codex --limit 2
```

`--agent claude` selects Claude Code instead. `--limit 2` asks the harness
to stop around two US dollars of reported or estimated usage. This is an
approximate limit because pricing estimates and delayed usage reports can
differ from actual charges. It may also be insufficient to finish a proof.

The agent receives the specification and generated guide, writes Rust and
Lean proofs in its working directory, and calls the verifier. The default
workflow reuses existing implementation and proof work and asks the agent
to complete or repair what is missing. Existing files can change and should
be included in review. Acceptance depends on the verifier's results.

The following commands inspect the resulting state, verify the current
files, and build the crate:

```sh
cargo djinn status
cargo djinn verify
cargo build
```

The new function is available as `clampdemo::spec::abs`. Adding `abs` to
the `pub use spec::{...};` list in `src/lib.rs` also exposes it as
`clampdemo::abs`. The existing CLI remains a caller of the original clamp
functions; using `abs` requires an explicit call.

If the agent stops before verification passes, inspect `status` and the
verification error, correct a flawed specification if necessary, and run
`implement` again to continue from the existing work. `cargo djinn guide`
prints the implementation guide, which is also useful when writing the
Rust implementation and Lean proofs directly.

## Development workflow and build gate

The development sequence separates specification checks from proof work
and application testing:

1. Edit the specification and its ordinary Rust callers.
2. Run `cargo djinn smoke-test`, or `--only NAME` for a focused check.
3. Run `cargo djinn implement --agent codex --limit 2` when implementation
   or proof work is needed. Alternatively, edit the implementation and
   proofs yourself.
4. Run `cargo djinn verify` to check the current files and regenerate the
   report. Use `cargo djinn status` to interpret incomplete results.
5. Run `cargo build`, `cargo test`, and the application-level checks that
   exercise the surrounding unverified Rust code.

The normal macro build gate checks the report's per-function verdicts and
whether the declaration and its specification dependencies match the
recorded tokens. A new or changed specification can therefore stop
`cargo build` with a message asking you to implement or verify it.

The gate reads saved evidence and does not fingerprint changes to the
implementation or proof files. Consequently, `verify` is required after
changing either, even if `cargo build` succeeds. The verifier bypasses the
gate for its intermediate build; editor integrations disable it for
rust-analyzer, and `DJINN_GATE=off` disables it explicitly. These builds
remain distinct from verification.

These status markers help distinguish the stages:

| Marker or message | Next step |
|---|---|
| Missing implementation or proof | Run `implement`, or supply the missing Rust or Lean code. |
| `~` / drafted | Resolve the proof errors or remaining `sorry` placeholders. |
| `✓·` / checks locally | Run full `verify`; a local proof check is not full acceptance. |
| `✓?` / changed since verification | Re-run `verify`, then repair implementation or proofs if needed. |
| `✓` / accepted by verify | Check that verification is fresh for the files you intend to use. |

## A new crate

The following commands create a separate library next to the checkout.
Creating its files requires the Rust tools; checking its specification
requires Z3. Generating the proof project and implementation additionally
requires the verification setup from [Installation](INSTALL.md), including
the absolute `DJINN_CHARON`, `DJINN_AENEAS`, and `DJINN_AENEAS_LEAN` paths.

```sh
cargo new --lib "$DJINN_REPO/../djinn-tutorial" --edition 2021
cd "$DJINN_REPO/../djinn-tutorial"
cargo add djinn --path "$DJINN_REPO/rust-djinn"
```

The dependency is the `rust-djinn/` package inside the repository, not the
repository root. Append this configuration to the new `Cargo.toml`:

```toml
[package.metadata.charon]
preset = "aeneas"

[package.metadata.djinn]
spec = "src/spec.rs"
namespace = "Tutorial"
```

`spec` is relative to the new crate. `namespace` names its generated Lean
namespace. Since this crate does not set `charon`, `aeneas`, or
`aeneas_lean` in its manifest, it uses your environment configuration.

Replace `src/lib.rs` with:

```rust
pub mod spec;

#[forbid(unsafe_code)]
#[path = "../djinn/solution/mod.rs"]
pub mod solution;

pub use spec::abs;
```

The `solution` module must exist at the crate root because the macro calls
`crate::solution::abs`. The path is relative to `src/lib.rs`. The
`#[forbid(unsafe_code)]` attribute is required by the verifier unless unsafe
code is already forbidden for the whole crate.

Create `src/spec.rs`:

```rust
use djinn::djinn;

djinn! {
    pub fn abs(x: i32) -> r: i64 {
        r >= 0;
        r == x || r == -x;
    }
}
```

The specification can now be checked:

```sh
cargo djinn smoke-test
```

With the verification toolchain configured, these commands generate and
inspect the initial proof project:

```sh
cargo djinn translate
cargo djinn status
```

`translate` creates the missing `djinn/solution/mod.rs`, the Lean project
under `djinn/proofs/`, and proof stubs. It does not implement or prove
`abs`. A normal `cargo build` should still be rejected at this stage.

Implementation and verification then follow the same sequence as in the
clamp example:

```sh
cargo djinn implement --agent codex --limit 2
cargo djinn verify
cargo build
```

After verification passes, ordinary Rust can call
`djinn_tutorial::abs(i32::MIN)` and receive `2147483648_i64`. For an
application-level exercise, add a binary or test that calls the function
with negative, zero, positive, and minimum `i32` inputs.

## Troubleshooting

| Symptom | What to check |
|---|---|
| `no such command: djinn` | The CLI binary must be installed or its build directory must be on `PATH`; see [Installation](INSTALL.md). |
| `Cargo.toml` cannot be read | Run in the crate directory, or supply `--manifest-path /path/to/crate/Cargo.toml`. The repository root is not the example crate. |
| `cannot run z3` | Install Z3 and put it on `PATH`. Smoke testing does not require an agent. |
| `AMBIGUOUS` or a contradiction | Read the reported inputs and constraints. Repair the specification before trying to prove it. |
| Missing `solution/mod.rs` | Check the module path and run `cargo djinn translate` to create the scaffold. |
| `changed since it was verified` | Re-run `verify`; if the old implementation no longer satisfies the new specification, run `implement` or repair it yourself. |
| Charon, Aeneas, or Lake fails | Inspect the named failing stage and the tool paths. Manifest settings override environment variables; the examples contain explicit paths. |
| Unsupported external function | Keep I/O and formatting in ordinary Rust drivers; use operations supported by the translation and library models in verified code. |
| `sorry`, missing theorem, or axiom-audit failure | The proof is incomplete or relies on a disallowed assumption. A successful Rust build or Lean file build alone is insufficient. |
| Agent exits without `PASS` | Read `status`, `djinn/report.toml`, and the agent logs under `.djinnscratch/jails/`; a budget or process exit is not proof completion. |

Run `cargo djinn verify` directly to reproduce the failing verification
stage without starting another agent. `cargo djinn clean --list` lists
available backups; `clean` without that flag archives and removes current
implementation and proof artifacts, so it is not a routine prerequisite.

## Editor integration and performance

The [editor integrations](../editors/README.md) expose status, smoke tests,
implementation, verification, and navigation to generated obligations and
proofs. They supplement the CLI workflow without changing the language or
verification requirements.

The supplied clamp crate also defines a benchmark workload in its manifest:

```sh
cd "$DJINN_REPO/example/clamp"
cargo djinn bench
```

The optimizer starts an agent run to search for a faster implementation,
using the same approximate spending limit as `implement`:

```sh
cargo djinn optimize --cycles 2 --limit 2 --agent codex
```

The optimizer verifies candidate implementations and measures the
configured workload before accepting an improvement. Performance is
specific to that workload and machine. Benchmark results provide evidence
about performance, while the proofs establish the functional specification.

[Writing specifications](WRITING_SPECS.md) develops the author's decisions
about what a function should guarantee. The [language tour](LANGUAGE_TOUR.md)
describes syntax and semantics, and the [example programs](../example)
provide larger specifications.
