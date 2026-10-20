# First steps with Djinn

Djinn lets you describe a Rust function by the conditions its result must
satisfy. Your task is to make that description precise: which inputs are
allowed, what a result means, and what should happen at the boundaries.
An implementation supplies the algorithm; Lean proofs establish that the
translated implementation satisfies the written conditions.

This guide starts with a working example, helps you write and repair a
small specification, and then shows the implementation and verification
workflow. You do not need to know Lean to follow it.

Complete the Rust-tools section of [Installation](INSTALL.md) first. Running
the supplied example needs only those tools. Add Z3 for the specification
exercise; regenerating and checking proofs needs the full Charon, Aeneas,
and Lean setup. An editor
extension and an AI agent are optional until their sections below.

The commands assume `DJINN_REPO` points to your checkout, as set in the
installation guide. Start in the example crate and stay there unless a step
explicitly changes directories:

```sh
cd "$DJINN_REPO/example/clamp"
```

## Run an existing implementation

The example already includes an implementation, proofs, and a verification
report. Run its ordinary Rust command-line program without starting an agent:

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
functions declared in [`src/spec.rs`](../example/clamp/src/spec.rs).

Inspect the recorded proof status:

```sh
cargo djinn status
```

`status` distinguishes missing implementations, draft proofs, locally checked
proofs, and proofs accepted by the verifier. It does not run the full
verification pipeline. To check the supplied implementation and proofs on
your machine, after configuring the full toolchain, run:

```sh
cargo djinn verify
```

A successful run ends with:

```text
PASS: every obligation is proved and the axiom audit is clean.
```

This invokes local verification tools, not an AI agent. If a tool is missing
or an example's configured path does not match your installation, follow the
path configuration and troubleshooting sections in [Installation](INSTALL.md).

## Read the specification

Open `src/spec.rs`. Its first declaration is:

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

Notice how the clauses express the behavior in words: a result is in range;
a value below the range becomes its lower bound; a value above becomes its
upper bound; an already valid value stays unchanged. Merely writing
`lo <= r <= hi;` would leave many answers possible. The remaining clauses
identify the intended answer in each case. They also cover `x == lo`,
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

The named result is part of the specification language; a caller simply
uses `clamp(x, lo, hi)`. The parser, input validation, and formatting in the
example driver are ordinary Rust outside the verified entry points.

## Understand what gets proved

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

The guarantee is about the written specification and the translated model.
You still need to decide whether the specification describes the intended
behavior and whether callers establish its preconditions. The translation
tools, supported library models, and proof-checking foundation are part of
the trust assumptions. A proof for `clamp` does not verify the surrounding
CLI, all Rust library code, or the whole application. Read the
[language tour](LANGUAGE_TOUR.md) for the supported language and its limits.

## Know which files to edit

The example separates the specification, the implementation, and the
evidence used to check it:

| Path, relative to `example/clamp` | Role |
|---|---|
| `Cargo.toml` | Authored dependency, specification, tool-path, and benchmark configuration. |
| `src/spec.rs` | Authored `djinn!` declarations and the ordinary Rust driver beside them. |
| `src/lib.rs` | Authored module wiring and public exports. |
| `src/main.rs` | Authored command-line entry point. |
| `djinn/solution/mod.rs` | Rust implementation, normally written by the agent; inspect it as part of review. |
| `djinn/proofs/ClampDemo/Proofs.lean` | Proofs, normally written by the agent. Djinn creates and extends the initial skeleton. |
| `djinn/proofs/ClampDemo/Spec.lean`, `Obligations.lean`, `Vocab.lean`, `Audit.lean` | Generated files; change the specification or generator rather than editing these outputs. |
| `djinn/proofs/ClampDemo/Code/` | Aeneas-generated Lean model of the Rust code, regenerated during verification. |
| `djinn/report.toml` | Generated record of the last verification attempt, including failures. |
| `.djinnscratch/` | Local job logs, agent working directories, generated guide, intermediates, and backups. It is not source material to commit. |

Keep the specification, implementation, and proofs under version control.
The examples also commit the generated Lean project and report so their
state can be inspected and the normal Rust build gate can read the report.
After making a change, review the relevant generated changes along with
your authored changes.

## Write an incomplete specification and diagnose it

Suppose you want a function that returns the absolute value of an `i32`.
Before writing syntax, settle three questions:

1. **Inputs:** should every `i32` be accepted? Here, yes: no precondition.
2. **Result:** what describes an absolute value? It is nonnegative and
   equals either the input or its negation.
3. **Boundaries:** can the result type hold every answer? The magnitude of
   `i32::MIN` is `2147483648`, so use `i64` for the result.

To see what a missing condition looks like, add this deliberately incomplete
declaration **inside the existing `djinn!` block** in `src/spec.rs`:

```rust
    pub fn abs(x: i32) -> r: i64 {
        r == x || r == -x;
    }
```

Ask the smoke tester to inspect just this declaration:

```sh
cargo djinn smoke-test --only abs
```

Expect an `AMBIGUOUS` finding with an input and two distinct permitted
outputs. The specific counterexample may vary. For example, with `x = -1`,
both `r = -1` and `r = 1` satisfy the constraint. The declaration says either
sign is acceptable, but an ordinary `fn` must determine a unique result.

Before reading the repair, try the same reasoning for `x = 0` and `x = 5`.
For zero, both alternatives give the same answer. For five, the declaration
again permits both signs. A few examples can reveal missing intent even
before a tool runs.

Add the missing nonnegative constraint:

```rust
    pub fn abs(x: i32) -> r: i64 {
        r >= 0;
        r == x || r == -x;
    }
```

Now run the same smoke test again. Every input has exactly one nonnegative
magnitude. Each clause has a job: nonnegativity rules out the wrong sign;
the second clause rules out unrelated nonnegative numbers. Either clause
alone would be insufficient.

Specification arithmetic uses mathematical values; the eventual Rust
implementation must still use machine arithmetic safely, for example by
widening to `i64` before negating. If the result type were `i32`, even the
repaired constraints would have no representable answer for `i32::MIN`.
That is a missing result, which is different from having several results.

Smoke testing uses Z3 to search for problems within its supported checks
and bounds. It starts with small integer values and sequences up to length
4 by default, and repeats suitable checks with full machine integer ranges.
A clean result is useful feedback, but it is not a proof. Some checks can
also be skipped or time out; read the individual results. The command does
not implement the function or produce an accepted verification report.
Run it explicitly: `implement` and `verify` do not run it for you.

For more practice turning intended behavior into complete specifications,
continue with [Writing specifications](WRITING_SPECS.md). The remaining
sections here explain how to turn a specification into a usable crate.

## Implement and verify the new function

This step is optional if you only want to explore the language. It starts
an external AI agent and may use paid tokens. Configure and authenticate
Codex or Claude Code as described in [Installation](INSTALL.md), then choose
one agent:

```sh
cargo djinn implement --agent codex --limit 2
```

Use `--agent claude` instead if that is your configured agent. `--limit 2`
asks the harness to stop around two US dollars of reported or estimated
usage. It is not a strict billing cap: pricing estimates and delayed usage
reports can differ from actual charges. The budget may also be insufficient
to finish a proof.

The agent receives the specification and generated guide, writes Rust and
Lean proofs in its working directory, and calls the verifier. The default
workflow reuses existing implementation and proof work and asks the agent
to complete or repair what is missing. Existing files can change, so inspect
the resulting diff. A successful run requires the verifier to accept the
obligations; an agent's description of success is not the acceptance check.

After it finishes, inspect the status, rerun verification if you have edited
any code or proofs, and build:

```sh
cargo djinn status
cargo djinn verify
cargo build
```

The new function is available as `clampdemo::spec::abs`. Add `abs` to the
`pub use spec::{...};` list in `src/lib.rs` if you also want the shorter
`clampdemo::abs` path. The existing CLI does not call `abs` automatically.

If the agent stops before verification passes, inspect `status` and the
verification error, correct a flawed specification if necessary, and run
`implement` again to continue from the existing work. `cargo djinn guide`
prints the implementation guide if you want to inspect the obligations or
work on the Rust and Lean files yourself.

## Use the edit, check, implement, and build loop

For subsequent changes, use this sequence from the crate directory:

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

This gate is not a fresh proof run, and it does not fingerprint changes to
the implementation or proof files. Run `verify` after changing either,
even if `cargo build` succeeds. The verifier bypasses the gate for its own
intermediate build. Editor integrations also disable it for rust-analyzer,
and `DJINN_GATE=off` disables it explicitly; such a build is not evidence
of verification.

These status markers help distinguish the stages:

| Marker or message | Next step |
|---|---|
| Missing implementation or proof | Run `implement`, or supply the missing Rust or Lean code. |
| `~` / drafted | Resolve the proof errors or remaining `sorry` placeholders. |
| `✓·` / checks locally | Run full `verify`; a local proof check is not full acceptance. |
| `✓?` / changed since verification | Re-run `verify`, then repair implementation or proofs if needed. |
| `✓` / accepted by verify | Check that verification is fresh for the files you intend to use. |

## Start a crate of your own

This section creates a separate library next to the checkout. You can create
the files with the Rust tools and check the specification after adding Z3.
Before generating its proof project or implementation, complete the full
verification setup from [Installation](INSTALL.md), including the absolute
`DJINN_CHARON`, `DJINN_AENEAS`, and `DJINN_AENEAS_LEAN` paths. No editor
integration is required.

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

Check the specification without starting an agent:

```sh
cargo djinn smoke-test
```

Once the full verification toolchain is configured, generate its initial
project files:

```sh
cargo djinn translate
cargo djinn status
```

`translate` creates the missing `djinn/solution/mod.rs`, the Lean project
under `djinn/proofs/`, and proof stubs. It does not implement or prove
`abs`. A normal `cargo build` should still be rejected at this stage.

When you are ready to run an agent, use the same explicit implementation
step and check its result:

```sh
cargo djinn implement --agent codex --limit 2
cargo djinn verify
cargo build
```

After verification passes, ordinary Rust can call
`djinn_tutorial::abs(i32::MIN)` and receive `2147483648_i64`. For an
application-level exercise, add a binary or test that calls the function
with negative, zero, positive, and minimum `i32` inputs.

## Resolve common failures

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

## Optional editor and performance workflows

The [editor integrations](../editors/README.md) expose status, smoke tests,
implementation, verification, and navigation to generated obligations and
proofs. They supplement the same CLI workflow. You can finish this tutorial
with any editor.

To experiment with performance, return to the supplied clamp crate, whose
manifest defines a benchmark workload:

```sh
cd "$DJINN_REPO/example/clamp"
cargo djinn bench
```

If you want an agent to search for a faster implementation, this command
also starts a potentially paid run:

```sh
cargo djinn optimize --cycles 2 --limit 2 --agent codex
```

The optimizer verifies candidate implementations and measures the
configured workload before accepting an improvement. Performance is
specific to that workload and machine; benchmark results are not part of
the functional specification. Start with correct, useful specifications
and measurements before optimizing.

Continue with [Writing specifications](WRITING_SPECS.md) to practice deciding
what a function should guarantee. Use the [language tour](LANGUAGE_TOUR.md)
for syntax and semantics, and the [example programs](../example) for larger
specifications.
