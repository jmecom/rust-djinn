# rust-djinn

rust-djinn lets you specify a Rust function by describing how its inputs and
outputs relate. A coding agent writes an implementation and Lean proofs that
the implementation satisfies those constraints. The verifier checks the proofs;
the rest of your program calls the resulting function like ordinary Rust.

For example, the maximum of a nonempty list is an element of the list that is
at least as large as every other element:

```rust
use djinn::djinn;

djinn! {
    #[requires(list.len() >= 1)]
    pub fn maximum(list: &[i32]) -> r: i32 {
        r in list;
        for x in list { x <= r; }
    }
}
```

Here `r` names the result. The body states constraints, not instructions for
computing it: `for` means that the constraint holds for every element. Both
clauses matter. Membership alone permits the wrong element; the upper-bound
constraint alone permits a value larger than every element. Together, they
specify the maximum without choosing an algorithm.

Writing these constraints is the human's main task. The guides below explain
how to turn intended behavior into a specification, identify missing cases,
and use counterexamples to improve it. Djinn functions can live alongside
ordinary Rust, so you can start with one function.

**This is research software.** The implementation and trusted models are
experimental. Read [Verification and its limits](#verification-and-its-limits)
before relying on the guarantees.

## Start here

| Guide | What you will learn |
|---|---|
| [Onboarding](docs/FIRST_STEPS.md) | Run an example, repair an ambiguous specification, and create your first crate |
| [Writing specifications](docs/WRITING_SPECS.md) | Derive constraints from requirements, handle edge cases, and decide whether the result is fully specified |
| [Language tour](docs/LANGUAGE_TOUR.md) | Express constraints, reusable relations, data types, mutation, and deliberate choices |
| [Installation](docs/INSTALL.md) | Set up the tools needed for each stage, plus optional editor integration |
| [Documentation and examples](docs/README.md) | Choose an example and find the relevant implementation files |

You need Rust and Cargo to try the checked-in `clamp` example. You do not need
a coding agent or the Lean toolchain for this first run:

```sh
git clone https://github.com/shenniger/rust-djinn.git
cd rust-djinn
export DJINN_REPO="$PWD"
printf '3\n-4\n12\n' | cargo run --locked --manifest-path example/clamp/Cargo.toml -- 0 10
```

After Cargo's build output, the program prints:

```text
1 negative input(s); clamped to [0, 10]: [3, 0, 10]; smallest: Some(0)
```

This compiles the supplied implementation using its checked-in verification
report. It does not rerun the proofs. Continue with [onboarding](docs/FIRST_STEPS.md)
to inspect the specification and make your first change. The
[writing workshop](docs/WRITING_SPECS.md) develops a new specification step by step.

## The development workflow

You write specifications in `djinn! { … }` blocks inside a Rust crate. The
agent writes ordinary Rust in `djinn/solution/` and proofs in `djinn/proofs/`.
Your Rust code calls the functions exposed by the macro.

Once the tools are installed, run these commands in your example or application
crate, which is separate from the repository's `rust-djinn/` tool workspace:

```sh
cargo djinn smoke-test                    # find small counterexamples with Z3
cargo djinn implement --limit 5           # ask the agent to implement and prove
cargo djinn status                        # inspect saved results and outstanding obligations
cargo djinn verify                        # rerun translation, proof checking, and the axiom audit
cargo build                              # compile the Rust application
```

`implement` defaults to Codex; `--agent claude` selects Claude Code. It consumes
agent usage. `--limit` is Djinn's usage-based stop mechanism, not a guarantee
of an exact provider bill. See [agent setup](docs/INSTALL.md) before running it.
The other commands above do not invoke a coding agent. Smoke tests are bounded
searches, so finding no counterexample is not a proof.

After changing a specification, use `implement` to update its implementation
and proofs. After editing generated Rust or proofs yourself, rerun `verify`.
The ordinary build gate consults the report and specification dependencies;
it is not a replacement for fresh verification of modified implementation code.

For performance work, provide a benchmark workload and use `cargo djinn bench`
and `cargo djinn optimize`. Optimization candidates must pass verification and
improve the measured workload to be retained. For a fully specified function,
this preserves the specified result. Functions marked `#[weakly_specified]`
deliberately leave choices open and need additional review; the
[language tour](docs/LANGUAGE_TOUR.md) explains that distinction.

## Verification and its limits

For an ordinary, fully specified function, the proof obligations are:

| Obligation | Meaning |
|---|---|
| `unambiguous` | Two outputs satisfying the specification for the same valid input are equal |
| `exists` | Every input satisfying the precondition admits an output |
| `impl_correct` | Under the precondition, the modeled implementation terminates successfully and returns an output satisfying the specification |
| `ens_0`, `ens_1`, … | Each optional `#[ensures]` clause follows from the specification |

The generated implementation is translated through Charon and Aeneas into a
Lean model. Lean checks the proof against that model, and Djinn audits the
axioms used. A successful verification establishes properties of that model
under its assumptions, rather than relying on the agent's claim of correctness.

The result still depends on the specification expressing your intent and on
the trusted components: Djinn's translation and audit, Charon, Aeneas, Lean,
and the library models. Those models currently include parts of `std`, `core`,
`alloc`, and `memchr`; their presence is not evidence of an independent audit.
Ordinary Rust callers must uphold `#[requires]`: the macro does not insert
runtime precondition checks or verify the whole application.

Current examples cover integer arithmetic, slices, vectors, strings, structs,
enums, `Option`, `Result`, and recursion, within the subset supported by the
parser and translation pipeline. Arbitrary Rust syntax and calls into arbitrary
crates are not supported. Proof search can fail or take a long time even for a
valid specification. Runtime performance and absence of timing side channels
are not specified or proved; these guarantees do not establish suitability for
cryptographic code.

## Repository layout

```text
docs/                   installation, onboarding, writing workshop, language tour
example/                specifications, implementations, proofs, and Rust drivers
rust-djinn/             Cargo workspace containing the library and tools
  src/                  djinn library entry point
  syntax/               parser, checks, and lowering to Lean
  macros/               djinn! macro and build gate
  cargo-djinn/           verification and agent driver
  lsp/                  language server
editors/                VS Code extension and Neovim configuration
```

For background and the original Dafny implementation, see the
[blog post](https://henniger.dev/post/djinn) and the paper:

> Simon Henniger, Stephen Chong, Nada Amin. *Djinnlang: Higher-Level
> Programming by Unambiguous Specification with an LLM in the Compiler.*
> 2026. [arXiv:2609.23954](https://arxiv.org/abs/2609.23954)

See [LICENSE.txt](LICENSE.txt) for the license.
