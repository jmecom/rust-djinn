# example/lz77 — the paper's LZ77 specification in Rust-djinn

A translation of `eval/lz77/lz77.spec` from the Djinnlang reference
implementation: LZ77 with optimal parsing, where the format is fixed by a
`decode` relation and the encoder by a `mincost` recurrence. `cargo djinn
translate` emits a `Spec.lean` that elaborates, with the termination of every
recursive relation discharged automatically.

## Status

Implemented and verified by Codex through `cargo djinn implement`: `verify`
prints `PASS` with 18 of 18 obligations and a clean axiom audit (28 m, est.
$1.49). `compress` is a backward dynamic-programming table over the
positions whose recorded choices are then emitted as tokens: longest match
first, then the nearest distance, as `besttoken` demands. The solution is 72
lines of Rust, the proofs 1227 lines of Lean.

A first run stopped after a minute with a Lean-checked counterexample to the
specification (est. $0.08): `encoded`, then a `fn` returning `u32` with no
precondition, has no possible output for `[Match { dist: 1, len: 4294967295
}, Lit(0)]`, whose length does not fit. `encoded` is now a `rel` returning
`int`: the number of bytes a token sequence produces is a mathematical
quantity, used only inside `compress`'s constraints, so it needs no
implementation and cannot overflow.

What the translation uses, beyond the sort/clamp/sudoku subset:

1. **A user enum in the specification.** `Token` is a Rust `enum` declared
   next to the block; constraints match on its constructors (`match t {
   Token::Lit(_) => …, Token::Match { len, .. } => … }`, each arm a block of
   constraints or a single one, exhaustive unless there is a `_` arm) and
   `Vec<Token>` / `&[Token]` are sequence types. On the Lean side Aeneas
   generates the inductive type; the generator lowers `match` to a Lean
   `match` and the smoke test to an SMT datatype.
2. **Recursive relations.** `copies`, `encoded`, `decode`, `mincost` refer to
   themselves and carry `#[decreases(..)]` — the paper's "positions are
   counted from the end" is exactly that measure. The generator emits a
   well-founded `def` whose termination proof is automatic: the body is
   written so that every guard and earlier conjunct is a hypothesis
   (`A ∧ (A → B)`), and `omega` closes the measure goals.
3. **Constants.** `WINDOW`, `MINLEN`, `MAXLEN` are `pub const`s of the crate,
   inlined as literals.

The I/O is not specified: `report` at the end of `src/spec.rs` is a plain-Rust
driver around `compress` (DESIGN.md §7); `naturalnumbertostring` from the paper
needs a floor-log in the vocabulary.

`cargo djinn smoke-test` handles `toklen` and the enum-valued checks;
recursion deeper than six unfoldings (`ismatch`, `mincost`, `besttoken`),
slices with symbolic bounds (`encoded`, `compress`) and `some` binders of
sequence type (`decode`) are reported as unsupported.
