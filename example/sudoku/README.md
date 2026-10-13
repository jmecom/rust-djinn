# example/sudoku — the paper's Sudoku specification in Rust-djinn

A translation of `eval/sudoku/sudoku.spec` from the Djinnlang reference
implementation (the lexicographically least completion of a puzzle, or the
verdict that there is none). Implemented and fully verified by agents,
several times over: `cargo djinn verify` prints `PASS` with 32 of 32
obligations and a clean axiom audit. The files in place are Codex's, from
the last two runs in the table below: `djinn/solution/mod.rs` (93 lines, a
recursive search trying digits in ascending order) from run 6, and the proofs
split over `djinn/proofs/Sudoku/Proofs.lean` and `Proofs/Solver.lean` (982
lines), written in run 6 and repaired in run 7.
Claude's earlier version (139 and 1044 lines) is kept under
`.djinnscratch/backup/`.

What changed in translation:

| Dafny version | Here |
|---|---|
| `datatype Answer = NoSolution \| Solution(grid)` in the ambient | `Option<Vec<u8>>`; `a.issolution()` is `a.is_some()`, `a.grid` is `a.unwrap()` |
| `seq<int>` grids | `&[u8]` inputs, `Vec<u8>` outputs |
| `func sameunit(i: int, j: int)`, `func prefixthen(.., i: int, d: int)` | `rel`s with `int` parameters: they are called with the loop indices, which are mathematical integers, and a `fn` must have Rust types |
| strings and chars (`digitof`, `showgrid`, `"no solution\n"`) | byte sequences; the text is a `rel` listing its bytes |
| `proc printstring`, `proc main` | not specified: `solve_stream` at the end of `spec.rs` is a plain-Rust driver that calls the verified functions (DESIGN.md §7) |
| — | `showgrid` requires `c.len() == 81` (and `showanswer` passes it on): for a slice of length `usize::MAX` no `Vec` one longer exists, so the unconditional version had no implementation. Found by the agent. |

## The runs

```sh
cargo djinn implement --agent claude --background          # run 1
cargo djinn implement --agent claude --background --limit 20   # run 2, after the fixes below
```

| run | agent | wall | tokens in (cached) / out | verifies | cost | result |
|---|---|---|---|---|---|---|
| 1 | Claude Code | 38 m 34 s | 13.9 M (13.6 M) / 163 k | 3 | $19.02 | all six implemented, 29/32 proved; blocked |
| 2 (reuse) | Claude Code | 5 m 29 s | 2.6 M (2.5 M) / 18 k | 2 | $3.94 | PASS, 32/32 |
| 3 (from scratch) | Codex | 25 m 53 s | 5.1 M (5.0 M) / 30 k | 3 | est. $1.11 | PASS, 32/32 |
| 4 (from scratch) | Codex | 12 m 31 s | 3.7 M (3.6 M) / 26 k | 5 | est. $0.84 | PASS, 32/32 |
| 5 (from scratch) | Claude Code | 21 m 40 s | 10.0 M (9.8 M) / 108 k | 2 | $12.11 | PASS, 32/32 |
| 6 (from scratch) | Codex | 22 m 12 s | 3.4 M (3.2 M) / 28 k | 5 | est. $0.92 | PASS, 32/32; the solution in place |
| 7 (reuse) | Codex | 2 m 22 s | 597 k (547 k) / 2.1 k | 5 | est. $0.15 | PASS, 32/32; the proofs in place |

Two further Codex runs exited without finishing their turn (a CLI error,
$0.64 together), and two Claude runs on 2026-10-05 were stopped by a $15
spending limit each; `cargo djinn status` lists everything.

Run 1 ended with a correct diagnosis of why `verify` could not pass: a
zero-parameter `rel` (`nosolutiontext`) was printed as `∀ , …` in
`Obligations.lean`; `a.is_some() => completion(g) == a.unwrap()` lifted the
call outside the implication, demanding a completion for every puzzle (the
agent proved the generated `ens_1` false); and the `showgrid` gap above.
The first two were generator bugs (`&&`/`||`/`=>` now scope their right
operand like Rust's short-circuit operators); the third a specification
fix. Run 2 kept the implementation and repaired the proofs.

Run 7 repaired the proofs after a change to the generator: `prefixthen(..)
not in domain(completion)` used to be lowered as "some `h` that `prefixthen`
gives has no completion" (`∃ h, prefixthen_spec … h ∧ ¬…`) and is now "no
`h` that `prefixthen` gives has one" (`¬∃ h, prefixthen_spec … h ∧ …`). The
two agree here, since `prefixthen` is a function, but the old proof built the
witness `h` and no longer matched the statement. The agent kept the Rust and
rewrote the two affected steps.

`cargo djinn smoke-test` (about six seconds) finds nothing wrong. The
declarations whose preconditions demand 81-cell inputs are reported as
unreachable within the default bounds rather than explored; the byte helpers
are checked in full; `solve` and `showanswer` are skipped because the smoke
test does not model `Option<Vec<u8>>` yet.

## The driver

The I/O is ordinary Rust in the same file as the specification:
`solve_stream` at the end of `src/spec.rs` reads lines, skips those that are
not 81 characters (the precondition of `parsepuzzle`), and calls
`parsepuzzle`, `solve` and `showanswer` through their stubs; `src/main.rs`
hands it standard input and output. Charon starts its translation from the
specification's functions, so the driver is never translated.

```
printf '530070000600195000098000060800060003400803001700020006060000280000419005000080079\n' | cargo run --quiet
534678912672195348198342567859761423426853791713924856961537284287419635345286179
```
