# example/sort — the end-to-end program

Status: **`cargo djinn verify` → PASS.** Specification in Rust macros,
solution in Rust, proofs in Lean against the Aeneas model, axiom audit clean.
The specification: `perm` (a list's permutations, a `rel`), `permsuperset`,
`sort` (in place, ascending) and `max`,
plus a plain-Rust driver `run`.

| File | Owner | Trusted? | Regenerated? |
|---|---|---|---|
| `src/spec.rs` | human | yes (the spec) | no |
| `src/lib.rs`, `Cargo.toml` | human | yes (glue, config) | no |
| `djinn/solution/mod.rs` | LLM | no | no (LLM edits) |
| `djinn/proofs/SortProg/Code/*` | Aeneas | yes (toolchain output) | every verify |
| `djinn/proofs/SortProg/Spec.lean` | driver | yes | every verify |
| `djinn/proofs/SortProg/Obligations.lean` | driver | yes (pins proof types) | every verify |
| `djinn/proofs/SortProg/Audit.lean` | driver | yes | every verify |
| `djinn/proofs/SortProg/Proofs.lean` | LLM | no | written once as a skeleton |

The first proofs were the ones from `../calib`, ported (namespace, and the
stub `SortProg.spec.sort` unfolding to `SortProg.solution.sort`). The
current solution (quicksort plus an insertion pass) and proofs are the
agents': written by the optimize cycles below, then repaired twice by
`implement` runs after the sort order in the specification was flipped to
descending and back (Claude, $1.93, 2 m 40 s; Codex, est. $0.11, 1 m 51 s).

## Run

```sh
# from this directory, with the tools built and on PATH (docs/INSTALL.md)
cargo djinn translate   # emit Spec/Obligations/Audit (+ Proofs skeleton once)
cargo djinn verify      # cargo build → charon → aeneas → lake build → axiom audit
```

`verify` prints `PASS` and exits 0, or `FAIL: <stage>` with the last lines of
that stage. Tool paths and the Lean namespace come from
`[package.metadata.djinn]` in `Cargo.toml`. The Lean project's
`.lake/packages` is a symlink to the shared cache
`~/.cache/djinn/lake-packages`, which `verify` creates when the cache exists;
without one, run `lake update` and `lake exe cache get` in `djinn/proofs/`.

## Optimize

`src/bench.rs` holds the workload (`bench = "bench::workload"` in
`Cargo.toml`): sorting 8192 pseudo-random `i32`. Starting from the
calibration insertion sort:

```sh
cargo djinn optimize --cycles 2 --limit 40 --agent claude
```

| cycle | change | time/iter | speedup | verify | cost | wall |
|---|---|---|---|---|---|---|
| — | insertion sort (calibration) | 4.677 ms | 1× | PASS | | |
| 1 | Shell sort | 230.68 µs | 20.3× | PASS, accepted | $2.68 | 7 m 58 s |
| 2 | quicksort to runs of 16 + insertion pass | 73.00 µs | 64.1× | PASS, accepted | $5.75 | 14 m 24 s |

Both proofs were rewritten by the agent (the recursive `quicksort` is a
`partial_fixpoint` in the Aeneas model); $8.42 in total. The history is in
`.djinnscratch/optimize.json`, and `cargo djinn status` shows the summary
line. A Ctrl-C during a cycle stops the agent and restores the last
verified checkpoint.
