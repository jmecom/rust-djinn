# example/calib — the proved instance

`sort` (insertion sort on `&mut Vec<i32>`) and `max` (on `&[i32]`) from
`example/sort`, as a plain crate, translated by Charon + Aeneas and proved
against the hand-emitted Djinn obligations. Status: **all obligations proved,
axiom audit clean** (only `propext`, `Classical.choice`, `Quot.sound`).

| File | Role | Lines (content) |
|---|---|---|
| `src/lib.rs` | the "LLM solution": two Rust functions | 26 |
| `proofs/Calib/Code/Funs.lean` | Aeneas output (regenerated) | 123 |
| `proofs/Calib/Spec.lean` | trusted relations, as the driver would emit them | 38 |
| `proofs/Calib/Obligations.lean` | trusted, type-pinned obligations | 54 |
| `proofs/Calib/Proofs.lean` | the proofs (the LLM's deliverable) | 318 |
| `proofs/Calib/Audit.lean` | `#print axioms` for every obligation | 12 |

For comparison, the three declarations these obligations come from (`perm`,
`sort`, `max` in `../sort/src/spec.rs`) are a dozen lines of Rust-embedded
DSL. This crate is a snapshot: `example/sort` has since moved on (its solution
and proofs were rewritten by agents), while the files here stay as they
were proved by hand.

## Reproduce

Toolchain (built once under `../../tools/`, see `docs/INSTALL.md`): Aeneas
`557eff83` with its pinned Charon `c8f15d7d`, Rust `nightly-2026-09-17`,
OCaml 5.4 via opam, Lean `v4.31.0`, Mathlib `v4.31.0` through the Aeneas
lakefile. The Lean project's `.lake/packages` is a symlink to the shared
cache `~/.cache/djinn/lake-packages`.

```sh
export PATH=/opt/homebrew/opt/rustup/bin:$PATH
T=../../tools/aeneas
$T/charon/bin/charon cargo --preset=aeneas --dest-file=calib.llbc
$T/bin/aeneas -backend lean calib.llbc -dest proofs -subdir Calib/Code \
    -split-files -namespace Calib -emit-json
cd proofs
lake build                      # Spec, Obligations (pins Proofs by type)
lake env lean Calib/Audit.lean  # axiom audit
```

Full `lake build` from a warm cache takes about 25 s wall clock; the Aeneas
library itself builds from source the first time (about 15 minutes on an
M4 Max) and Mathlib comes from the cache.
