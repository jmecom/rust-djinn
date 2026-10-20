# choice — leaving decisions to the implementer

The specification language's `any x: T where c;` and `#[weakly_specified]`
(see the [language tour](../../docs/LANGUAGE_TOUR.md)). Five functions:

- `checked_div`: a top-level choice — the error message on division by
  zero, any string of at least 10 characters.
- `safe_div`: a caller of a weakly specified `fn` inherits its choice (one
  per call site, lifted into `safe_div_body`); its `ensures` must hold for
  every admissible choice.
- `shrink`: a choice per `for` position — in Lean a function
  `w : List U8 → ℤ → U8` of the input and the index.
- `pick` / `pick_twice`: scalar versions the smoke test can check.

`djinn/proofs/AnyDemo/Spec.lean` has `f_body` (choices explicit) and `f_spec`
(their existential closure); `Obligations.lean` states `unambiguous` and `wf`
on `f_body`, quantified over the choices, and `ens_*`, `impl_correct`,
`exists` on `f_spec`. `cargo djinn smoke-test` reports unambiguity modulo the
choices and an `ensures` that depends on a choice.

## Status

Implemented and verified by Codex through `cargo djinn implement`: `verify`
prints `PASS` with 21 of 21 obligations and a clean axiom audit (8 m 17 s,
est. $0.42). With no workload to push them anywhere, the agent took the
simplest admissible choice everywhere, which is what a human reviewing the
`#[weakly_specified]` functions should check:

| fn | left open by the specification | chosen |
|---|---|---|
| `checked_div` | the error message, at least 10 bytes | `"division by zero"` |
| `safe_div` | inherits `checked_div`'s message | 0 on error; the message is never used |
| `shrink` | each byte `w <= v[i]` | 0 |
| `pick` | any `k` with `lo <= k <= hi` | `lo` |
| `pick_twice` | inherits `pick`'s choice | `pick(lo, hi)`, so `lo` |
