# example/broken — flawed specifications for `cargo djinn smoke-test`

Six funcs, five of them wrong on purpose: a `max` that forgot "none is
larger" (ambiguous), an `abs` with no case for zero (an input without an
output), a sortedness constraint indexing one past the end (ill-formed), an
`ensures` that does not follow, and a contradictory pair of constraints. The
sixth is a correct `clamp` as a control. This crate is never meant to be
implemented; run

```sh
cargo djinn smoke-test
```

and compare with the comments in `src/spec.rs`.
