# example/clamp — implemented by agents through `cargo djinn implement`

Four funcs (the third added after the first runs, the fourth later still),
no solution to start from.

```rust
djinn! {
    #[requires(lo <= hi)]
    pub fn clamp(x: i32, lo: i32, hi: i32) -> r: i32 {
        lo <= r <= hi;
        x < lo => r == lo;
        x > hi => r == hi;
        lo <= x <= hi => r == x;
    }

    pub fn count_negative(v: &[i32]) -> r: usize {
        r == v.iter().filter(|y| y < 0).count();
    }

    pub fn min(a: i32, b: i32) -> r: i32 {      // added later, to exercise reuse
        r <= a;
        r <= b;
        r == a || r == b;
    }

    pub fn max(a: i32, b: i32) -> r: i32 {
        r >= a;
        r >= b;
        r == a || r == b;
    }
}
```

`src/spec.rs` also holds `run`, a plain-Rust driver (`printf '3\n-4\n12\n' |
cargo run -- 0 10`), and `src/bench.rs` the workload for `optimize`.

Runs (from `cargo djinn status`; the agents' jails and logs are under
`.djinnscratch/`):

| Agent | Mode | Wall | Verifier calls | Tokens in (cached) / out | Cost | Result |
|---|---|---|---|---|---|---|
| Claude Code, claude-fable-5-1 | `--background --max-budget-usd 20` | 4 m 28 s | 5 | 1.05 M (0.99 M) / 17.7 k | $2.27 (reported) | PASS |
| Codex, gpt-6-astra | `--background --limit 5` | 3 m 11 s | 5 | 387 k (332 k) / 3.5 k | est.≈ $0.14 (priced as gpt-5) | PASS |
| Claude Code, after adding `min` (reuse) | foreground, `--limit 10` | 1 m 34 s | 2 | 308 k (278 k) / 4.0 k | $0.85 (reported) | PASS |
| Codex, all three with `-B` | `--background --limit 5` | 5 m 01 s | 5 | 604 k (567 k) / 5.6 k | est.≈ $0.17 | PASS |

Both agents proved the unambiguity obligations before writing any Rust, as
the guide asks, then implemented, read the Aeneas model, and proved
`impl_correct` with a loop invariant, a body lemma and a `@[step]` loop lemma
in the guide's shape. Neither touched the specification; the verifier would
have ignored it if they had. A series of short Claude runs afterwards
(one to three minutes, $0.77 to $1.35 each) exercised the harness and added
`max`; `cargo djinn status` lists them all. Current state: 4/4 verified.

Reproduce:

```sh
cargo djinn clean                  # archives solution/ and Proofs.lean under .djinnscratch/backup/
cargo djinn implement --agent claude --background --limit 10
cargo djinn status                 # phases per function, live view of the running jail
cargo djinn verify                 # PASS once the agent is done
```

## Optimize

`src/bench.rs` times `count_negative` over 4096 elements (with `clamp` and
`min` in the loop). Across two `optimize` runs, both re-verified: a first
Codex cycle narrowed the counter to `u32` where the length allows, 23.5 %
faster on its own baseline; a second found 2.77× (15.92 µs → 5.74 µs per
iteration), which is the `optimize:` line `status` shows now. A Claude cycle
before them was stopped by its $6 spending limit and left nothing behind.

```sh
cargo djinn optimize --cycles 2 --limit 5 --agent codex
```
