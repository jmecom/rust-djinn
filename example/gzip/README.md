# example/gzip — a verified gzip, translated from lean-zip's specification

A Djinn translation of the specification of [lean-zip](https://github.com/kim-em/lean-zip), the
verified DEFLATE codec in Lean 4. Three functions are specified in `src/spec.rs` and implemented by
agents in `djinn/solution/mod.rs`, each with a Lean proof in `djinn/proofs/`:

| Function | Specification |
|---|---|
| `decompress(s) -> Option<Vec<u8>>` | `Some(content)` exactly when `s` is one gzip member (any header flags, matching CRC-32 and length) |
| `compress(data, level) -> Vec<u8>` | the gzip header for `level`, followed by *any* member that `decompress` reads back as `data` (`any`, see [docs/ANY.md](../../docs/ANY.md)); `ensures(decompress(out) == Some(data))` |
| `crc32(data) -> u32` | the CRC-32 of RFC 1952 |

`cargo djinn status`: 3/3 functions implemented and fully verified, axiom audit clean.

## The specification

lean-zip specifies the format as a decoder, a function from bits to bytes. Djinn has no monad, so
each parsing step is a relation that reads `s` from bit `i` and returns the bit `j` where it stops:
`stored(s, i, prev, out) == j` means "bits `i..j` are a stored block that extends `prev` to `out`".
A read past the end or a wrong value leaves the relation empty. Three layers:

1. **Bits and codes.** `bit`, `field`, `code`, and canonical Huffman codes (RFC 1951 §3.2.2) as
   arithmetic: `shorter`, `earlier`, `codeword`, the Kraft inequality `valid`, and `symbol`.
2. **Blocks.** `symbols`, `stored`, `tables` and `lengths` (the dynamic header), `block`, `blocks`;
   the length and distance tables are recurrences (`lbase`, `dbase`).
3. **gzip.** `header` with the optional fields, `member` with the trailer, and the CRC-32 relations.

`compress` pins only the header and the round trip: the parse, the block split, the codes and what
each level trades are the implementer's (`#[weakly_specified]`). The intent
given to the agents was level 1 radically fast, level 10 radically dense.

## Results

All measurements are on the Silesia corpus (12 files) on one core. Each figure is a geomean over
files or streams.

**Decompression**, of lean-zip's 72 Silesia streams (each file encoded by libdeflate at levels 1, 3,
6, 9 and 12, and by zopfli). Each stream is timed as the median of 5 runs, the best of 10 passes is
kept, and the 72 results are combined by geomean. Every decoder runs under lean-zip's own harness
and timing code, which reports MiB/s (its output labels them "MB/s"). The comparators decode raw
DEFLATE, so none of them computes a checksum:

| Decoder | MiB/s |
|---|---|
| **this crate, with CRC check** | **666** |
| this crate, without CRC check | 787 |
| libdeflate | 657 |
| zune-inflate (checksum off) | 652 |
| zlib-rs | 594 |
| zlib-ng | 588 |
| miniz_oxide | 445 |
| zlib | 393 |
| lean-zip | 283 |

**Compression**, against lean-zip at each level (lean-zip's figures are from its harness, so they are
MiB/s):

| Level | Ratio | MB/s | lean-zip ratio @ MB/s |
|---|---|---|---|
| 1 | 0.3907 | 159.5 | 0.3928 @ 219.8 |
| 2 | 0.3636 | 115.4 | 0.3581 @ 133.1 |
| 3 | 0.3419 | 88.8 | 0.3426 @ 78.5 |
| 4 | 0.3345 | 76.1 | 0.3321 @ 60.2 |
| 5 | 0.3304 | 66.4 | 0.3273 @ 51.8 |
| 6 | 0.3294 | 63.1 | 0.3220 @ 33.8 |
| 7 | 0.3280 | 57.5 | 0.3182 @ 31.8 |
| 8 | 0.3174 | 20.0 | 0.3175 @ 22.5 |
| 9 | 0.3158 | 15.2 | 0.3139 @ 3.4 |
| 10 | 0.3113 | 11.0 | 0.3087 @ 2.0 |

Comparing the curves, the compressor beats lean-zip in both speed and ratio around lean-zip's
levels 3 to 5, and is nearly 4× faster at lean-zip's level-9 ratio. lean-zip is ahead at the fast
end, around its level 7, and in its densest output. miniz_oxide is beaten everywhere except at its
level 1.

## How it got there

Both sides started from a straightforward verified implementation and were optimised by
`cargo djinn optimize`, Claude and Codex taking turns. Each round must keep every proof, and is kept
only if it measures faster. Decompression went from 675 ms to 6.8 ms per pass of its workload (99×)
in 125 rounds. Compression got 8.3× faster over its ten levels in 108 rounds, by the harness's count; its corpus gained a binary file along the way.
Some of what the agents reported:

> Expanded the Huffman lookup table from 8 to 10 bits (256 to 1,024 entries), reducing costly symbol
> scans. Updated the table invariants and decoder proofs. … **52.6% faster**.
> — Codex, decompression round 1

> Replaced 16 Huffman counting scans with one pass using four independent histograms. Skipped
> unnecessary overlap repair when copy length ≤ distance. Updated the Lean proofs.
> — Codex, decompression round 86

> Level 10 spent 30% of its time (51 ms) in hinted re-pricing passes, and the pass loop stopped
> early only when a block's refitted prices were *exactly* equal to the ones it was parsed with.
> — Claude, compression round 60 (level 10 then 13% faster)

> Found a real fixed cost: each compress call at L8+ frees ~770 KB, glibc trims the heap and the
> next call page-faults it back (~170–200 µs per file).
> — Claude, compression round 98

## Running

```sh
cargo run --release -- -6 file > file.gz       # compress at level 0..10 (default 6)
cargo run --release -- -d file.gz > file       # decompress
cargo run --release -- --sizes [FILE...]       # compressed sizes next to gzip -9 (the built-in corpus if no files)
cargo run --release -- --workload [FILE...]    # compression time per file
cargo run --release -- -d --workload [FILE...] # decompression time per stream
cargo djinn status                             # what is verified
cargo djinn verify                             # re-check every proof
```

## Optimising

`cargo djinn bench` times the compressor's workload (`bench::workload_compress`, the built-in
corpus at every level in `bench_points`); `DJINN_BENCH_SCALE=4` gives a corpus of about 1 MB.

**Use your own binary sample.** The corpus is synthetic text, source, tables, runs and random
data, generated in process; no sample files ship with the crate. Binary input matters (one accepted
round looked better on the synthetic corpus but grew 2–3% on binary data), so name a binary file of your own in
`DJINN_BENCH_BINARY`. Any compiled executable will do; a slice from 2 MiB into it becomes the
`binary` entry. Keep the same file for a whole optimisation run, since changing it changes the
corpus. Without the variable the entry is left out, and `optimize-loop.sh` refuses to start.

A single round:

```sh
export DJINN_BENCH_BINARY=/path/to/some/executable
DJINN_BENCH_SCALE=4 cargo djinn optimize --cycles 1 --agent claude --jobs 1 --min-time 30
```

`--jobs 1 --min-time 30` matters: timing several points at once or for short batches gave 2–7%
noise and false rejections. To run indefinitely, alternating Claude and Codex and passing each
agent the history of earlier rounds (one target at a time: both write the same output file, and two
loops would time their benchmarks against each other):

```sh
setsid nohup ./optimize-loop.sh compress   > .djinnscratch/optimize-loop.out 2>&1 &
setsid nohup ./optimize-loop.sh decompress > .djinnscratch/optimize-loop.out 2>&1 &
touch .djinnscratch/optimize-loop.stop     # stop after the current round
```

The `decompress` target times `bench_decompress::workload_decompress`, the built-in corpus
(with your binary entry) compressed at levels 1, 6 and 10. The script points `bench` at it while it runs and restores
Cargo.toml on exit. `implement-prompt.txt` is the compressor's brief to the agents. Accepted rounds
leave the new solution and proofs in the working tree for you to commit.
