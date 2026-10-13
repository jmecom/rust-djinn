# example/strmap — strings, maps and an ambient function

Four small functions that exercise what the standard-library model library
and ambient functions add to the specification language (DESIGN.md §3, §6):

| declaration | what it shows |
|---|---|
| `byte_len(s: String) -> usize` | a `String` parameter, viewed as its UTF-8 bytes (`s.len()` counts them) |
| `has_key(m: HashMap<u32, u64>, k: u32) -> bool` | a `HashMap` parameter, viewed as its list of entries; `m.contains_key(&k)` |
| `lookup(m, k) -> Option<u64>` | `m.get(&k)` |
| `lookup_next(m, k) -> Option<u64>` | a call to `bump`, an ordinary Rust function of `spec.rs`, inside a constraint |

The implementations use the real APIs (`String::len`, `HashMap::contains_key`,
`HashMap::get(..).copied()`, and `crate::spec::bump`). `verify` finds that
Aeneas has no model for those items, covers them from the driver's model
library (writing `Code/FunsExternal.lean` and `Code/TypesExternal.lean`), and
the proofs in `Proofs.lean` go through the models: `Djinn.Vocab.find_eq`
turns the models' lookup with Rust's `Eq` instance into `List.find?`, and
`unfold StrMap.spec.bump` exposes the ambient function's body. PASS, with the
proofs written by hand.

`run` at the end of `spec.rs` is the plain-Rust driver: it builds a map from
`key value` lines and answers queries through the verified functions:

```
printf '1 10\n2 20\n' | cargo run --quiet -- 1 2 3
2 entries; 10 bytes of input
1: present=true value=Some(10) next=Some(20)
2: present=true value=Some(20) next=None
3: present=false value=None next=None
```
