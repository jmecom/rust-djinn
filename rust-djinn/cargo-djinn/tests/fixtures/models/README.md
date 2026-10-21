These fixtures contain resolved compiler IR from Charon 0.1.279, using
`--preset=aeneas --no-dedup-serialized-ast`. Only modeled type declarations,
method signatures, map-type occurrences and function references are kept;
duplicate map types within a function and unrelated metadata are omitted.
The retained nodes preserve their original compiler nesting, resolved IDs
and argument types. No compiler nodes are synthesized, and the usage check
does not inspect Rust source spelling.

`strmap.json` comes from the checked-in `example/strmap`, extracting its four
specification functions. It exercises the supported primitive-key map API,
including `contains_key` and `get`, with an ambient function and borrowed
queries.

`unsound-hashing.json` comes from these two original audit counterexamples
under specification wrappers. Previously both false specifications passed.

```rust
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

struct Recorder { touched: bool }
impl Hasher for Recorder {
    fn finish(&self) -> u64 { if self.touched { 1 } else { 0 } }
    fn write(&mut self, _: &[u8]) { self.touched = true; }
}
pub fn hash_is_noop() -> bool {
    let mut recorder = Recorder { touched: false };
    1u8.hash(&mut recorder);
    recorder.touched
}

#[derive(PartialEq, Eq)]
struct Bomb(u8);
impl Hash for Bomb {
    fn hash<H: Hasher>(&self, _: &mut H) { panic!("hash called"); }
}
pub fn map_insert_is_total() -> bool {
    let mut map = HashMap::new();
    map.insert(Bomb(1), 42u8);
    true
}
```

The specifications claimed `hash_is_noop() == false` and
`map_insert_is_total() == true` without panic. Both must now fail the
trusted-model usage check before Lean proof execution.
