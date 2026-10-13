//! Strings, maps and an ambient function. `String` is seen as its bytes,
//! `HashMap<K, V>` as its list of entries; both come from the trusted model
//! library of the driver (DESIGN.md §6). `bump` is an ordinary Rust function
//! of this file that the specification calls (DESIGN.md §3).
use djinn::djinn;
use std::collections::HashMap;

/// An ambient function: trusted Rust, callable from constraints, meaning its
/// Aeneas translation. (The guard keeps it from overflowing.)
pub fn bump(x: u32) -> u32 {
    if x < 1_000_000 { x + 1 } else { x }
}

djinn! {
    // A string is its bytes: `s.len()` counts them.
    pub fn byte_len(s: String) -> r: usize {
        r == s.len();
    }

    // A map is its entries, no key twice.
    pub fn has_key(m: HashMap<u32, u64>, k: u32) -> r: bool {
        r == m.contains_key(&k);
    }

    pub fn lookup(m: HashMap<u32, u64>, k: u32) -> r: Option<u64> {
        r == m.get(&k);
    }

    // The value under the next key, as `bump` defines "next".
    pub fn lookup_next(m: HashMap<u32, u64>, k: u32) -> r: Option<u64> {
        r == m.get(&bump(k));
    }
}

// ------------------------------------------------------------------ a driver

/// Reads `key value` lines into a map, then answers the queries given as
/// arguments through the verified functions.
pub fn run(input: &str, queries: &[u32]) -> String {
    let mut m: HashMap<u32, u64> = HashMap::new();
    for line in input.lines() {
        let mut it = line.split_whitespace();
        if let (Some(k), Some(v)) = (it.next().and_then(|k| k.parse().ok()), it.next().and_then(|v| v.parse().ok())) {
            m.insert(k, v);
        }
    }
    let mut out = String::new();
    out.push_str(&format!("{} entries; {} bytes of input\n", m.len(), byte_len(input.to_string())));
    for &q in queries {
        out.push_str(&format!("{q}: present={} value={:?} next={:?}\n", has_key(m.clone(), q), lookup(m.clone(), q), lookup_next(m.clone(), q)));
    }
    out
}
