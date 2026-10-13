use std::collections::HashMap;

pub fn byte_len(s: String) -> usize {
    s.len()
}

pub fn has_key(m: HashMap<u32, u64>, k: u32) -> bool {
    m.contains_key(&k)
}

pub fn lookup(m: HashMap<u32, u64>, k: u32) -> Option<u64> {
    m.get(&k).copied()
}

pub fn lookup_next(m: HashMap<u32, u64>, k: u32) -> Option<u64> {
    m.get(&crate::spec::bump(k)).copied()
}
