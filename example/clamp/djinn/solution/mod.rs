//! LLM-owned.

pub fn clamp(x: i32, lo: i32, hi: i32) -> i32 {
    if x < lo { lo } else if x > hi { hi } else { x }
}

pub fn count_negative(v: &[i32]) -> usize {
    let mut count = 0;
    let mut i = 0;
    while i < v.len() {
        if v[i] < 0 {
            count += 1;
        }
        i += 1;
    }
    count
}

pub fn min(a: i32, b: i32) -> i32 {
    if a <= b { a } else { b }
}

pub fn max(a: i32, b: i32) -> i32 {
    if a >= b { a } else { b }
}
