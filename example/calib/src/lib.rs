//! Calibration crate: the LLM-side `solution` bodies of example/sort, as a
//! plain crate so Charon/Aeneas can translate them without the djinn macros.
#![forbid(unsafe_code)]

/// Insertion sort, index reads/writes only (every op has an Aeneas model).
pub fn sort(v: &mut Vec<i32>) {
    let n = v.len();
    let mut i = 1;
    while i < n {
        let mut j = i;
        while j > 0 && v[j - 1] > v[j] {
            let t = v[j - 1];
            v[j - 1] = v[j];
            v[j] = t;
            j -= 1;
        }
        i += 1;
    }
}

/// Precondition: `list` is non-empty.
pub fn max(list: &[i32]) -> i32 {
    let mut r = list[0];
    let mut i = 1;
    while i < list.len() {
        if list[i] > r {
            r = list[i];
        }
        i += 1;
    }
    r
}
