//! The specification. This is the only artifact a human writes and the only
//! human artifact the verifier trusts. No line here is executable: every
//! statement is a constraint relating inputs to outputs, and the body of a
//! `fn` or `rel` is the conjunction of its statements.

use djinn::djinn;

djinn! {
    // `perm` relates a list to each of its permutations: ambiguous on purpose.
    // It is a `rel`, so it is never implemented and owes no unambiguity proof.
    // `total` asks for the existence obligation (realizability).
    // Counting is written the way Rust counts; the driver knows its Lean model.
    #[total]
    pub rel perm(list: &[i32]) -> t: Vec<i32> {
        t.len() == list.len();
        for x in list {
            t.iter().filter(|y| y == x).count() == list.iter().filter(|y| y == x).count();
        }
        for x in t {
            t.iter().filter(|y| y == x).count() == list.iter().filter(|y| y == x).count();
        }
    }
    
    #[total]
    pub rel permsuperset(list: &[i32]) -> t: Vec<i32> {
        t.len() >= list.len();
        for x in list {
            t.iter().filter(|y| y == x).count() == list.iter().filter(|y| y == x).count();
        }
    }

    // Sort in place. The output of this `fn` is the final value of `v`;
    // `old(v)` is its value on entry.
    pub fn sort(v: &mut Vec<i32>) {
        perm(old(v)) == v;                               // v is SOME permutation ...
        for i in 0..v.len() - 1 { v[i] <= v[i + 1]; }     // ... namely the sorted one
    }

    // Figure 1 of the paper. `r` names the return value.
    #[requires(list.len() >= 1)]
    #[ensures(r in list)]
    pub fn max(list: &[i32]) -> r: i32 {
        r in list;                          // r is one of the elements ...
        for x in list { x <= r; }            // ... and none of them is larger
    }
}

// ------------------------------------------------------------------ a driver
//
// Ordinary Rust, in the same file as the specification. Charon starts its
// translation from the `fn`s above and follows their calls, so nothing below
// is translated or verified, and it may use whatever Rust it likes
// (`String`, `format!`, parsing). Its one duty is visible: `max` requires a
// non-empty list, so the empty case is handled before the call.

/// Sorts the integers given as arguments and reports their maximum.
pub fn run(args: impl Iterator<Item = String>) -> Result<String, String> {
    let mut v: Vec<i32> = Vec::new();
    for a in args {
        v.push(a.trim().parse().map_err(|_| format!("not an integer: `{a}`"))?);
    }
    if v.is_empty() {
        return Err("usage: sortprog <integers…>".into());
    }
    let m = max(&v);
    sort(&mut v);
    Ok(format!("sorted: {v:?}\nmax: {m}"))
}
