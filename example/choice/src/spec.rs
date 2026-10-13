//! Choices left to the implementer: `any x: T where …;`

use djinn::djinn;

djinn! {
    // the quotient; on division by zero an error message of the
    // implementer's choosing, at least 10 characters long
    #[weakly_specified]
    pub fn checked_div(a: u32, b: u32) -> out: Result<u32, String> {
        if b == 0 {
            any msg: String where msg.len() >= 10;
            out == Err(msg);
        } else {
            some q: u32 { q == a / b; out == Ok(q); }
        }
    }

    // a caller inherits the choice
    #[weakly_specified]
    #[ensures(b != 0 => out == a / b)]
    pub fn safe_div(a: u32, b: u32) -> out: u32 {
        if b == 0 {
            some m: String { checked_div(a, b) == Err(m); }
            out == 0;
        } else {
            checked_div(a, b) == Ok(out);
        }
    }

    // a choice per position: every element is replaced by a smaller one
    #[weakly_specified]
    pub fn shrink(v: &[u8]) -> out: Vec<u8> {
        out.len() == v.len();
        for i in 0..v.len() {
            any w: u8 where w <= v[i];
            out[i] == w;
        }
    }
}

djinn! {
    // a top-level choice
    #[weakly_specified]
    #[requires(lo <= hi)]
    pub fn pick(lo: i32, hi: i32) -> out: i32 {
        any k: i32 where lo <= k && k <= hi;
        out == k;
    }

    // inherits the choice; the ensures holds for every choice
    #[weakly_specified]
    #[requires(lo <= hi)]
    #[ensures(out >= lo)]
    pub fn pick_twice(lo: i32, hi: i32) -> out: i32 {
        some p: i32, q: i32 {
            pick(lo, hi) == p;
            pick(lo, hi) == q;
            out == p + q - p;
        }
    }
}
