//! Deliberately flawed specifications, to exercise `cargo djinn smoke-test`.
use djinn::djinn;

djinn! {
    // forgot "none is larger": ambiguous
    #[requires(list.len() >= 1)]
    pub fn max_ambiguous(list: &[i32]) -> r: i32 {
        r in list;
    }

    // no case for i == 0: no output there
    pub fn abs_partial(i: i64) -> n: i64 {
        cases {
            i > 0 && n == i;
            i < 0 && n == -i;
        }
    }

    // off by one: v[i + 1] out of bounds
    pub fn sorted_offbyone(v: &[i32]) -> b: bool {
        b == true;
        for i in 0..v.len() { v[i] <= v[i + 1]; }
    }

    // ensures does not follow
    #[requires(list.len() >= 1)]
    #[ensures(r > 0)]
    pub fn max_pos(list: &[i32]) -> r: i32 {
        r in list;
        for x in list { x <= r; }
    }

    // contradictory
    pub fn two_values(x: i32) -> r: i32 {
        r == 1;
        r == 2;
    }

    // fine: a control
    #[requires(lo <= hi)]
    pub fn clamp_ok(x: i32, lo: i32, hi: i32) -> r: i32 {
        lo <= r <= hi;
        x < lo => r == lo;
        x > hi => r == hi;
        lo <= x <= hi => r == x;
    }
}
