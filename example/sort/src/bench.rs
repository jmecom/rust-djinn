//! The performance workload for `cargo djinn optimize`: sort a large
//! pseudo-random vector. Human-written, trusted only for timing.

pub fn workload() {
    let mut x: u32 = 0x1234_5678;
    let mut v: Vec<i32> = Vec::with_capacity(8192);
    for _ in 0..8192 {
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        v.push((x as i32) >> 8);
    }
    crate::sort(&mut v);
    std::hint::black_box(&v);
    std::hint::black_box(crate::max(&v));
}
