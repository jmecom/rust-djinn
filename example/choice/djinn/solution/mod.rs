pub fn checked_div(a: u32, b: u32) -> Result<u32, String> {
    if b == 0 {
        Err(String::from("division by zero"))
    } else {
        Ok(a / b)
    }
}

pub fn safe_div(a: u32, b: u32) -> u32 {
    match checked_div(a, b) {
        Ok(q) => q,
        Err(_) => 0,
    }
}

pub fn shrink(v: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < v.len() {
        out.push(0);
        i += 1;
    }
    out
}

pub fn pick(lo: i32, _hi: i32) -> i32 {
    lo
}

pub fn pick_twice(lo: i32, hi: i32) -> i32 {
    pick(lo, hi)
}
