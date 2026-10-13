//! Verified Sudoku implementation and byte-oriented text conversion.

pub fn digitof(ch: u8) -> u8 {
    if ch >= 49 && ch <= 57 { ch - 48 } else { 0 }
}

pub fn digitchar(d: u8) -> u8 {
    if d <= 9 { 48 + d } else { 63 }
}

pub fn parsepuzzle(s: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < s.len() {
        out.push(digitof(s[i]));
        i += 1;
    }
    out
}

pub fn showgrid(c: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < c.len() {
        out.push(digitchar(c[i]));
        i += 1;
    }
    out.push(10);
    out
}

pub fn showanswer(a: Option<Vec<u8>>) -> Vec<u8> {
    match a {
        Some(c) => showgrid(&c),
        None => {
            let mut out = Vec::new();
            out.push(110);
            out.push(111);
            out.push(32);
            out.push(115);
            out.push(111);
            out.push(108);
            out.push(117);
            out.push(116);
            out.push(105);
            out.push(111);
            out.push(110);
            out.push(10);
            out
        }
    }
}

fn same_unit(i: usize, j: usize) -> bool {
    (i / 9 == j / 9) | (i % 9 == j % 9)
        | ((i / 27 == j / 27) & ((i % 9) / 3 == (j % 9) / 3))
}

// Only cells before i have been assigned by the search.
fn allowed(c: &[u8], i: usize, d: u8) -> bool {
    let mut j = 0;
    let mut ok = true;
    while j < i {
        if c[j] == d {
            if same_unit(i, j) {
                ok = false;
            }
        }
        j += 1;
    }
    ok
}

// The pair (remaining cells, remaining digits) decreases on every call.
fn search(g: &[u8], c: &mut Vec<u8>, i: usize, d: u8) -> bool {
    if i == 81 { return true; }
    if d == 10 { return false; }
    if ((g[i] == 0) | (g[i] == d)) & allowed(c, i, d) {
        c[i] = d;
        if search(g, c, i + 1, 1) { return true; }
    }
    search(g, c, i, d + 1)
}

pub fn solve(g: &[u8]) -> Option<Vec<u8>> {
    let mut c = Vec::new();
    let mut i = 0;
    while i < 81 {
        c.push(0);
        i += 1;
    }
    if search(g, &mut c, 0, 1) { Some(c) } else { None }
}
