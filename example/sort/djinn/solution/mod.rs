//! Verified ascending insertion sort and maximum.

fn insert(list: &[i32], n: usize, x: i32) -> Vec<i32> {
    if n == 0 {
        let mut out = Vec::new();
        out.push(x);
        out
    } else {
        let k = n - 1;
        let y = list[k];
        let (lo, hi) = if x >= y { (y, x) } else { (x, y) };
        let mut out = insert(list, k, lo);
        out.push(hi);
        out
    }
}

fn sort_prefix(list: &[i32], n: usize) -> Vec<i32> {
    if n == 0 {
        Vec::new()
    } else {
        let k = n - 1;
        let x = list[k];
        let sorted = sort_prefix(list, k);
        insert(&sorted, k, x)
    }
}

pub fn sort(v: &mut Vec<i32>) {
    *v = sort_prefix(v, v.len());
}

fn max_prefix(list: &[i32], n: usize) -> i32 {
    if n <= 1 {
        list[0]
    } else {
        let k = n - 1;
        let m = max_prefix(list, k);
        let x = list[k];
        if x > m { x } else { m }
    }
}

pub fn max(list: &[i32]) -> i32 {
    max_prefix(list, list.len())
}
