//! `printf '1 10\n2 20\n' | cargo run -- 1 2 3`: the driver lives next to the specification (`spec.rs`).
use std::io::Read;

fn main() {
    let queries: Vec<u32> = std::env::args().skip(1).filter_map(|a| a.parse().ok()).collect();
    let mut input = String::new();
    let _ = std::io::stdin().read_to_string(&mut input);
    print!("{}", strmap::run(&input, &queries));
}
