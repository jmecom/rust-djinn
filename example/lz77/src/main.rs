//! `cargo run < file`: the driver lives next to the specification (`spec.rs`).
use std::io::Read;

fn main() {
    let mut input = Vec::new();
    let _ = std::io::stdin().read_to_end(&mut input);
    println!("{}", lz77::report(&input));
}
