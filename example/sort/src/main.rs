//! `cargo run -- 5 3 9 -1 4`: the driver lives next to the specification (`spec.rs`).
fn main() {
    match sortprog::run(std::env::args().skip(1)) {
        Ok(report) => println!("{report}"),
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(2);
        }
    }
}
