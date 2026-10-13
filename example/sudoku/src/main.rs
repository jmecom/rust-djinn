//! `printf '<81 digits, 0 for empty>\n' | cargo run`: the driver lives next to the specification (`spec.rs`).
fn main() {
    let stdin = std::io::stdin();
    if let Err(e) = sudoku::solve_stream(stdin.lock(), std::io::stdout()) {
        eprintln!("{e}");
        std::process::exit(1);
    }
}
