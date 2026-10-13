//! Sudoku — the lexicographically smallest completion of a puzzle, or the
//! verdict that there is none. Translated from the paper's `sudoku.spec`.
//!
//! A puzzle and a grid are both sequences of 81 bytes, row-major (cell
//! (r, c) is index 9*r + c); 0 in a puzzle means "empty". Nothing below
//! says how to search. It says what a completion is (`completion`, a rel,
//! because a puzzle has none or many), which one `solve` must return (the
//! least in the lexicographic order on grids), and that `None` is a proof
//! of absence (the first `ensures` on `solve`).
//!
//! The order is pinned down WITHOUT quantifying over all grids: c is the
//! least completion iff no cell can be lowered — for every empty cell i and
//! every digit d below c[i], the puzzle that keeps c's prefix and puts d at
//! i has no completion at all (`prefixthen(..) not in domain(completion)`).
//! That is exactly the shape of a backtracking search's failed branches.
//!
//! Differences from the Dafny version: the `Answer` datatype is
//! `Option<Vec<u8>>` (`None` = no solution); text is bytes ('0' is 48,
//! '\n' is 10), as Aeneas models strings; the I/O is not specified at all —
//! `solve_stream` at the end of this file is an ordinary Rust driver that
//! reads puzzles and calls the verified functions.

use djinn::djinn;

djinn! {
    // ------------------------------------------------------------ the rules

    // Two cells constrain each other when they share a row, a column, or a
    // 3x3 box. A `rel` because its parameters are mathematical indices.
    #[requires(0 <= i < 81 && 0 <= j < 81)]
    pub rel sameunit(i: int, j: int) -> b: bool {
        b == (i / 9 == j / 9 || i % 9 == j % 9
              || (i / 27 == j / 27 && (i % 9) / 3 == (j % 9) / 3));
    }

    // The completions of a puzzle: every full grid that agrees with the
    // givens and repeats no digit within a unit. A given outside 1..9, or
    // two givens that clash, simply leave the puzzle with no completion.
    #[requires(g.len() == 81)]
    pub rel completion(g: &[u8]) -> c: Vec<u8> {
        c.len() == 81;
        for i in 0..81 {
            1 <= c[i] <= 9;
            g[i] != 0 => c[i] == g[i];
        }
        for i in 0..81 {
            for j in 0..81 {
                i != j && sameunit(i, j) => c[i] != c[j];
            }
        }
    }

    // ------------------------------------------------------------ the order

    // The puzzle that keeps c on the cells before i, puts d at i, and keeps
    // g's givens after i: "c's prefix, then a different digit". Any
    // completion of it is lexicographically below c whenever d < c[i].
    #[requires(g.len() == 81 && c.len() == 81 && 0 <= i < 81)]
    pub rel prefixthen(g: &[u8], c: &[u8], i: int, d: int) -> h: Vec<u8> {
        h.len() == 81;
        for j in 0..i { h[j] == c[j]; }
        h[i] == d;
        for j in i + 1..81 { h[j] == g[j]; }
    }

    // ----------------------------------------------------------- the solver

    // The answer is a completion — the lexicographically least one — exactly
    // when there is any. The two ensures export both halves to callers: a
    // Some is a completion, and None means there is none.
    #[requires(g.len() == 81)]
    #[ensures(a.is_some() == (g in domain(completion)))]
    #[ensures(a.is_some() => completion(g) == a.unwrap())]
    pub fn solve(g: &[u8]) -> a: Option<Vec<u8>> {
        if g in domain(completion) {
            a.is_some();
            completion(g) == a.unwrap();
            for i in 0..81 {
                if g[i] == 0 {
                    for d in 1..a.unwrap()[i] {
                        prefixthen(g, a.unwrap(), i, d) not in domain(completion);
                    }
                }
            }
        } else {
            a == None;
        }
    }

    // --------------------------------------------------------------- text

    // A puzzle line: '1'..'9' (bytes 49..57) is a given, anything else is empty.
    #[ensures(0 <= d <= 9)]
    pub fn digitof(ch: u8) -> d: u8 {
        d == if 49 <= ch && ch <= 57 { ch - 48 } else { 0 };
    }

    #[requires(s.len() == 81)]
    #[ensures(g.len() == 81)]
    pub fn parsepuzzle(s: &[u8]) -> g: Vec<u8> {
        g.len() == 81;
        for i in 0..81 { g[i] == digitof(s[i]); }
    }

    // A digit as its character, '?' (63) otherwise.
    pub fn digitchar(d: u8) -> ch: u8 {
        ch == if d <= 9 { 48 + d } else { 63 };
    }

    // The precondition keeps the output a possible Vec: for a slice of length
    // usize::MAX there is no sequence one longer, so without it the function
    // could not be implemented.
    #[requires(c.len() == 81)]
    #[ensures(s.len() == c.len() + 1)]
    pub fn showgrid(c: &[u8]) -> s: Vec<u8> {
        s.len() == c.len() + 1;
        for i in 0..c.len() { s[i] == digitchar(c[i]); }
        s[c.len()] == 10;                         // '\n'
    }

    // The bytes of "no solution\n".
    #[total]
    pub rel nosolutiontext() -> s: Vec<u8> {
        s.len() == 12;
        s[0] == 110; s[1] == 111; s[2] == 32; s[3] == 115; s[4] == 111; s[5] == 108;
        s[6] == 117; s[7] == 116; s[8] == 105; s[9] == 111; s[10] == 110; s[11] == 10;
    }

    #[requires(a.is_some() => a.unwrap().len() == 81)]
    pub fn showanswer(a: Option<Vec<u8>>) -> s: Vec<u8> {
        if a.is_some() {
            showgrid(a.unwrap()) == s;
        } else {
            nosolutiontext() == s;
        }
    }
}

// ------------------------------------------------------------------ a driver
//
// The I/O of the paper's `main`, as plain Rust next to the specification:
// read puzzles, call the verified functions, write answers. Charon starts
// its translation from the `fn`s above, so this function is never seen by
// the verifier and may use `std::io` and strings freely. What it owes is the
// precondition of `parsepuzzle`, a line of exactly 81 bytes, checked below.

/// Solves every 81-character line of `input`, writing each answer (the
/// lexicographically least completion, or `no solution`) to `out`; other
/// lines are reported on stderr and skipped.
pub fn solve_stream(input: impl std::io::BufRead, mut out: impl std::io::Write) -> std::io::Result<()> {
    for line in input.lines() {
        let line = line?;
        let bytes = line.as_bytes();
        if bytes.len() != 81 {
            eprintln!("skipping a line of {} characters (a puzzle has 81)", bytes.len());
            continue;
        }
        let grid = parsepuzzle(bytes);
        let answer = solve(&grid);
        out.write_all(&showanswer(answer))?;
    }
    Ok(())
}
