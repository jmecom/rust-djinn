//! LZ77 compression with optimal parsing. Translated from the paper's
//! `lz77.spec`.
//!
//! The FORMAT is fixed by `decode`: a token is a literal byte or a
//! back-reference `Match { dist, len }` copying `len` bytes from `dist`
//! back (overlapping copies allowed, as in DEFLATE), with dist <= WINDOW
//! and MINLEN <= len <= MAXLEN. The OBJECTIVE fixes the encoder: among all
//! token sequences that decode to the input, a shortest one; among the
//! shortest, at every position the longest usable token, and among equally
//! long matches the nearest. `mincost` is that minimum as a recurrence over
//! the finite menu of tokens usable at a position — it ranges over every
//! encoding without ever naming one.
//!
//! Positions are counted from the END: `n` is the number of bytes not yet
//! encoded, so each recursion visibly decreases on its first argument.
//!
//! The `Token` enum is matched by constructor patterns; the recursive
//! relations carry a `#[decreases(..)]` measure (the paper's "positions are
//! counted from the end"); `WINDOW`, `MINLEN`, `MAXLEN` are crate constants.

use djinn::djinn;

/// The token alphabet and the format's constants (the Dafny "ambient").
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Token {
    Lit(u8),
    Match { dist: u32, len: u32 },
}

pub const WINDOW: u32 = 32768; // farthest back a match may reach
pub const MINLEN: u32 = 3; // shortest match worth a token
pub const MAXLEN: u32 = 258; // longest match a token can express

djinn! {
    // ------------------------------------------------------------ the format

    // The l bytes at position j repeat the l bytes d back.
    #[requires(0 <= l && 1 <= d <= j && j + l <= s.len())]
    #[decreases(l)]
    pub rel copies(l: int, s: &[u8], j: int, d: int) -> b: bool {
        b == (l == 0 || (s[j] == s[j - d] && copies(l - 1, s, j + 1, d)));
    }

    // A match token (d, l) is usable at position j of s.
    #[requires(0 <= j <= s.len())]
    pub rel ismatch(s: &[u8], j: int, d: int, l: int) -> b: bool {
        b == (1 <= d <= WINDOW && d <= j && MINLEN <= l <= MAXLEN && j + l <= s.len()
              && copies(l, s, j, d));
    }

    pub fn toklen(t: Token) -> n: u32 {
        match t {
            Token::Lit(_) => n == 1,
            Token::Match { len, .. } => n == len,
        }
    }

    // Bytes produced by a token sequence.
    #[decreases(ts.len())]
    pub rel encoded(ts: &[Token]) -> m: int {
        if ts.is_empty() {
            m == 0;
        } else {
            m == encoded(ts[..ts.len() - 1]) + toklen(ts[ts.len() - 1]);
        }
    }

    // What a token sequence denotes. A rel: a match reaching before the start
    // of the output, or of a bad length, denotes nothing.
    #[decreases(ts.len())]
    pub rel decode(ts: &[Token]) -> s: Vec<u8> {
        if ts.is_empty() {
            s.is_empty();
        } else {
            some p: Vec<u8> {
                decode(ts[..ts.len() - 1]) == p;
                match ts[ts.len() - 1] {
                    Token::Lit(ch) => {
                        s.len() == p.len() + 1;
                        s[..p.len()] == p;
                        s[p.len()] == ch;
                    }
                    Token::Match { dist, len } => {
                        1 <= dist <= p.len();
                        1 <= len;
                        s.len() == p.len() + len;
                        s[..p.len()] == p;
                        for k in p.len()..s.len() { s[k] == s[k - dist]; }
                    }
                }
            }
        }
    }

    // --------------------------------------------------------- the objective

    // The fewest tokens that encode the last n bytes of s, given that the
    // rest has been emitted already (matches may reach back into it): the
    // minimum over the menu at position s.len() - n — a literal, or any
    // usable match. The `for` block says every option costs at least k; the
    // `cases` block says one of them costs exactly k.
    #[requires(0 <= n <= s.len())]
    #[ensures(0 <= k <= n)]
    #[decreases(n)]
    pub rel mincost(n: int, s: &[u8]) -> k: int {
        if n == 0 {
            k == 0;
        } else {
            k <= 1 + mincost(n - 1, s);
            for l in MINLEN..MAXLEN + 1 {
                for d in 1..WINDOW + 1 {
                    ismatch(s, s.len() - n, d, l) => k <= 1 + mincost(n - l, s);
                }
            }
            cases {
                k == 1 + mincost(n - 1, s);
                some l: int, d: int {
                    ismatch(s, s.len() - n, d, l);
                    k == 1 + mincost(n - l, s);
                }
            }
        }
    }

    // The token to emit with n bytes left: one that keeps the encoding
    // shortest — the longest such, and among equally long matches the
    // nearest. A literal only when no match is optimal.
    #[requires(1 <= n <= s.len())]
    #[ensures(1 <= toklen(t) <= n)]
    #[ensures(1 + mincost(n - toklen(t), s) == mincost(n, s))]
    pub rel besttoken(n: int, s: &[u8]) -> t: Token {
        match t {
            Token::Lit(ch) => {
                ch == s[s.len() - n];
                1 + mincost(n - 1, s) == mincost(n, s);
                for l in MINLEN..MAXLEN + 1 {
                    for d in 1..WINDOW + 1 {
                        ismatch(s, s.len() - n, d, l) => 1 + mincost(n - l, s) != mincost(n, s);
                    }
                }
            }
            Token::Match { dist, len } => {
                ismatch(s, s.len() - n, dist, len);
                1 + mincost(n - len, s) == mincost(n, s);
                for l in len + 1..MAXLEN + 1 {
                    for d in 1..WINDOW + 1 {
                        ismatch(s, s.len() - n, d, l) => 1 + mincost(n - l, s) != mincost(n, s);
                    }
                }
                for d in 1..dist {
                    ismatch(s, s.len() - n, d, len) => 1 + mincost(n - len, s) != mincost(n, s);
                }
            }
        }
    }

    // ----------------------------------------------------------- the encoder

    // The encoding of s: token i is the best token at the position where the
    // tokens before it end, and the tokens end exactly at the end of s. The
    // ensures export what matters to a caller: it decodes back to s, and it
    // is as short as any encoding.
    #[ensures(decode(ts) == s)]
    #[ensures(ts.len() == mincost(s.len(), s))]
    pub fn compress(s: &[u8]) -> ts: Vec<Token> {
        encoded(ts) == s.len();
        for i in 0..ts.len() {
            besttoken(s.len() - encoded(ts[..i]), s) == ts[i];
        }
    }
}

// ------------------------------------------------------------------ a driver
//
// The paper's `main`, as plain Rust next to the specification: read the
// input, compress it, report. Nothing here is translated or verified
// (Charon starts from the `fn`s above); it only has to respect the
// preconditions of what it calls, and `compress` has none.

/// Compresses `input` and describes the result (the token count stands in
/// for the paper's `naturalnumbertostring`).
pub fn report(input: &[u8]) -> String {
    let tokens = compress(input);
    let matches = tokens.iter().filter(|t| matches!(t, Token::Match { .. })).count();
    format!("{} bytes → {} tokens ({} literals, {} matches)", input.len(), tokens.len(), tokens.len() - matches, matches)
}
