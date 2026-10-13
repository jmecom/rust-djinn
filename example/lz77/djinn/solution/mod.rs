//! Optimal LZ77 parsing with longest-match, then nearest-match tie breaking.

use crate::spec::Token;

pub fn toklen(t: Token) -> u32 {
    match t {
        Token::Lit(_) => 1,
        Token::Match { len, .. } => len,
    }
}

// Overlap is intentional: all comparisons refer to the original input.
fn match_bytes(s: &[u8], pos: usize, dist: usize, len: usize) -> bool {
    if len == 0 {
        true
    } else if s[pos] != s[pos - dist] {
        false
    } else {
        match_bytes(s, pos + 1, dist, len - 1)
    }
}

// Entry n-1 stores the cost of the final n bytes; the empty suffix costs zero.
fn suffix_cost(costs: &[usize], n: usize) -> usize {
    if n == 0 { 0 } else { costs[n - 1] }
}

fn best_at(s: &[u8], pos: usize, costs: &[usize]) -> (usize, Token) {
    let remaining = s.len() - pos;
    let mut best_cost = 1 + suffix_cost(costs, remaining - 1);
    let mut best = Token::Lit(s[pos]);
    let mut best_len = 1;
    let mut len = 3;
    while len <= 258 && len <= remaining {
        let mut dist = 1;
        while dist <= 32768 && dist <= pos {
            if match_bytes(s, pos, dist, len) {
                let cost = 1 + suffix_cost(costs, remaining - len);
                // Lengths and distances are visited in increasing order.
                // Keeping an equal-length winner retains the nearest distance.
                if cost < best_cost || (cost == best_cost && len > best_len) {
                    best_cost = cost;
                    best = Token::Match { dist: dist as u32, len: len as u32 };
                    best_len = len;
                }
            }
            dist += 1;
        }
        len += 1;
    }
    (best_cost, best)
}

pub fn compress(s: &[u8]) -> Vec<Token> {
    let mut costs = Vec::new();
    let mut choices = Vec::new();
    let mut n = 0;
    while n < s.len() {
        n += 1;
        let (cost, token) = best_at(s, s.len() - n, &costs);
        costs.push(cost);
        choices.push(token);
    }
    let mut output = Vec::new();
    let mut pos = 0;
    while pos < s.len() {
        let token = choices[s.len() - pos - 1];
        pos += toklen(token) as usize;
        output.push(token);
    }
    output
}
