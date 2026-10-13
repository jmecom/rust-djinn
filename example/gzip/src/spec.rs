//! gzip (RFC 1952) over DEFLATE (RFC 1951), translated from the specification of
//! [lean-zip](https://github.com/kim-em/lean-zip) (`Zip/Spec/{Deflate,Huffman,LZ77,Crc32}.lean`
//! and `GzipCorrect.lean`).
//!
//! lean-zip specifies the *format* as a decoder — what a bit stream means — and the compressor
//! only by the round trip, `decompress (compress data) = ok data`. The same shape here, in three
//! layers: the bits and the Huffman codes, the DEFLATE blocks, the gzip member around them. The
//! parsing relations all read `s` from bit `i` and return the bit `j` where they stop, with what
//! they read among their inputs — so `stored(s, i, prev, out) == j` says "bits `i..j` of `s` are a
//! stored block that extends `prev` to `out`". No preconditions: a relation that reads past the end
//! or finds a wrong value is simply empty, and the stream is not a gzip member.
//!
//! `compress` has no leeway in lean-zip beyond the round trip, and the same here: it is specified
//! only as the gzip header bytes and *some* member that `decompress` turns back into the data
//! (`any`, see docs/ANY.md). Everything about the encoder — the parse, the blocks, the codes — is
//! the implementer's, and so is what the levels mean. The round trip is its `ensures`.
//!
//! Integers in constraints are mathematical, so the specification has no bit operators: `bit`
//! takes bits apart with `/` and `%`, and `xor` is defined by recursion where CRC-32 needs it.

use djinn::djinn;

pub const WINDOW: u32 = 32768; // farthest back a copy may reach
pub const MINLEN: u32 = 3; // shortest copy a token can express
pub const MAXLEN: u32 = 258; // longest copy a token can express
pub const MAXOUT: usize = 1073741824; // `decompress` refuses larger contents (a zip-bomb guard, as in lean-zip)
pub const POLY: u32 = 0xEDB88320; // the CRC-32 polynomial, reversed
pub const HEADER: &[u8] = b"\x1f\x8b\x08\x00\x00\x00\x00\x00"; // what `compress` emits: ID1 ID2, CM = deflate, FLG = 0, MTIME = 0; then XFL from the level and OS = unknown
pub const CL_ORDER: &[u8] = b"\x10\x11\x12\x00\x08\x07\x09\x06\x0a\x05\x0b\x04\x0c\x03\x0d\x02\x0e\x01\x0f"; // RFC 1951 §3.2.7
pub const UNSEEN: u32 = 15; // the cost charged for a symbol the current code leaves out
pub const GRID: u32 = 2048; // blocks begin and end at multiples of this many tokens
pub const MAXSPAN: u32 = 128; // and span at most this many grid cells
pub const HDRBITS: u32 = 71; // the estimated size of a dynamic header, before 4 bits per used symbol

djinn! {
    // ================================================================ bits

    // Bit i of s. Bytes are read least significant bit first (RFC 1951 §3.1.1).
    pub rel bit(s: &[u8], i: int) -> b: int {
        0 <= i < 8 * s.len();
        b == (s[i / 8] / 2.pow(i % 8)) % 2;
    }

    // The n-bit number at bit i, least significant bit first: how counts and extra bits are stored.
    #[requires(0 <= n)]
    #[decreases(n)]
    pub rel field(s: &[u8], i: int, n: int) -> v: int {
        if n == 0 { v == 0; } else { v == bit(s, i) + 2 * field(s, i + 1, n - 1); }
    }

    // The n-bit number at bit i, most significant bit first: how Huffman codewords are stored.
    #[requires(0 <= n)]
    #[decreases(n)]
    pub rel code(s: &[u8], i: int, n: int) -> v: int {
        if n == 0 { v == 0; } else { v == 2 * code(s, i, n - 1) + bit(s, i + n - 1); }
    }

    // Little-endian numbers in the bytes from i.
    pub rel u16le(s: &[u8], i: int) -> v: int {
        0 <= i && i + 2 <= s.len();
        v == s[i] + 256 * s[i + 1];
    }

    pub rel u32le(s: &[u8], i: int) -> v: int {
        v == u16le(s, i) + 65536 * u16le(s, i + 2);
    }

    // ======================================================= Huffman codes (§3.2.2)
    //
    // A code is given by the length of each symbol's codeword, 0 for an unused symbol. The
    // codewords follow from the lengths: shorter ones are numerically smaller, and equal lengths
    // go in symbol order. So the codeword of a symbol is the number of codewords shorter than it,
    // each scaled up to its length, plus the number of lower symbols of the same length.

    // Over the first k symbols, the sum of 2^(n - length) for the lengths between 1 and n - 1:
    // the first codeword of length n.
    #[requires(0 <= k <= lens.len())]
    #[decreases(k)]
    pub rel shorter(lens: &[u8], k: int, n: int) -> c: int {
        if k == 0 {
            c == 0;
        } else if 1 <= lens[k - 1] < n {
            c == shorter(lens, k - 1, n) + 2.pow(n - lens[k - 1]);
        } else {
            c == shorter(lens, k - 1, n);
        }
    }

    // How many of the first k symbols have length n.
    #[requires(0 <= k <= lens.len())]
    #[decreases(k)]
    pub rel earlier(lens: &[u8], k: int, n: int) -> c: int {
        if k == 0 {
            c == 0;
        } else if lens[k - 1] == n {
            c == earlier(lens, k - 1, n) + 1;
        } else {
            c == earlier(lens, k - 1, n);
        }
    }

    pub rel codeword(lens: &[u8], sym: int) -> c: int {
        0 <= sym < lens.len();
        c == shorter(lens, lens.len(), lens[sym]) + earlier(lens, sym, lens[sym]);
    }

    // Lengths of at most n bits that do not oversubscribe the code (the Kraft inequality): then
    // no codeword is a prefix of another, and `symbol` below has at most one answer.
    #[requires(0 <= n)]
    pub rel valid(lens: &[u8], n: int) -> b: bool {
        b == (lens.iter().all(|l| l <= n) && shorter(lens, lens.len(), n + 1) <= 2.pow(n + 1));
    }

    // The symbol whose codeword starts at bit i.
    pub rel symbol(s: &[u8], i: int, lens: &[u8]) -> sym: int {
        0 <= sym < lens.len();
        1 <= lens[sym];
        code(s, i, lens[sym]) == codeword(lens, sym);
    }

    // The fixed codes (§3.2.6), given by their lengths like any other: literal/length symbols
    // 0–143 have 8 bits, 144–255 have 9, 256–279 have 7, 280–287 have 8; the 30 distance codes
    // have 5 bits, and two unused symbols of 5 bits complete that code.
    pub rel fixedlen(sym: int) -> n: int {
        n == if sym < 144 { 8 } else if sym < 256 { 9 } else if sym < 280 { 7 } else { 8 };
    }

    #[override_smoke_test]                                                // 288 elements: beyond the bounded search
    pub rel fixedlit() -> lens: Vec<u8> {
        lens.len() == 288;
        for k in 0..288 { lens[k] == fixedlen(k); }
    }

    pub rel fixeddist() -> lens: Vec<u8> {
        lens.len() == 32;
        for l in lens { l == 5; }
    }

    // ================================================ lengths and distances (§3.2.5)
    //
    // Length code 257 + k stands for the lengths from lbase(k) on, lextra(k) extra bits telling
    // which. Each code's lengths start where the previous code's end: 3..10 one code each, then
    // groups of four codes with 1, 2, 3, 4, 5 extra bits, and code 285 for 258 alone. That is the
    // table of the RFC: lbase = 3 4 5 6 7 8 9 10 11 13 15 17 19 23 27 31 35 43 51 59 67 83 99 115
    // 131 163 195 227 258.
    #[ensures(0 <= e)]
    pub rel lextra(k: int) -> e: int {
        0 <= k <= 28;
        if k < 8 || k == 28 { e == 0; } else { e == k / 4 - 1; }
    }

    #[requires(0 <= k)]
    #[decreases(k)]
    pub rel lbase(k: int) -> b: int {
        k <= 28;
        if k == 0 { b == 3; } else if k == 28 { b == 258; } else { b == lbase(k - 1) + 2.pow(lextra(k - 1)); }
    }

    // Distance code k stands for the distances from dbase(k) on, dextra(k) extra bits telling
    // which: 1..4 one code each, then pairs of codes with 1, 2, ..., 13 extra bits, up to 32768.
    // dbase = 1 2 3 4 5 7 9 13 17 25 33 49 65 97 129 193 257 385 513 769 1025 1537 2049 3073 4097
    // 6145 8193 12289 16385 24577.
    #[ensures(0 <= e)]
    pub rel dextra(k: int) -> e: int {
        0 <= k <= 29;
        if k < 4 { e == 0; } else { e == k / 2 - 1; }
    }

    #[requires(0 <= k)]
    #[decreases(k)]
    pub rel dbase(k: int) -> b: int {
        k <= 29;
        if k == 0 { b == 1; } else { b == dbase(k - 1) + 2.pow(dextra(k - 1)); }
    }

    // ================================================================ blocks
    //
    // The output grows by literals and by copies (§3.2.3). A copy may overlap what it writes.
    pub rel append(prev: &[u8], x: int) -> out: Vec<u8> {
        out.len() == prev.len() + 1;
        out[..prev.len()] == prev;
        out[prev.len()] == x;
    }

    pub rel copy(prev: &[u8], d: int, len: int) -> out: Vec<u8> {
        1 <= d <= prev.len();
        out.len() == prev.len() + len;
        out[..prev.len()] == prev;
        for k in prev.len()..out.len() { out[k] == out[k - d]; }
    }

    // The symbols of a Huffman block from bit i to its end-of-block symbol: each is a literal
    // byte, or a length code with its extra bits followed by a distance code with its extra bits,
    // standing for a copy. They extend `prev` to `out`; the block ends at bit j.
    #[decreases(8 * s.len() - i)]
    pub rel symbols(s: &[u8], i: int, lit: &[u8], dist: &[u8], prev: &[u8], out: &[u8]) -> j: int {
        some sym: int, a: int {
            symbol(s, i, lit) == sym;
            a == i + lit[sym];                                            // after the codeword
            i < a <= 8 * s.len();
            if sym == 256 {
                out == prev;
                j == a;
            } else if sym < 256 {
                symbols(s, a, lit, dist, append(prev, sym), out) == j;
            } else {
                some len: int, b: int, dc: int, d: int, c: int {
                    len == lbase(sym - 257) + field(s, a, lextra(sym - 257));
                    b == a + lextra(sym - 257);                           // after the length's extra bits
                    symbol(s, b, dist) == dc;
                    d == dbase(dc) + field(s, b + dist[dc], dextra(dc));
                    c == b + dist[dc] + dextra(dc);                       // after the distance's extra bits
                    a < c <= 8 * s.len();
                    symbols(s, c, lit, dist, copy(prev, d, len), out) == j;
                }
            }
        }
    }

    // A stored block (§3.2.4): from the next byte boundary, LEN and its one's complement NLEN as
    // 16-bit little-endian numbers, then LEN bytes as they are.
    pub rel stored(s: &[u8], i: int, prev: &[u8], out: &[u8]) -> j: int {
        some a: int, len: int {
            a == (i + 7) / 8;
            len == u16le(s, a);
            u16le(s, a + 2) == 65535 - len;
            a + 4 + len <= s.len();
            out.len() == prev.len() + len;
            out[..prev.len()] == prev;
            out[prev.len()..out.len()] == s[a + 4..a + 4 + len];
            j == 8 * (a + 4 + len);
        }
    }

    // Code lengths, run-length coded in the code-length code: a symbol below 16 is a length;
    // 16 repeats the previous length 3–6 times (2 extra bits); 17 and 18 stand for 3–10 (3 bits)
    // and 11–138 (7 bits) zeros. Reads from bit i, fills `all` from index p on, ends at bit j.
    #[requires(0 <= p <= all.len())]
    #[decreases(all.len() - p)]
    pub rel lengths(s: &[u8], i: int, cl: &[u8], p: int, all: &[u8]) -> j: int {
        if p == all.len() {
            j == i;
        } else {
            some sym: int, a: int, n: int {
                symbol(s, i, cl) == sym;
                a == i + cl[sym];                                         // after the codeword
                if sym < 16 {
                    n == 1;
                    for k in p..p + n { all[k] == sym; }
                    lengths(s, a, cl, p + n, all) == j;
                } else if sym == 16 {
                    1 <= p;
                    n == 3 + field(s, a, 2);
                    p < p + n <= all.len();
                    for k in p..p + n { all[k] == all[p - 1]; }
                    lengths(s, a + 2, cl, p + n, all) == j;
                } else if sym == 17 {
                    n == 3 + field(s, a, 3);
                    p < p + n <= all.len();
                    for k in p..p + n { all[k] == 0; }
                    lengths(s, a + 3, cl, p + n, all) == j;
                } else {
                    sym == 18;
                    n == 11 + field(s, a, 7);
                    p < p + n <= all.len();
                    for k in p..p + n { all[k] == 0; }
                    lengths(s, a + 7, cl, p + n, all) == j;
                }
            }
        }
    }

    // A dynamic block's own codes (§3.2.7): the counts HLIT, HDIST, HCLEN in 5, 5 and 4 bits;
    // then HCLEN + 4 three-bit lengths of the code-length code, for the symbols in the order
    // CL_ORDER (the others are 0); then, in that code, the HLIT + 257 literal/length lengths
    // followed by the HDIST + 1 distance lengths, run-length coded.
    pub rel tables(s: &[u8], i: int, lit: &[u8], dist: &[u8]) -> j: int {
        some hclen: int, cl: Vec<u8>, all: Vec<u8> {
            lit.len() == 257 + field(s, i, 5);
            dist.len() == 1 + field(s, i + 5, 5);
            hclen == 4 + field(s, i + 10, 4);
            cl.len() == 19;
            for k in 0..19 {
                if k < hclen { cl[CL_ORDER[k]] == field(s, i + 14 + 3 * k, 3); } else { cl[CL_ORDER[k]] == 0; }
            }
            valid(cl, 7);
            all.len() == lit.len() + dist.len();
            all[..lit.len()] == lit;
            all[lit.len()..all.len()] == dist;
            lengths(s, i + 14 + 3 * hclen, cl, 0, all) == j;
            valid(lit, 15);
            valid(dist, 15);
        }
    }

    // One block: its type in two bits, then stored (0), coded with the fixed codes (1), or
    // coded with its own codes (2). Extends `prev` to `out`, ends at bit j.
    pub rel block(s: &[u8], i: int, prev: &[u8], out: &[u8]) -> j: int {
        if field(s, i, 2) == 0 {
            stored(s, i + 2, prev, out) == j;
        } else if field(s, i, 2) == 1 {
            symbols(s, i + 2, fixedlit(), fixeddist(), prev, out) == j;
        } else {
            field(s, i, 2) == 2;
            some lit: Vec<u8>, dist: Vec<u8>, k: int {
                tables(s, i + 2, lit, dist) == k;
                symbols(s, k, lit, dist, prev, out) == j;
            }
        }
    }

    // A DEFLATE stream: blocks, each announced by a BFINAL bit, up to and including the final
    // one. Copies may reach back into earlier blocks, so each block extends what the blocks
    // before it produced. Starts at bit i, turns `prev` into `out`, ends at bit j.
    #[decreases(8 * s.len() - i)]
    pub rel blocks(s: &[u8], i: int, prev: &[u8], out: &[u8]) -> j: int {
        if bit(s, i) == 0 {
            some mid: Vec<u8>, k: int {
                block(s, i + 1, prev, mid) == k;
                i < k <= 8 * s.len();
                blocks(s, k, mid, out) == j;
            }
        } else {
            block(s, i + 1, prev, out) == j;
        }
    }

    // ================================================================ CRC-32
    //
    // Exclusive or, bit by bit.
    #[requires(0 <= a && 0 <= b)]
    #[ensures(0 <= c)]
    #[decreases(a + b)]
    pub rel xor(a: int, b: int) -> c: int {
        if a == 0 && b == 0 { c == 0; } else { c == (a + b) % 2 + 2 * xor(a / 2, b / 2); }
    }

    // CRC-32 as gzip uses it (ISO 3309): the register starts at all ones; each byte is xored
    // into its low bits, then the register is shifted right eight times, the reversed polynomial
    // xored in whenever a one bit falls out; the checksum is the complement of the register.
    #[requires(0 <= c)]
    #[ensures(0 <= d)]
    pub rel crcbit(c: int) -> d: int {
        if c % 2 == 1 { d == xor(c / 2, POLY); } else { d == c / 2; }
    }

    #[requires(0 <= c && 0 <= n)]
    #[ensures(0 <= d)]
    #[decreases(n)]
    pub rel crcbits(c: int, n: int) -> d: int {
        if n == 0 { d == c; } else { d == crcbit(crcbits(c, n - 1)); }
    }

    // The register after the first n bytes of data.
    #[requires(0 <= n <= data.len())]
    #[ensures(0 <= c)]
    #[decreases(n)]
    pub rel crcreg(data: &[u8], n: int) -> c: int {
        if n == 0 { c == 4294967295; } else { c == crcbits(xor(crcreg(data, n - 1), data[n - 1]), 8); }
    }

    pub fn crc32(data: &[u8]) -> c: u32 {
        c == xor(crcreg(data, data.len()), 4294967295);
    }

    // ============================================================ gzip (RFC 1952)
    //
    // Bit k of the flags byte, and the first zero byte at or after i.
    #[requires(0 <= k)]
    pub rel flag(f: int, k: int) -> b: bool {
        b == ((f / 2.pow(k)) % 2 == 1);
    }

    pub rel zero(s: &[u8], i: int) -> z: int {
        0 <= i <= z < s.len();
        s[z] == 0;
        for k in i..z { s[k] != 0; }
    }

    // The header occupies the first n bytes: ID1 ID2, CM = 8 (deflate), FLG, then six bytes nobody
    // checks (MTIME, XFL, OS), then the optional fields the flags announce.
    pub rel header(s: &[u8]) -> n: int {
        10 <= s.len();
        s[0] == 31 && s[1] == 139 && s[2] == 8;
        s[3] < 32;                                                        // the three reserved flag bits are zero
        some a: int, b: int, c: int {
            if flag(s[3], 2) { a == 12 + u16le(s, 10); } else { a == 10; } // FEXTRA: a 16-bit length, then that many bytes
            if flag(s[3], 3) { b == zero(s, a) + 1; } else { b == a; }    // FNAME: a zero-terminated string
            if flag(s[3], 4) { c == zero(s, b) + 1; } else { c == b; }    // FCOMMENT: another
            if flag(s[3], 1) { n == c + 2; } else { n == c; }             // FHCRC: a 16-bit header checksum (not checked)
            n <= s.len();
        }
    }

    // A gzip member and its content: the header, a DEFLATE stream, and from the next byte
    // boundary the CRC-32 and the length (mod 2^32) of the content, little-endian. Nothing may
    // follow.
    pub rel member(s: &[u8]) -> out: Vec<u8> {
        some h: int, j: int, t: int {
            header(s) == h;
            blocks(s, 8 * h, b"", out) == j;
            t == (j + 7) / 8;
            s.len() == t + 8;
            u32le(s, t) == crc32(out);
            u32le(s, t + 4) == out.len() % 4294967296;
        }
    }

    // Some(content) if s is a gzip member with at most MAXOUT bytes of content, else None.
    pub fn decompress(s: &[u8]) -> r: Option<Vec<u8>> {
        r.is_some() == (s in domain(member) && member(s).len() <= MAXOUT);
        r.is_some() => member(s) == r.unwrap();
    }

    // ============================================================== compress
    //
    // lean-zip specifies its compressor only by the round trip, and so does this: `compress`
    // produces the fixed gzip header (ID1 ID2, CM = deflate, FLG = 0, MTIME = 0, then XFL from the
    // level as lean-zip sets it — 0 for level 0, 4 "fastest" for 1–4, 2 "slowest" from 5 on — and
    // OS = unknown) followed by whatever `decompress` reads back as the data. Which member that is,
    // and so the parse, the blocks, the codes and the speed/ratio trade-off of every level, is the
    // implementer's choice (`any`); the choice is reviewed by a human (`#[weakly_specified]`).
    // The intent for the levels: level 1 radically fast, level 10 radically dense, the levels
    // between trading one for the other.
    #[weakly_specified]
    #[requires(data.len() <= MAXOUT)]
    #[ensures(decompress(out) == Some(data))]
    pub fn compress(data: &[u8], level: u8) -> out: Vec<u8> {
        any o: Vec<u8> where decompress(o) == Some(data);
        out == o;
        out.len() >= 18;                                                  // a member: 10 header bytes, 8 trailer bytes
        out[..8] == HEADER;
        out[8] == if level == 0 { 0 } else if level < 5 { 4 } else { 2 };
        out[9] == 255;
    }
}

// ------------------------------------------------------------------ a driver
//
// Plain Rust, not verified: reads nothing itself (main.rs does the I/O), calls the two verified
// functions, and turns None into a message.

/// Decompresses `input` when `level` is `None`, else compresses it at that level.
pub fn run(level: Option<u8>, input: &[u8]) -> Result<Vec<u8>, String> {
    match level {
        None => decompress(input).ok_or_else(|| format!("not a gzip member, or more than {MAXOUT} bytes of content")),
        Some(level) if input.len() <= MAXOUT => Ok(compress(input, level)),
        Some(_) => Err(format!("input exceeds {MAXOUT} bytes")),
    }
}
