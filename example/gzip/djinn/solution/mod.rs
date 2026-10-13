//! DEFLATE with stored, fixed and dynamic Huffman blocks: a greedy parser for the fast levels,
//! an optimal parser for level 10, and for every block whichever of the three block types is
//! smallest. The dynamic codes are built from the block's own symbol frequencies; everything
//! the decoder requires of them (lengths within the limit, the Kraft inequality, a codeword
//! below 2^length, a nonzero length for every symbol the block uses) is checked at run time,
//! with the fixed code as the fallback, so that the proof covers the checks and not the
//! construction.

const LENGTH_BASE: [usize; 29] = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LENGTH_EXTRA: [u32; 29] = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE: [usize; 30] = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA: [u32; 30] = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const CL_ORDER: [usize; 19] = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
// The length code of each length 3..258 (entries 0..2 unused), and the distance code of each
// distance 1..256 (entry 0 unused) and, for the distances above 256, of (dist - 1) / 128.
const LENGTH_CODE: [u8; 259] = [0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 12, 12, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28];
const DIST_CODE_LOW: [u8; 257] = [0, 0, 1, 2, 3, 4, 4, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15];
const DIST_CODE_HIGH: [u8; 256] = [0, 0, 16, 17, 18, 18, 19, 19, 20, 20, 20, 20, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29];

/// The length code of a length 3..258, by table.
fn length_code(len: usize) -> usize {
    if len < 259 { LENGTH_CODE[len] as usize } else { 28 }
}

/// The distance code of a distance 1..32768, by table.
fn distance_code(dist: usize) -> usize {
    if dist < 257 {
        DIST_CODE_LOW[dist] as usize
    } else if dist < 32769 {
        DIST_CODE_HIGH[(dist - 1) >> 7] as usize
    } else {
        29
    }
}

/// A codeword's bits reversed for the writer: DEFLATE fields are LSB first, codes MSB first.
fn reverse_code(value: u32, count: u32) -> u32 {
    let mut v = value;
    v = ((v & 0x5555) << 1) | ((v >> 1) & 0x5555);
    v = ((v & 0x3333) << 2) | ((v >> 2) & 0x3333);
    v = ((v & 0x0f0f) << 4) | ((v >> 4) & 0x0f0f);
    v = ((v & 255) << 8) | ((v >> 8) & 255);
    v >> (16 - count)
}

/// Four bytes from `p` on as a little-endian word: one bounds check for the four, so that the
/// compiler loads them at once.
fn word(data: &[u8], p: usize) -> u32 {
    let w = &data[p..p + 4];
    w[0] as u32 + (w[1] as u32) * 256 + (w[2] as u32) * 65536 + (w[3] as u32) * 16777216
}

/// The table entry of the low byte of `x` in the sub-table starting at `base`.
fn look(table: &Vec<u32>, base: usize, x: u32) -> u32 {
    table[base + (x & 255) as usize]
}

/// The part of the register after the sixteen bytes from `p` that comes from their last
/// twelve bytes alone.
#[inline(always)]
fn crc_rest(data: &[u8], table: &Vec<u32>, p: usize) -> u32 {
    let w1 = word(data, p + 4);
    let w2 = word(data, p + 8);
    let w3 = word(data, p + 12);
    let t4 = look(table, 2816, w1);
    let t5 = look(table, 2560, w1 >> 8);
    let t6 = look(table, 2304, w1 >> 16);
    let t7 = look(table, 2048, w1 >> 24);
    let t8 = look(table, 1792, w2);
    let t9 = look(table, 1536, w2 >> 8);
    let t10 = look(table, 1280, w2 >> 16);
    let t11 = look(table, 1024, w2 >> 24);
    let t12 = look(table, 768, w3);
    let t13 = look(table, 512, w3 >> 8);
    let t14 = look(table, 256, w3 >> 16);
    let t15 = look(table, 0, w3 >> 24);
    (t4 ^ t5 ^ t6 ^ t7) ^ (t8 ^ t9 ^ t10 ^ t11) ^ (t12 ^ t13 ^ t14 ^ t15)
}

/// The part of the register after sixteen bytes that comes from the register xored with their
/// first four (`w0`).
#[inline(always)]
fn crc_head(table: &Vec<u32>, w0: u32) -> u32 {
    (look(table, 3840, w0) ^ look(table, 3584, w0 >> 8)) ^ (look(table, 3328, w0 >> 16) ^ look(table, 3072, w0 >> 24))
}

pub fn crc32(data: &[u8]) -> u32 {
    // `table[256 * j + b]` is the register after the byte `b` followed by `j` zero bytes, so
    // that eight bytes xored into the register are consumed with one lookup each.
    let mut table = Vec::with_capacity(4096);
    let mut i = 0u32;
    while i < 256 {
        let mut c = i;
        let mut n = 0;
        while n < 8 {
            c = if c & 1 == 1 { (c >> 1) ^ 0xedb88320 } else { c >> 1 };
            n += 1;
        }
        table.push(c);
        i += 1;
    }
    let mut k = 256;
    while k < 4096 {
        let prev = table[k - 256];
        let c = (prev >> 8) ^ table[(prev & 255) as usize];
        table.push(c);
        k += 1;
    }
    let mut c = 0xffffffff;
    let mut p = 0;
    // The twelve bytes of a block after its first four do not depend on the register: their
    // part is computed one block ahead, so that the register waits only for its own four.
    let mut x = if data.len() >= 16 { crc_rest(data, &table, 0) } else { 0 };
    while data.len() - p >= 32 {
        let w0 = c ^ word(data, p);
        let next = crc_rest(data, &table, p + 16);
        c = crc_head(&table, w0) ^ x;
        x = next;
        p += 16;
    }
    if data.len() - p >= 16 {
        let w0 = c ^ word(data, p);
        c = crc_head(&table, w0) ^ x;
        p += 16;
    }
    while p < data.len() {
        c = (c >> 8) ^ table[((c ^ data[p] as u32) & 255) as usize];
        p += 1;
    }
    c ^ 0xffffffff
}

struct Writer {
    out: Vec<u8>,
    bits: u64,
    count: u32,
}

impl Writer {
    /// Appends `count` bits (at most 32; fewer than 32 are pending): four whole bytes leave the
    /// accumulator at a time, so that most calls push nothing.
    #[inline(always)]
    fn bits(&mut self, value: u32, count: u32) {
        self.bits |= (value as u64) << self.count;
        self.count += count;
        if self.count >= 32 {
            let b = self.bits;
            self.out.push(b as u8);
            self.out.push((b >> 8) as u8);
            self.out.push((b >> 16) as u8);
            self.out.push((b >> 24) as u8);
            self.bits = b >> 32;
            self.count -= 32;
        }
    }

    /// Two fields of together at most 32 bits in one call.
    #[inline]
    fn bits2(&mut self, first: u32, first_count: u32, second: u32, second_count: u32) {
        self.bits(first | (second << first_count), first_count + second_count);
    }

    /// Emits both halves of a copy together when they fit one writer call.
    #[inline]
    fn pair(&mut self, first: u32, first_count: u32, second: u32, second_count: u32) {
        let count = first_count + second_count;
        if count <= 32 {
            self.bits2(first, first_count, second, second_count);
        } else {
            self.bits(first, first_count);
            self.bits(second, second_count);
        }
    }

    /// Pushes the pending whole bytes, then the partial one padded with zeros, if any.
    fn align(&mut self) {
        while self.count >= 8 {
            self.out.push(self.bits as u8);
            self.bits >>= 8;
            self.count -= 8;
        }
        if self.count != 0 {
            self.out.push(self.bits as u8);
            self.bits = 0;
            self.count = 0;
        }
    }

    fn code(&mut self, value: u32, count: u32) {
        // Reverse a codeword's bits: DEFLATE fields are LSB first, codes MSB first.
        let mut v = value;
        v = ((v & 0x5555) << 1) | ((v >> 1) & 0x5555);
        v = ((v & 0x3333) << 2) | ((v >> 2) & 0x3333);
        v = ((v & 0x0f0f) << 4) | ((v >> 4) & 0x0f0f);
        v = ((v & 255) << 8) | ((v >> 8) & 255);
        self.bits(v >> (16 - count), count);
    }

    fn symbol(&mut self, sym: usize) {
        if sym < 144 {
            self.code(sym as u32 + 48, 8);
        } else if sym < 256 {
            self.code(sym as u32 + 256, 9);
        } else if sym < 280 {
            self.code(sym as u32 - 256, 7);
        } else {
            self.code(sym as u32 - 88, 8);
        }
    }

    fn copy(&mut self, len: usize, dist: usize) {
        let l = length_code(len);
        let d = distance_code(dist);
        self.symbol(l + 257);
        self.bits((len - LENGTH_BASE[l]) as u32, LENGTH_EXTRA[l]);
        self.code(d as u32, 5);
        self.bits((dist - DIST_BASE[d]) as u32, DIST_EXTRA[d]);
    }
}

fn length_index(len: usize) -> usize {
    let mut i = 0;
    while i < 28 && LENGTH_BASE[i + 1] <= len {
        i += 1;
    }
    i
}

fn distance_index(dist: usize) -> usize {
    let mut i = 0;
    while i < 29 && DIST_BASE[i + 1] <= dist {
        i += 1;
    }
    i
}

/// `n` zeros, filled in one go (a push loop costs a noticeable share of a parsing pass).
fn zeros(n: usize) -> Vec<usize> {
    let mut v = Vec::new();
    v.resize(n, 0);
    v
}

fn zeros_u8(n: usize) -> Vec<u8> {
    let mut v = Vec::new();
    v.resize(n, 0);
    v
}

/// `n` zero prices: the price list before the first block.
fn zeros_u32(n: usize) -> Vec<u32> {
    let mut v = Vec::new();
    v.resize(n, 0);
    v
}

/// A hash of four bytes (below 2^32 before the mask): the bytes a, b, c, d weighted by the
/// powers of 251, taken from one word load, with the products independent of each other (the
/// hash is on the path from one position to the next, so its latency counts).
fn hash4(data: &[u8], p: usize, mask: usize) -> usize {
    let w = word(data, p) as usize;
    let a = w & 255;
    let b = (w >> 8) & 255;
    let c = (w >> 16) & 255;
    let d = w >> 24;
    (a * 15813251 + b * 63001 + c * 251 + d) & mask
}


/// A hash of five bytes (below 2^32 before the mask): the chains and trees of one hash then
/// hold fewer and longer candidates, which is worth more than the copies of four bytes it
/// misses at every level but the two densest, and makes the walks shorter. The value is
/// (a * 251 + b) * 63001 + (c * 251 + d) * 251 + e, computed as for `hash4`.
fn hash5(data: &[u8], p: usize, mask: usize) -> usize {
    let w = word(data, p) as usize;
    let e = data[p + 4] as usize;
    let a = w & 255;
    let b = (w >> 8) & 255;
    let c = (w >> 16) & 255;
    let d = w >> 24;
    (a * 15813251 + (b + c) * 63001 + d * 251 + e) & mask
}

/// The greedy chains mix the packed first four bytes with the fifth using two bounded
/// products. The hash retains byte order without extracting each byte separately.
fn chain_hash5(data: &[u8], p: usize, mask: usize) -> usize {
    let w = word(data, p) as u64;
    let e = data[p + 4] as u64;
    let mixed = w * 506832829 + e * 2654435761;
    ((mixed >> 16) as usize) & mask
}

/// The hash the trees of the optimal parser are keyed by at a position with at least four
/// bytes left: of five bytes when `five` and there are five, else of four.
fn tree_hash(data: &[u8], p: usize, mask: usize, five: bool) -> usize {
    if five && data.len() - p >= 5 { hash5(data, p, mask) } else { hash4(data, p, mask) }
}

/// Links position `p` into its hash chain (nothing if too few bytes remain for a hash).
fn insert(data: &[u8], p: usize, head: &mut Vec<u32>, chain: &mut Vec<u32>, five: bool) {
    let h = hash_at(data, p, head, five);
    insert_hashed(h, p, head, chain);
}

/// Enters a position inside a copy into the tables: above level 2 into its hash chain; at
/// level 2, which follows no chains, only as the latest position of its hash (the chain
/// writes would be wasted, and cost a tenth of the parse).
fn insert_at(data: &[u8], p: usize, head: &mut Vec<u32>, chain: &mut Vec<u32>, level: u8, five: bool) {
    if level > 2 {
        insert(data, p, head, chain, five);
    } else {
        let h = hash_at(data, p, head, five);
        if h < head.len() {
            let next = p + 1;
            head[h] = next as u32;
        }
    }
}

/// The matching prefix of two unequal packed words, through their first three bytes.
#[inline]
fn prefix3(a: u32, b: u32) -> usize {
    let first = if a & 255 == b & 255 { 1 } else { 0 };
    let second = if a & 65535 == b & 65535 { 1 } else { 0 };
    let third = if a & 16777215 == b & 16777215 { 1 } else { 0 };
    first + second + third
}

fn match_length(data: &[u8], p: usize, q: usize, end: usize) -> usize {
    let limit = if end - p < 258 { end - p } else { 258 };
    match_from(data, p, q, 0, limit)
}

/// Eight bytes from `p` on as a little-endian word, loaded at once like `word`.
fn word8(data: &[u8], p: usize) -> u64 {
    let w = &data[p..p + 8];
    w[0] as u64 + (w[1] as u64) * 256 + (w[2] as u64) * 65536 + (w[3] as u64) * 16777216 + (w[4] as u64) * 4294967296 + (w[5] as u64) * 1099511627776 + (w[6] as u64) * 281474976710656 + (w[7] as u64) * 72057594037927936
}

// Bit index of an isolated low bit, keyed by its wrapped de Bruijn product.
const CTZ64: [u32; 64] = [0, 1, 48, 2, 57, 49, 28, 3, 61, 58, 50, 42, 38, 29, 17, 4, 62, 55, 59, 36, 53, 51, 43, 22, 45, 39, 33, 30, 24, 18, 12, 5, 63, 47, 56, 27, 60, 41, 37, 16, 54, 35, 52, 21, 44, 32, 23, 11, 46, 26, 40, 15, 34, 20, 31, 10, 25, 14, 19, 9, 13, 8, 7, 6];

/// The matching byte prefix, capped at seven, from the lowest set bit of the words XOR.
/// Widening the negation and product makes the arithmetic checked; casts keep their low bits.
#[inline]
fn prefix7(x: u64, y: u64) -> usize {
    let x = x ^ y;
    if x == 0 { return 7; }
    let neg = (18446744073709551616u128 - x as u128) as u64;
    let low = x & neg;
    let mixed = ((low as u128) * 285870213051386505u128) as u64;
    let index = (mixed >> 58) as usize;
    (CTZ64[index] / 8) as usize
}

/// The match length from offset `from` on, up to `limit`: the bytes before `from` are not
/// compared (the tree walk knows them to be equal), so the result is only a guide for the walk.
/// Eight bytes per step, then four, then one at a time; a failed word gives its prefix without
/// rereading those bytes (the walk's comparisons were a byte loop with an unpredictable exit
/// at every node).
#[inline(always)]
fn match_from(data: &[u8], p: usize, q: usize, from: usize, limit: usize) -> usize {
    let a = &data[p..p + limit];
    let b = &data[q..q + limit];
    if from >= limit {
        return from;
    }
    let mut n = from;
    while limit - n >= 8 {
        let x = word8(a, n);
        let y = word8(b, n);
        if x != y {
            return n + prefix7(x, y);
        }
        n += 8;
    }
    match_tail(a, b, n, limit)
}

/// The last bytes of `match_from` (fewer than eight from `from`, which is at most `limit`):
/// four at once if there are four, then one at a time.
#[inline]
fn match_tail(a: &[u8], b: &[u8], from: usize, limit: usize) -> usize {
    let mut n = from;
    if limit - n >= 4 {
        let x = word(a, n);
        let y = word(b, n);
        if x != y {
            return n + prefix3(x, y);
        }
        n += 4;
    }
    while n < limit && a[n] == b[n] {
        n += 1;
    }
    n
}

/// The hash of position `p`: of five bytes when `five`, else of four; `head.len()` (out of
/// range) if fewer bytes remain.
#[inline(always)]
fn hash_at(data: &[u8], p: usize, head: &Vec<u32>, five: bool) -> usize {
    if five {
        if data.len() - p >= 5 { chain_hash5(data, p, head.len() - 1) } else { head.len() }
    } else if data.len() - p >= 4 {
        hash4(data, p, head.len() - 1)
    } else {
        head.len()
    }
}

/// Links position `p` into the chain of hash `h` (nothing if `h` is out of range).
fn insert_hashed(h: usize, p: usize, head: &mut Vec<u32>, chain: &mut Vec<u32>) {
    if h < head.len() {
        let previous = head[h];
        let next = p + 1;
        let slot = p & 32767;
        chain[slot] = previous;
        head[h] = next as u32;
    }
}

/// Whether the candidate `q` (before `p`) can still beat a match of `best` bytes at `p`: only
/// if its bytes up to offset `best` agree with `p`'s. The four bytes ending at `best` are
/// compared at once (one load each side) when there are that many, else the byte at `best`;
/// `p + best` must be within the data. A filter only: a candidate that passes is measured.
fn can_beat(data: &[u8], p: usize, q: usize, best: usize) -> bool {
    if best >= 3 {
        word(data, q + best - 3) == word(data, p + best - 3)
    } else {
        data[q + best] == data[p + best]
    }
}

fn find_match(data: &[u8], p: usize, end: usize, h: usize, head: &[u32], chain: &[u32], depth: usize) -> (usize, usize) {
    let mut best = 2;
    let mut distance = 0;
    if end - p >= 3 && h < head.len() {
        let mut candidate = head[h] as usize;
        let mut count = 0;
        while candidate != 0 && count < depth && best < 258 {
            let q = candidate - 1;
            if q >= p || p - q > 32768 {
                candidate = 0;
            } else {
                // Only a candidate that agrees up to offset `best` is measured.
                if best < end - p && can_beat(data, p, q, best) {
                    let n = match_length(data, p, q, end);
                    if n > best {
                        best = n;
                        distance = p - q;
                    }
                }
                candidate = chain[q & 32767] as usize;
            }
            count += 1;
        }
    }
    (best, distance)
}

// Plans carry a length and distance per token; a distance of zero means a literal.
struct Plan {
    lengths: Vec<u16>,
    distances: Vec<u16>,
}

/// The match length at level 1, where most candidates of the small table are false: the
/// low three bytes of the words at `p` and `q` are compared at once (0 for a disagreement:
/// no copy), and the length is measured only when all four agree.
#[inline]
fn first_length(data: &[u8], p: usize, q: usize, end: usize) -> usize {
    if end - p >= 4 {
        let x = word(data, p) ^ word(data, q);
        if x & 16777215 != 0 {
            0
        } else if x != 0 {
            3
        } else {
            let limit = if end - p < 258 { end - p } else { 258 };
            match_from(data, p, q, 4, limit)
        }
    } else {
        match_length(data, p, q, end)
    }
}

/// Level 1 keeps only the latest position of each hash: no chain is followed or updated.
#[inline]
fn first_match(data: &[u8], p: usize, end: usize, h: usize, head: &mut Vec<u32>) -> (usize, usize) {
    if h < head.len() {
        let candidate = head[h] as usize;
        let next = p + 1;
        head[h] = next as u32;
        if end - p >= 3 && candidate != 0 {
            let q = candidate - 1;
            if q < p && p - q <= 32768 {
                let n = first_length(data, p, q, end);
                if n > 2 {
                    return (n, p - q);
                }
            }
        }
    }
    (2, 0)
}

/// Keeps one useful position inside a level-1 copy for later direct matches.
#[inline]
fn first_insert(data: &[u8], p: usize, head: &mut Vec<u32>) {
    let h = hash_at(data, p, head, false);
    if h < head.len() {
        let next = p + 1;
        head[h] = next as u32;
    }
}

/// The miss counter after a position without a copy: it counts up to 96 and then restarts
/// the sampled stretch at 32.
#[inline]
fn next_misses(misses: u32) -> u32 {
    if misses < 96 { misses + 1 } else { 32 }
}

/// The match at a position of levels 2 and 3 (no lookahead; level 1 has its own parse):
/// level 2's latest position of the hash, level 3's chain.
#[inline]
fn choose_match(data: &[u8], p: usize, end: usize, level: u8, depth: usize, head: &mut Vec<u32>, chain: &mut Vec<u32>, five: bool) -> (usize, usize) {
    let h = hash_at(data, p, head, five);
    // Level 2 takes the latest position of the hash and follows no chain.
    if level <= 2 {
        return first_match(data, p, end, h, head);
    }
    let (len, dist) = find_match(data, p, end, h, head, chain, depth);
    insert_hashed(h, p, head, chain);
    (len, dist)
}

/// The depth of the lookahead search at the lazy levels: far below the depth of the search
/// itself (4, 4, 8 and 16 at levels 4 to 7), which tells a longer match from a short one
/// almost as well for a fraction of the walk; the seed parse of the optimal levels (level 11)
/// looks ahead as deep as it searches.
fn lazy_depth(level: u8, depth: usize) -> usize {
    if level == 4 || level == 5 { 4 } else if level == 6 { 8 } else if level == 7 { 16 } else { depth }
}

/// Copies of at least this length are taken without lookahead: 6 at level 4, 12 at levels 5
/// and 6, 16 at level 7, and 4 for the seed (level 11: so none with a hash of five bytes).
fn lazy_limit(level: u8) -> usize {
    if level == 4 { 6 } else if level == 7 { 16 } else if level > 7 { 4 } else if level > 4 { 12 } else { 8 }
}

/// The extra bits of a distance's code (0 for no distance).
fn extra_bits(dist: usize) -> usize {
    let d = distance_code(dist);
    if d < 30 { DIST_EXTRA[d] as usize } else { 0 }
}

/// Whether the lookahead's copy (`next` bytes at distance `ndist` from the next position)
/// wins over the copy at the position (`len` at `dist`), which then becomes a literal. At
/// levels 4 to 7 by the gains of the two copies (zstd's estimate): four times the length less
/// the extra bits of the distance, the copy at the position taking a bonus of 3; for the
/// optimal levels' seed (level 11) when the lookahead's is at least two bytes longer.
fn defers(level: u8, len: usize, dist: usize, next: usize, ndist: usize) -> bool {
    if level < 8 {
        let e1 = extra_bits(dist);
        let e2 = extra_bits(ndist);
        next > len && 4 * next + e1 > 4 * len + e2 + 3
    } else {
        next > len + 1
    }
}

/// The depth of the chain search of a greedy level: 1 and 2 at levels 1 and 2 (which follow
/// no chain), 4 at level 3, then 12, 32, 48 and 96 at levels 4 to 7, and 16 for the optimal
/// levels' seed (level 11).
fn chain_depth(level: u8) -> usize {
    if level <= 2 {
        level as usize
    } else if level == 3 {
        4
    } else if level == 4 {
        12
    } else if level == 5 {
        32
    } else if level == 6 {
        48
    } else if level == 7 {
        96
    } else {
        16
    }
}

/// The match at `p`: the carried one (`cl`, `cd`) if there is one (`cl` is not 0), else the
/// chain's.
fn carried_or_found(data: &[u8], p: usize, end: usize, h: usize, head: &[u32], chain: &[u32], depth: usize, cl: usize, cd: usize) -> (usize, usize) {
    if cl != 0 {
        (cl, cd)
    } else {
        find_match(data, p, end, h, head, chain, depth)
    }
}

/// The match at `p` at the lazy levels (above 3), and the match carried to `p + 1`: the one at
/// `p` is the carried one (`cl`, `cd`: what the previous position's lookahead found at `p`) if
/// there is one, else searched; when it is short, the position after it is searched (the
/// lookahead), and if that finds a longer match the position is a literal and the lookahead's
/// match is carried to the next position, which is then not searched again (zlib's lazy
/// evaluation). Returns the length and distance at `p` and the carried length (0 for none) and
/// distance.
fn lazy_match(data: &[u8], p: usize, end: usize, level: u8, depth: usize, head: &mut Vec<u32>, chain: &mut Vec<u32>, five: bool, cl: usize, cd: usize) -> (usize, usize, usize, usize) {
    let h = hash_at(data, p, head, five);
    let (len, dist) = carried_or_found(data, p, end, h, head, chain, depth, cl, cd);
    insert_hashed(h, p, head, chain);
    if len < lazy_limit(level) && len >= 3 && p + 1 < end {
        let h1 = hash_at(data, p + 1, head, five);
        let (next, ndist) = find_match(data, p + 1, end, h1, head, chain, lazy_depth(level, depth));
        if defers(level, len, dist, next, ndist) {
            return (1, 0, next, ndist);
        }
    }
    (len, dist, 0, 0)
}

/// The match at `p` and the one carried to `p + 1`: the lazy search above level 3 (which may
/// carry a match), the plain one below (which never does).
fn step_match(data: &[u8], p: usize, end: usize, level: u8, depth: usize, head: &mut Vec<u32>, chain: &mut Vec<u32>, five: bool, cl: usize, cd: usize) -> (usize, usize, usize, usize) {
    if level > 3 {
        lazy_match(data, p, end, level, depth, head, chain, five, cl, cd)
    } else {
        let (len, dist) = choose_match(data, p, end, level, depth, head, chain, five);
        (len, dist, 0, 0)
    }
}

/// After 32 positions in a row without a copy, only one position in sixteen is searched (the
/// gap to the next one is filled with literals) until a copy is found.
#[inline]
fn sample_gap(misses: u32) -> usize {
    if misses >= 32 && misses < 96 && misses & 15 != 0 {
        16 - (misses & 15) as usize
    } else {
        0
    }
}

#[inline]
fn advance_misses(misses: u32, skip: u32) -> u32 {
    misses + skip
}

/// A plan with what the block writer needs of it: the length and distance code indices of its
/// tokens (0 for literals) and the frequencies of its literal/length and distance symbols,
/// counted while the tokens were chosen (`fused`), or left empty for the writer to count.
struct Parsed {
    plan: Plan,
    lsym: Vec<u8>,
    dsym: Vec<u8>,
    lfreq: Vec<usize>,
    dfreq: Vec<usize>,
    fused: bool,
}

/// A plan alone, with nothing counted.
fn unfused(plan: Plan) -> Parsed {
    Parsed { plan, lsym: Vec::new(), dsym: Vec::new(), lfreq: Vec::new(), dfreq: Vec::new(), fused: false }
}

/// Whether a found match (`dist` 0 for none) is taken: a copy of three bytes from far away
/// costs about what the literals cost.
#[inline]
fn taken(len: usize, dist: usize) -> bool {
    dist != 0 && (len > 3 || dist <= 4096)
}

/// Counts the `n` literals from `p` on.
fn count_literals(data: &[u8], p: usize, n: usize, lit: &mut Vec<usize>, dist: &mut Vec<usize>) {
    let mut k = 0;
    while k < n {
        count_symbols(data, p + k, 0, 0, 0, lit, dist);
        k += 1;
    }
}

/// Level 1's sampled parse. Positions between two samples contain only literals: fill their
/// tokens together instead of calling the matcher and pushing two tokens for each byte. The
/// miss counter lives in a register (it was a slot of the unused chain table, a store and a
/// load on every position), and level 1 has no chain table at all.
fn greedy_fast(data: &[u8], start: usize, end: usize, head: &mut Vec<u32>) -> Parsed {
    let mut plan = Plan { lengths: Vec::with_capacity(end - start), distances: Vec::with_capacity(end - start) };
    let mut lsym = Vec::with_capacity(end - start);
    let mut dsym = Vec::with_capacity(end - start);
    let mut lit = zeros(286);
    let mut dist = zeros(30);
    let mut p = start;
    let mut misses = 0u32;
    while p < end {
        let gap = sample_gap(misses);
        if gap != 0 {
            let remaining = end - p;
            let skip = if remaining < gap { remaining } else { gap };
            plan.lengths.resize(plan.lengths.len() + skip, 1);
            plan.distances.resize(plan.distances.len() + skip, 0);
            lsym.resize(lsym.len() + skip, 0);
            dsym.resize(dsym.len() + skip, 0);
            count_literals(data, p, skip, &mut lit, &mut dist);
            let skipped = skip as u32;
            misses = advance_misses(misses, skipped);
            p += skip;
        } else {
            let h = hash_at(data, p, head, false);
            let (len, d) = first_match(data, p, end, h, head);
            misses = if d != 0 { 0 } else { next_misses(misses) };
            if taken(len, d) {
                plan.lengths.push(len as u16);
                plan.distances.push(d as u16);
                let l = length_code(len);
                let dc = distance_code(d);
                lsym.push(l as u8);
                dsym.push(dc as u8);
                count_symbols(data, p, d, l, dc, &mut lit, &mut dist);
                let keep = if d < len { len - d } else { len - 1 };
                first_insert(data, p + keep, head);
                p += len;
            } else {
                plan.lengths.push(1);
                plan.distances.push(0);
                lsym.push(0);
                dsym.push(0);
                count_symbols(data, p, 0, 0, 0, &mut lit, &mut dist);
                p += 1;
            }
        }
    }
    let c = lit[256] + 1;
    lit[256] = c;
    Parsed { plan, lsym, dsym, lfreq: lit, dfreq: dist, fused: true }
}

/// Stop searching a chunk whose first four KiB contain almost entirely literal tokens.
/// The cheap token-count guard avoids dividing at positions with many useful copies.
#[inline]
fn literal_tail(level: u8, start: usize, p: usize, tokens: usize) -> bool {
    if tokens < 4000 || level < 2 || (level > 7 && level != 11) {
        return false;
    }
    let consumed = p - start;
    consumed >= 4096 && tokens > consumed - consumed / 100
}

/// A periodic copy repeats its interior hashes. Keep the last period and the
/// four windows that reach beyond the copy. Preserve the seed (level 11).
fn insertion_start(len: usize, dist: usize, level: u8) -> usize {
    if len > 5 && dist < len - 4 && level < 8 { len - dist - 4 } else { 1 }
}

/// The greedy parse (lazy above level 3) with chains of hashes of five bytes when `five`, else
/// of four; levels 1 and 2 keep only the latest position of each hash (level 2 also enters the
/// positions inside its copies), the levels above search their chains to `chain_depth`; at
/// level 0 the plan is all literals. Level 11 is the
/// seed parse of the optimal levels (`first_prices`).
fn greedy(data: &[u8], start: usize, end: usize, level: u8, head: &mut Vec<u32>, chain: &mut Vec<u32>, five: bool) -> Parsed {
    if level == 1 {
        return greedy_fast(data, start, end, head);
    }
    let mut plan = Plan { lengths: Vec::with_capacity(end - start), distances: Vec::with_capacity(end - start) };
    let mut lsym = Vec::with_capacity(end - start);
    let mut dsym = Vec::with_capacity(end - start);
    let mut lit = zeros(286);
    let mut dist = zeros(30);
    let depth = chain_depth(level);
    let mut p = start;
    // The match the lookahead found at `p`, if any (`cl` is 0 for none).
    let mut cl = 0;
    let mut cd = 0;
    while p < end {
        if literal_tail(level, start, p, plan.lengths.len()) {
            let remaining = end - p;
            plan.lengths.resize(plan.lengths.len() + remaining, 1);
            plan.distances.resize(plan.distances.len() + remaining, 0);
            lsym.resize(lsym.len() + remaining, 0);
            dsym.resize(dsym.len() + remaining, 0);
            count_literals(data, p, remaining, &mut lit, &mut dist);
            p = end;
            cl = 0;
            cd = 0;
        } else {
            let (len, d, nl, nd) = step_match(data, p, end, level, depth, head, chain, five, cl, cd);
            cl = nl;
            cd = nd;
            if taken(len, d) {
                plan.lengths.push(len as u16);
                plan.distances.push(d as u16);
                let l = length_code(len);
                let dc = distance_code(d);
                lsym.push(l as u8);
                dsym.push(dc as u8);
                count_symbols(data, p, d, l, dc, &mut lit, &mut dist);
                let mut k = insertion_start(len, d, level);
                if level > 1 {
                    while k < len {
                        insert_at(data, p + k, head, chain, level, five);
                        k += 1;
                    }
                }
                p += len;
            } else {
                plan.lengths.push(1);
                plan.distances.push(0);
                lsym.push(0);
                dsym.push(0);
                count_symbols(data, p, 0, 0, 0, &mut lit, &mut dist);
                p += 1;
            }
        }
    }
    let c = lit[256] + 1;
    lit[256] = c;
    Parsed { plan, lsym, dsym, lfreq: lit, dfreq: dist, fused: true }
}

// The parser's row: one cell per position, holding the bits of the cheapest path to it above
// bit 32, and the length (bits 16 to 31) and distance (the low 16 bits) of that path's last
// token. A cell is replaced when a path's bits are strictly lower, which is one comparison of
// whole cells against the candidate's bits with the low half all ones; the replacement is a
// selection, since whether a length wins is unpredictable.

/// The bits of a cell's path.
#[inline]
fn cell_cost(cell: u64) -> u64 {
    cell / 4294967296
}

/// The length of a cell's last token.
#[inline]
fn cell_length(cell: u64) -> usize {
    (cell % 4294967296 / 65536) as usize
}

/// The distance of a cell's last token (0 for a literal).
#[inline]
fn cell_distance(cell: u64) -> usize {
    (cell % 65536) as usize
}

/// The cell of `cost` bits with the low half all ones: below every cell of more bits, and
/// above every cell of at most `cost` bits.
#[inline]
fn probe(cost: u64) -> u64 {
    cost * 4294967296 + 4294967295
}

/// Prices the literal at `i` as the path to `i + 1`.
#[inline]
fn literal_step(bits: u32, i: usize, dp: &mut Vec<u64>) {
    let cost = cell_cost(dp[i]) + bits as u64;
    let next = i + 1;
    let old = dp[next];
    let fresh = cost * 4294967296 + 65536;
    let cell = if probe(cost) < old { fresh } else { old };
    dp[next] = cell;
}

/// Prices the literal `b` at `i` (of `bits` bits) and, when `record`, appends its edge (see
/// `relax_rec`): price index `b`, length 1, distance 0.
#[inline(always)]
fn literal_entry(bits: u32, b: u8, i: usize, dp: &mut Vec<u64>, record: bool, edges: &mut Vec<u64>) {
    literal_step(bits, i, dp);
    if record && edges.len() < 1073741824 {
        edges.push((i as u64) * 281474976710656 + (b as u64) * 4294967296 + 65536);
    }
}

/// The parser's price list: the bits of each literal/length symbol (286 entries, without the
/// extra bits), then the bits of a copy of each length 0..258 (259 entries from index 286 on:
/// its length symbol with the extra bits, so that pricing a length is one lookup), and of each
/// distance symbol (30 entries), under a block's own codes. A symbol costs at most 15 bits (a
/// symbol without a codeword 15), a length at most 20.
fn code_costs(lit: &Code, dist: &Code) -> (Vec<u32>, Vec<u32>) {
    let mut lcost = Vec::with_capacity(545);
    let mut i = 0;
    while i < 286 {
        let x = if i < lit.lens.len() { lit.lens[i] as u32 } else { 0 };
        lcost.push(if x == 0 || x > 15 { 15 } else { x });
        i += 1;
    }
    // Lengths below 3 are never priced.
    lcost.push(0);
    lcost.push(0);
    lcost.push(0);
    let mut len = 3;
    while len < 259 {
        let lc = length_code(len);
        let x = lcost[257 + lc] + LENGTH_EXTRA[lc];
        lcost.push(x);
        len += 1;
    }
    let mut dcost = Vec::with_capacity(30);
    i = 0;
    while i < 30 {
        let x = if i < dist.lens.len() { dist.lens[i] as u32 } else { 0 };
        dcost.push(if x == 0 || x > 15 { 15 } else { x });
        i += 1;
    }
    (lcost, dcost)
}

/// Prices the copies of lengths `longest + 1..=n` at distance `dist` from position `i`: the
/// hot loop of every pass. Its bounds are established once, before the loop (`n` below 259,
/// the last cell within the row, the price list of its full length: all three always hold),
/// and the loop then runs on the cell index `j` up to the last cell, so that the compiler
/// proves the cell index in range and drops the check from every iteration; the prices are
/// still indexed by the length.
#[inline(always)]
fn relax(i: usize, n: usize, dist: usize, longest: usize, lcost: &Vec<u32>, dcost: &Vec<u32>, dp: &mut Vec<u64>) {
    let dc = distance_code(dist);
    let base = cell_cost(dp[i]) + (dcost[dc] + DIST_EXTRA[dc]) as u64;
    let tail = dist as u64;
    let mut len = longest + 1;
    let last = i + n;
    if n < 259 && last < dp.len() && lcost.len() == 545 {
        let mut j = i + len;
        while j <= last {
            let cost = base + lcost[286 + len] as u64;
            let old = dp[j];
            let fresh = cost * 4294967296 + (len as u64) * 65536 + tail;
            let cell = if probe(cost) < old { fresh } else { old };
            dp[j] = cell;
            len += 1;
            j += 1;
        }
    }
}

/// `relax` for a recording pass, which also appends each length it prices as an edge for the
/// later passes: one word holding the index of the position (from bit 48), the index of the
/// edge's price in `edge_prices` (bits 32 to 47: 256 + 256 * distance code + length - 3), and
/// the cell's low half (the length from bit 16, the distance). A later pass is then one loop
/// over the edges, with no branch on how many candidates a position has.
#[inline(always)]
fn relax_rec(i: usize, n: usize, dist: usize, longest: usize, lcost: &Vec<u32>, dcost: &Vec<u32>, dp: &mut Vec<u64>, edges: &mut Vec<u64>) {
    let dc = distance_code(dist);
    let base = cell_cost(dp[i]) + (dcost[dc] + DIST_EXTRA[dc]) as u64;
    let tail = dist as u64;
    let mut len = longest + 1;
    let last = i + n;
    if n < 259 && last < dp.len() && lcost.len() == 545 {
        let mut j = i + len;
        let ebase = (i as u64) * 281474976710656 + ((253 + 256 * dc) as u64) * 4294967296 + tail;
        while j <= last {
            let cost = base + lcost[286 + len] as u64;
            let old = dp[j];
            let fresh = cost * 4294967296 + (len as u64) * 65536 + tail;
            let cell = if probe(cost) < old { fresh } else { old };
            dp[j] = cell;
            if edges.len() < 1073741824 {
                edges.push(ebase + (len as u64) * 4295032832);
            }
            len += 1;
            j += 1;
        }
    }
}

/// Prices a verified match at `i`: recording its edges when `record`.
#[inline(always)]
fn price_match(i: usize, n: usize, dist: usize, longest: usize, lcost: &Vec<u32>, dcost: &Vec<u32>, dp: &mut Vec<u64>, record: bool, edges: &mut Vec<u64>) {
    if record {
        relax_rec(i, n, dist, longest, lcost, dcost, dp, edges);
    } else {
        relax(i, n, dist, longest, lcost, dcost, dp);
    }
}

/// The initial row: 0 at the block's start, infinity (2^30 - 1 bits) elsewhere.
fn initial_costs(size: usize) -> Vec<u64> {
    let mut dp = Vec::new();
    dp.resize(size + 1, 4611686014132420608);
    dp[0] = 0;
    dp
}

/// The initial row of a later pass: 0 at the block's start, elsewhere infinity with a literal
/// as the last token (so that every cell holds a token, reached or not; the edges reach all).
fn literal_row(size: usize) -> Vec<u64> {
    let mut dp = Vec::new();
    dp.resize(size + 1, 4611686014132486144);
    dp[0] = 0;
    dp
}

/// The plan of the cheapest path, read back from the last position and reversed.
fn trace(size: usize, dp: &Vec<u64>) -> Plan {
    let mut plan = Plan { lengths: Vec::new(), distances: Vec::new() };
    let mut i = size;
    while i > 0 {
        let cell = dp[i];
        let len = cell_length(cell);
        plan.lengths.push(len as u16);
        plan.distances.push(cell_distance(cell) as u16);
        i -= len;
    }
    // Reverse the path reconstructed from the last position.
    let mut i = 0;
    while i < plan.lengths.len() / 2 {
        let j = plan.lengths.len() - 1 - i;
        let l = plan.lengths[i];
        let d = plan.distances[i];
        plan.lengths[i] = plan.lengths[j];
        plan.distances[i] = plan.distances[j];
        plan.lengths[j] = l;
        plan.distances[j] = d;
        i += 1;
    }
    plan
}

/// Save the predecessor distance of a long copy together with its remaining positions. An
/// endpoint whose predecessor has this length starts at `i`, certifying precisely the copy
/// whose interior positions will be entered next. Keep only the count when no such copy won.
fn cache_skip(i: usize, len: usize, dp: &Vec<u64>) -> usize {
    let remaining = if len > 0 && len <= 258 { len - 1 } else { 0 };
    if i < dp.len() && len < dp.len() - i {
        let cell = dp[i + len];
        if cell_length(cell) == len {
            let dist = cell_distance(cell);
            if dist <= 32768 {
                return dist * 512 + remaining;
            }
        }
    }
    remaining
}

/// Whether a position enters its tree. Every searching position does; of the positions
/// inside a long copy (only inserted, never searched, and their walks were a quarter of all
/// the nodes visited) levels 8 and 9 enter every sixth one, level 10 every second one. A copy
/// of the maximal length 258 chains on searched positions and 258 is a multiple of 6 (and of
/// 2), so the chains inside a long repetition lose nothing; a copy whose source lies inside
/// another long copy may have to start a few bytes later.
#[inline]
fn entered(searching: bool, depth: usize, p: usize) -> bool {
    if searching {
        true
    } else if depth > 32 {
        p % 2 == 0
    } else {
        p % 6 == 0
    }
}

/// The optimal parse of a block under a price list: the cheapest path through the positions,
/// each position priced as a literal and from the candidates met on its way into the binary
/// tree of the positions with its hash. The tree of hash `h` is rooted at `head[h]` (a position
/// plus one, 0 for none) and ordered by the suffixes; the children of the position `q` are
/// `chain[2 * (q & 32767)]` (smaller suffixes) and `chain[2 * (q & 32767) + 1]` (greater).
/// Walking down from the root to the place of `p` meets its nearest suffixes in the order,
/// hence its longest matches; `p` then becomes the new root, with the walk's smaller and
/// greater nodes as its subtrees. The tree is only a guide: every match is verified.
/// When `record`, also returns the candidates that lengthened the match at each position, in
/// the order of the positions (`pack_hint`), for the later passes, which price them without
/// comparing again. The trees are keyed by a hash of five bytes when `five` (smaller trees,
/// shorter walks), else of four.
fn optimal(data: &[u8], start: usize, end: usize, head: &mut Vec<u32>, chain: &mut Vec<u32>, lcost: &Vec<u32>, dcost: &Vec<u32>, depth: usize, record: bool, five: bool, four: bool) -> (Plan, Vec<u64>) {
    let size = end - start;
    let mut dp = initial_costs(size);
    // A recording pass pushes an edge per position and per length priced (five or six per
    // position on text): room for eight per position up front, so that the list rarely regrows
    // (copying itself) in the middle of the walk.
    let mut hints: Vec<u64> = if record { Vec::with_capacity(8 * size) } else { Vec::new() };
    let mut p = start;
    // After a long match, the positions inside it are not priced (the copy through them is
    // almost always the cheapest path) for `skip` more positions: they are only entered into
    // the tree, with the comparison cut short.
    let mut skip = 0;
    while p < end {
        let i = p - start;
        literal_entry(lcost[data[p] as usize], data[p], i, &mut dp, record, &mut hints);
        let skip_count = skip % 512;
        let searching = skip_count == 0;
        if skip_count > 0 {
            skip -= 1;
        }
        let enter = entered(searching, depth, p);
        if end - p >= 4 && enter {
            // With `four` (and a table of two halves), the trees take the first half of `head`
            // and the second half holds the most recent position of each hash of four bytes:
            // the copies of four bytes the trees of five miss.
            let both = four && head.len() >= 65536;
            let tmask = if both { 32767 } else { head.len() - 1 };
            let h = tree_hash(data, p, tmask, five);
            let cur = head[h] as usize;
            let next = p + 1;
            head[h] = next as u32;
            let slot = p & 32767;
            // Where the next smaller and the next greater node of the walk get linked.
            let lt = 2 * slot;
            let gt = 2 * slot + 1;
            let mut longest = 2;
            if both {
                longest = four_candidate(data, p, end, i, cur, searching, record, head, lcost, dcost, &mut dp, &mut hints);
            }
            let full = if end - p < 258 { end - p } else { 258 };
            let limit = if depth > 32 {
                if searching || full < 96 { full } else { 96 }
            } else {
                if searching || full < 32 { full } else { 32 }
            };
            // The two walks are separate functions, so that the searching walk (inlined here)
            // keeps its state in registers: with the insertion-only walk's cached comparison
            // in the same loop it spilled to the stack at every node.
            if searching {
                longest = walk_search(data, p, i, cur, depth, limit, chain, lt, gt, longest, lcost, dcost, &mut dp, record, &mut hints);
                if longest >= 64 {
                    skip = cache_skip(i, longest, &dp);
                }
            } else {
                walk_insert(data, p, cur, depth, limit, skip, chain, lt, gt);
            }
        }
        p += 1;
    }
    (trace(size, &dp), hints)
}

/// The walk of a searching position `p` down its tree from `cur`: the nodes met are its
/// nearest suffixes, each compared from the first byte, and every match longer than the ones
/// before is priced (and recorded when `record`); `p` is linked in as the new root (`lt` and
/// `gt` are its two pending links). Returns the longest match priced (`longest` if none).
#[inline(always)]
fn walk_search(data: &[u8], p: usize, i: usize, cur: usize, depth: usize, limit: usize, chain: &mut Vec<u32>, lt: usize, gt: usize, longest: usize, lcost: &Vec<u32>, dcost: &Vec<u32>, dp: &mut Vec<u64>, record: bool, hints: &mut Vec<u64>) -> usize {
    let mut cur = cur;
    let mut lt = lt;
    let mut gt = gt;
    let mut longest = longest;
    let mut count = 0;
    let mut go = true;
    // What the last pending links get: nothing, or the subtrees of the node that the
    // position replaces.
    let mut tail_lt = 0;
    let mut tail_gt = 0;
    while go && cur != 0 && count < depth {
        count += 1;
        let q = cur - 1;
        if q >= p || p - q >= 32768 {
            go = false;
        } else {
            let qs = q & 32767;
            let lo = 2 * qs;
            let hi = lo + 1;
            // Both children are read before the comparison, so that the one the walk
            // continues with is at hand whichever way the comparison goes; the
            // direction is then a plain selection, with no branch to mispredict. The
            // comparison gives the direction itself (`match_dir`), without a dependent
            // reload of the first differing bytes.
            let c_lt = chain[lo] as usize;
            let c_gt = chain[hi] as usize;
            let (n, lower) = match_dir(data, p, q, 0, limit);
            if n > longest {
                let m = if n <= limit { n } else { 0 };
                if m > longest {
                    price_match(i, m, p - q, longest, lcost, dcost, dp, record, hints);
                    longest = m;
                }
            }
            if n >= limit {
                // Equal as far as the walk compares: `p` takes the place of `q`.
                tail_lt = c_lt;
                tail_gt = c_gt;
                go = false;
            } else {
                // A smaller node is linked below and the walk goes on with its greater
                // child; a greater node is linked above and the walk goes on with its
                // smaller child.
                let slot = if lower { lt } else { gt };
                let next_lt = if lower { hi } else { lt };
                let next_gt = if lower { gt } else { lo };
                let next_cur = if lower { c_gt } else { c_lt };
                chain[slot] = cur as u32;
                lt = next_lt;
                gt = next_gt;
                cur = next_cur;
            }
        }
    }
    chain[lt] = tail_lt as u32;
    chain[gt] = tail_gt as u32;
    longest
}

/// `match_from` from 0 with the side of `q` in the tree: whether its first byte that differs
/// from `p`'s is the smaller one, which for a difference within eight bytes is a comparison of
/// the two words read big-endian, ready without the match length.
#[inline(always)]
fn match_dir(data: &[u8], p: usize, q: usize, from: usize, limit: usize) -> (usize, bool) {
    let a = &data[p..p + limit];
    let b = &data[q..q + limit];
    if from >= limit {
        return (from, false);
    }
    let mut n = from;
    while limit - n >= 8 {
        let x = word8(a, n);
        let y = word8(b, n);
        if x != y {
            return (n + prefix7(x, y), word_below(x, y));
        }
        n += 8;
    }
    let m = match_tail(a, b, n, limit);
    (m, byte_below(a, b, m, limit))
}

/// Inside a verified long copy, the matching source can supply the tree comparison without
/// reading its bytes again. The low nine bits of `skip` count the remaining positions and
/// the higher bits retain the copy's distance. Then the copy's own length is the comparison
/// (and the side is unused); otherwise `match_dir` from `from`.
#[inline]
fn dir_cached(data: &[u8], p: usize, q: usize, from: usize, limit: usize, skip: usize) -> (usize, bool) {
    if from <= limit && p - q == skip / 512 && limit <= skip % 512 + 1 {
        (limit, false)
    } else {
        match_dir(data, p, q, from, limit)
    }
}

/// A little-endian word's bytes in the opposite order: two such words compare as their bytes
/// do, first byte first.
#[inline(always)]
fn swap8(x: u64) -> u64 {
    let v = ((x & 0x00ff00ff00ff00ff) << 8) | ((x >> 8) & 0x00ff00ff00ff00ff);
    let v = ((v & 0x0000ffff0000ffff) << 16) | ((v >> 16) & 0x0000ffff0000ffff);
    (v << 32) | (v >> 32)
}

/// Whether the first byte where the word `y` differs from `x` is the smaller one.
#[inline(always)]
fn word_below(x: u64, y: u64) -> bool {
    swap8(y) < swap8(x)
}

/// Whether `b`'s byte at `m` is below `a`'s (false at `limit`).
#[inline(always)]
fn byte_below(a: &[u8], b: &[u8], m: usize, limit: usize) -> bool {
    if m < limit && m < a.len() && m < b.len() { b[m] < a[m] } else { false }
}

/// The walk of a position inside a long copy, which is only linked in as the new root: no
/// match is priced, so the comparison starts where the nodes already passed on both sides
/// agree with `p`, or takes the copy's own length (`dir_cached`). Kept out of line, apart
/// from the searching walk.
#[inline(never)]
fn walk_insert(data: &[u8], p: usize, cur: usize, depth: usize, limit: usize, skip: usize, chain: &mut Vec<u32>, lt: usize, gt: usize) {
    let mut cur = cur;
    let mut lt = lt;
    let mut gt = gt;
    let mut count = 0;
    let mut go = true;
    // The nodes already passed on each side agree with `p` for this many bytes, and
    // so does everything below them: the comparison starts there.
    let mut best_lt = 0;
    let mut best_gt = 0;
    // What the last pending links get: nothing, or the subtrees of the node that the
    // position replaces.
    let mut tail_lt = 0;
    let mut tail_gt = 0;
    while go && cur != 0 && count < depth {
        count += 1;
        let q = cur - 1;
        if q >= p || p - q >= 32768 {
            go = false;
        } else {
            let qs = q & 32767;
            let lo = 2 * qs;
            let hi = lo + 1;
            let c_lt = chain[lo] as usize;
            let c_gt = chain[hi] as usize;
            let lb = if best_lt < best_gt { best_lt } else { best_gt };
            let (n, lower) = dir_cached(data, p, q, lb, limit, skip);
            if n >= limit {
                tail_lt = c_lt;
                tail_gt = c_gt;
                go = false;
            } else {
                let slot = if lower { lt } else { gt };
                let next_lt = if lower { hi } else { lt };
                let next_gt = if lower { gt } else { lo };
                let next_cur = if lower { c_gt } else { c_lt };
                let next_best_lt = if lower { n } else { best_lt };
                let next_best_gt = if lower { best_gt } else { n };
                chain[slot] = cur as u32;
                lt = next_lt;
                gt = next_gt;
                cur = next_cur;
                best_lt = next_best_lt;
                best_gt = next_best_gt;
            }
        }
    }
    chain[lt] = tail_lt as u32;
    chain[gt] = tail_gt as u32;
}

/// The nearest copy of four bytes at a position of the trees keyed by five: the most recent
/// position with the same hash of four bytes, kept in the second half of `head` (which must
/// have two halves). It is priced (and recorded when `record`) when the position is searching,
/// it is not the tree's root (the nearest copy of five, which the walk prices), it is in a
/// cheaper distance class than the root, and it is verified; returns the length priced (2 for
/// none).
#[inline(never)]
fn four_candidate(data: &[u8], p: usize, end: usize, i: usize, cur: usize, searching: bool, record: bool, head: &mut Vec<u32>, lcost: &Vec<u32>, dcost: &Vec<u32>, dp: &mut Vec<u64>, hints: &mut Vec<u64>) -> usize {
    let h4 = 32768 + hash4(data, p, 32767);
    let c4 = head[h4] as usize;
    let next = p + 1;
    head[h4] = next as u32;
    let mut longest = 2;
    if searching && c4 != 0 && c4 != cur {
        let q = c4 - 1;
        let dcur = if cur == 0 || cur > p { 30 } else { distance_code(p + 1 - cur) };
        if q < p && p - q < 32768 && distance_code(p - q) < dcur {
            let m = match_length(data, p, q, end);
            if m > 2 {
                price_match(i, m, p - q, 2, lcost, dcost, dp, record, hints);
                longest = m;
            }
        }
    }
    longest
}

/// The price of every edge under a price list, by the edge's price index: the 256 literals,
/// then for each distance code (with its extra bits) the copies of each length 3..258 (with
/// theirs).
fn edge_prices(lcost: &Vec<u32>, dcost: &Vec<u32>) -> Vec<u32> {
    let mut t = Vec::with_capacity(7936);
    let mut c = 0;
    while c < 256 && c < lcost.len() {
        t.push(lcost[c]);
        c += 1;
    }
    let mut d = 0;
    while d < 30 && d < dcost.len() {
        let dp = dcost[d] as u64 + DIST_EXTRA[d] as u64;
        let mut len = 3;
        while len < 259 && 286 + len < lcost.len() {
            t.push((dp + lcost[286 + len] as u64) as u32);
            len += 1;
        }
        d += 1;
    }
    t
}

/// The optimal parse again under another price list, from the edges a first pass recorded (in
/// the order it priced them: by position, the literal first): each edge is priced as it is.
/// The cells reached through a position are final before its own edges are read, so this is
/// the same parse as pricing the positions one at a time, but with no branch per position.
fn optimal_hinted(data: &[u8], start: usize, end: usize, hints: &Vec<u64>, lcost: &Vec<u32>, dcost: &Vec<u32>) -> Plan {
    let size = end - start;
    let mut dp = literal_row(size);
    let prices = edge_prices(lcost, dcost);
    let mut e = 0;
    while e < hints.len() {
        let x = hints[e];
        let i = (x / 281474976710656) as usize;
        let c = (x / 4294967296 % 65536) as usize;
        let low = x % 4294967296;
        let j = i + (low / 65536) as usize;
        if j < dp.len() && c < prices.len() {
            let cost = cell_cost(dp[i]) + prices[c] as u64;
            let old = dp[j];
            dp[j] = if cost < old / 4294967296 { cost * 4294967296 + low } else { old };
        }
        e += 1;
    }
    trace(size, &dp)
}

/// The literal/length and distance code lengths used to price a plan.
fn plan_codes(data: &[u8], start: usize, plan: &Plan) -> (Code, Code) {
    let (lfreq, dfreq) = plan_histogram(data, start, &plan.lengths, &plan.distances);
    // Pricing only consumes the lengths: canonical words and their reversals are unused.
    // Keeping the zero tail gives the same price as a missing symbol in code_costs.
    let lit = Code { lens: code_lengths(&lfreq, 15), words: Vec::new(), rev: Vec::new() };
    let dist = Code { lens: code_lengths(&dfreq, 15), words: Vec::new(), rev: Vec::new() };
    (lit, dist)
}

/// The prices of a block's first optimal pass: the given ones (the previous block's), or for
/// the first block (`start` 0) the codes of a greedy parse of the block (with the level's
/// hash) at level 11: chains searched to depth 16 without lookahead, which as a seed ends in
/// smaller output at every optimal level than the lazy parses.
fn first_prices(data: &[u8], start: usize, end: usize, lcost: Vec<u32>, dcost: Vec<u32>, five: bool) -> (Vec<u32>, Vec<u32>) {
    if start == 0 {
        let mut seedhead = zeros_u32(32768);
        let mut seedchain = zeros_u32(65536);
        let seed = greedy(data, start, end, 11, &mut seedhead, &mut seedchain, five);
        let lit = Code { lens: code_lengths(&seed.lfreq, 15), words: Vec::new(), rev: Vec::new() };
        let dist = Code { lens: code_lengths(&seed.dfreq, 15), words: Vec::new(), rev: Vec::new() };
        code_costs(&lit, &dist)
    } else {
        (lcost, dcost)
    }
}

/// The absolute difference of two prices, counted as at most 64.
fn price_diff(a: u32, b: u32) -> u32 {
    let d = if a > b { a - b } else { b - a };
    if d > 64 { 64 } else { d }
}

/// Whether two price lists are nearly the same: the absolute differences of their symbol
/// prices (the 286 literal/length and the 30 distance symbols; the per-length entries follow
/// from the length symbols) sum to at most `limit`. A pass is a function of its prices, so
/// prices that have barely moved give the same plan, or nearly, and the passes are better
/// spent on the blocks whose prices still move.
fn near_prices(la: &Vec<u32>, da: &Vec<u32>, lb: &Vec<u32>, db: &Vec<u32>, limit: u32) -> bool {
    let mut gap = 0;
    let mut i = 0;
    while i < 286 && i < la.len() && i < lb.len() && gap <= limit {
        let d = price_diff(la[i], lb[i]);
        gap += d;
        i += 1;
    }
    i = 0;
    while i < 30 && i < da.len() && i < db.len() && gap <= limit {
        let d = price_diff(da[i], db[i]);
        gap += d;
        i += 1;
    }
    gap <= limit
}

/// Whether a chunk of at least 8 KiB looks incompressible: fewer than 8 of the positions of its
/// first 4 KiB find their four bytes again at the latest earlier position (in the chunk) with
/// the same hash. Random bytes find none; text, code and tables find thousands.
fn incompressible(data: &[u8], start: usize, end: usize) -> bool {
    if end - start < 8192 {
        return false;
    }
    let mut table = zeros_u32(4096);
    let mut hits = 0;
    let mut p = start;
    while p < start + 4096 {
        if hits >= 8 {
            break;
        }
        let h = hash4(data, p, 4095);
        let c = table[h] as usize;
        let next = p + 1;
        table[h] = next as u32;
        if c != 0 && c <= p && word(data, c - 1) == word(data, p) {
            hits += 1;
        }
        p += 1;
    }
    hits < 8
}

/// The plan of `n` literals.
fn literal_plan(n: usize) -> Plan {
    let mut plan = Plan { lengths: Vec::new(), distances: Vec::new() };
    plan.lengths.resize(n, 1);
    plan.distances.resize(n, 0);
    plan
}

/// The optimal parse of a block in at most `passes` passes; an incompressible chunk (whose
/// optimal parse would be all literals, and which is then stored) is not searched at all, and
/// takes the prices of its literal plan. The first pass is priced by
/// `lcost` and `dcost`, the codes of the previous block's final plan (a far better guess than
/// a greedy parse of the block itself, which seeds only the first block, at `start` 0); it
/// records the candidates, and later passes refit the prices to the preceding plan. A pass is
/// a function of its prices, so once a plan's prices nearly repeat the ones it was parsed
/// with (`near_prices`: the symbol prices moved by at most 12 bits in all), every further
/// pass would return the same plan, or nearly, and the passes stop (the plan is settled):
/// the pass budget goes to the blocks whose prices still move. With no recorded copies the
/// literal parse is already settled after fitting its prices. Returns
/// the plan and the prices of its own codes, for the next block. `five` selects the hash of
/// five bytes for the trees and the seed.
fn optimal_passes(data: &[u8], start: usize, end: usize, head: &mut Vec<u32>, chain: &mut Vec<u32>, passes: usize, depth: usize, lcost: Vec<u32>, dcost: Vec<u32>, five: bool, four: bool) -> (Plan, Vec<u32>, Vec<u32>) {
    if incompressible(data, start, end) {
        let plan = literal_plan(end - start);
        let (lit, dist) = plan_codes(data, start, &plan);
        let (lcost1, dcost1) = code_costs(&lit, &dist);
        return (plan, lcost1, dcost1);
    }
    // The seed parse hashes four bytes when the copies of four count (`four`).
    let seed_five = five && !four;
    let (lcost0, dcost0) = first_prices(data, start, end, lcost, dcost, seed_five);
    let (first, hints) = optimal(data, start, end, head, chain, &lcost0, &dcost0, depth, passes > 1, five, four);
    let mut plan = first;
    // The prices the plan was parsed with.
    let mut lcost1 = lcost0;
    let mut dcost1 = dcost0;
    let mut pass = 1;
    let mut settled = false;
    while pass < passes && !settled {
        let (lit, dist) = plan_codes(data, start, &plan);
        let (lcost2, dcost2) = code_costs(&lit, &dist);
        if hints.len() <= end - start || near_prices(&lcost1, &dcost1, &lcost2, &dcost2, 12) {
            settled = true;
        } else {
            plan = optimal_hinted(data, start, end, &hints, &lcost2, &dcost2);
        }
        lcost1 = lcost2;
        dcost1 = dcost2;
        pass += 1;
    }
    if settled {
        (plan, lcost1, dcost1)
    } else {
        let (lit, dist) = plan_codes(data, start, &plan);
        let (lcost3, dcost3) = code_costs(&lit, &dist);
        (plan, lcost3, dcost3)
    }
}

fn stored(writer: &mut Writer, data: &[u8], start: usize, end: usize, final_block: bool) {
    let header = if final_block { 1 } else { 0 };
    writer.bits(header, 3);
    writer.align();
    let len = (end - start) as u32;
    writer.bits(len, 16);
    writer.bits(65535 - len, 16);
    writer.out.extend_from_slice(&data[start..end]);
}

#[inline]
fn fixed(writer: &mut Writer, data: &[u8], start: usize, lengths: &Vec<u16>, distances: &Vec<u16>, final_block: bool) {
    let header = if final_block { 3 } else { 2 };
    writer.bits(header, 3);
    let mut p = start;
    let mut t = 0;
    while t < lengths.len() {
        let len = lengths[t] as usize;
        let dist = distances[t] as usize;
        if dist == 0 { writer.symbol(data[p] as usize); } else { writer.copy(len, dist); }
        p += len;
        t += 1;
    }
    writer.symbol(256);
}

// ================================================================ dynamic Huffman blocks

/// A Huffman code: the length of each symbol's codeword (0 for an unused symbol), the
/// canonical codeword itself, as the decoder derives it from the lengths, and the codeword
/// with its bits reversed, as the writer emits it.
struct Code {
    lens: Vec<u8>,
    words: Vec<usize>,
    rev: Vec<u32>,
}

/// The length and distance code indices of a plan's copies (0 for literals).
fn symbolize(lengths: &Vec<u16>, distances: &Vec<u16>) -> (Vec<u8>, Vec<u8>) {
    let mut lsym = Vec::with_capacity(lengths.len());
    let mut dsym = Vec::with_capacity(lengths.len());
    let mut t = 0;
    while t < lengths.len() {
        let dist = distances[t] as usize;
        if dist == 0 {
            lsym.push(0);
            dsym.push(0);
        } else {
            lsym.push(length_code(lengths[t] as usize) as u8);
            dsym.push(distance_code(dist) as u8);
        }
        t += 1;
    }
    (lsym, dsym)
}

/// How often each literal/length symbol and each distance symbol occurs in a plan.
fn histogram(data: &[u8], start: usize, lengths: &Vec<u16>, distances: &Vec<u16>, lsym: &Vec<u8>, dsym: &Vec<u8>) -> (Vec<usize>, Vec<usize>) {
    let mut lit = zeros(286);
    let mut dist = zeros(30);
    let mut p = start;
    let mut t = 0;
    while t < lengths.len() {
        let len = lengths[t] as usize;
        if distances[t] == 0 {
            let s = data[p] as usize;
            let c = lit[s] + 1;
            lit[s] = c;
        } else {
            let l = lsym[t] as usize;
            let d = dsym[t] as usize;
            if l < 29 && d < 30 {
                let c = lit[257 + l] + 1;
                lit[257 + l] = c;
                let e = dist[d] + 1;
                dist[d] = e;
            }
        }
        p += len;
        t += 1;
    }
    let c = lit[256] + 1;
    lit[256] = c;
    (lit, dist)
}

/// Counts already selected symbols without reading the plan and symbol arrays again.
#[inline]
fn count_symbols(data: &[u8], p: usize, dd: usize, l: usize, d: usize, lit: &mut Vec<usize>, dist: &mut Vec<usize>) {
    if dd == 0 {
        let s = data[p] as usize;
        let c = lit[s] + 1;
        lit[s] = c;
    } else if l < 29 && d < 30 {
        let c = lit[257 + l] + 1;
        lit[257 + l] = c;
        let e = dist[d] + 1;
        dist[d] = e;
    }
}

/// Frequencies for fitting and estimating a plan, without materializing unused symbol arrays.
fn plan_histogram(data: &[u8], start: usize, lengths: &Vec<u16>, distances: &Vec<u16>) -> (Vec<usize>, Vec<usize>) {
    let mut lit = zeros(286);
    let mut dist = zeros(30);
    let mut p = start;
    let mut t = 0;
    while t < lengths.len() {
        let len = lengths[t] as usize;
        let dd = distances[t] as usize;
        let (l, d) = if dd == 0 { (0, 0) } else { (length_code(len), distance_code(dd)) };
        count_symbols(data, p, dd, l, d, &mut lit, &mut dist);
        p += len;
        t += 1;
    }
    let c = lit[256] + 1;
    lit[256] = c;
    (lit, dist)
}

/// Symbol indices and frequencies in a single token pass.
fn symbols_histogram(data: &[u8], start: usize, lengths: &Vec<u16>, distances: &Vec<u16>) -> (Vec<u8>, Vec<u8>, Vec<usize>, Vec<usize>) {
    let mut lsym = Vec::with_capacity(lengths.len());
    let mut dsym = Vec::with_capacity(lengths.len());
    let mut lit = zeros(286);
    let mut dist = zeros(30);
    let mut p = start;
    let mut t = 0;
    while t < lengths.len() {
        let len = lengths[t] as usize;
        let dd = distances[t] as usize;
        let (l, d) = if dd == 0 { (0, 0) } else { (length_code(len), distance_code(dd)) };
        lsym.push(l as u8);
        dsym.push(d as u8);
        count_symbols(data, p, dd, l, d, &mut lit, &mut dist);
        p += len;
        t += 1;
    }
    let c = lit[256] + 1;
    lit[256] = c;
    (lsym, dsym, lit, dist)
}

/// The weight of a node of the Huffman tree (leaves are the symbols, then the inner nodes).
fn weight_of(weight: &Vec<usize>, node: usize) -> usize {
    if node < weight.len() { weight[node] } else { 0 }
}

/// The depth of each symbol's leaf in a Huffman tree of the frequencies: the used symbols are
/// sorted by frequency and merged with the queue of inner nodes, which is sorted by
/// construction. The one used symbol of a degenerate code gets depth 1. Depths saturate at
/// 1000, which the caller's limit rejects.
fn tree_depths(freq: &Vec<usize>) -> Vec<usize> {
    let n = freq.len();
    let mut order: Vec<usize> = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        if freq[i] > 0 {
            order.push(i);
            let mut j = order.len() - 1;
            let mut moving = true;
            while moving && j > 0 {
                let prev = order[j - 1];
                if weight_of(freq, prev) > freq[i] {
                    order[j] = prev;
                    j -= 1;
                } else {
                    moving = false;
                }
            }
            order[j] = i;
        }
        i += 1;
    }
    let used = order.len();
    let mut depth = zeros(n + used);
    if used == 1 {
        let s = order[0];
        if s < n { depth[s] = 1; }
    }
    if used >= 2 {
        // Node ids: the symbols, then inner node k at n + k.
        let mut weight = zeros(n + used);
        let mut left = zeros(used);
        let mut right = zeros(used);
        i = 0;
        while i < n {
            let w = freq[i];
            weight[i] = if w > 1073741824 { 1073741824 } else { w };
            i += 1;
        }
        let mut lq = 0;
        let mut iq = 0;
        let mut created = 0;
        let mut remaining = used;
        while remaining >= 2 && created < used {
            let a;
            if lq < used && (iq >= created || weight_of(&weight, order[lq]) <= weight_of(&weight, n + iq)) {
                a = order[lq];
                lq += 1;
            } else {
                a = n + iq;
                iq += 1;
            }
            let b;
            if lq < used && (iq >= created || weight_of(&weight, order[lq]) <= weight_of(&weight, n + iq)) {
                b = order[lq];
                lq += 1;
            } else {
                b = n + iq;
                iq += 1;
            }
            let wa = weight_of(&weight, a);
            let wb = weight_of(&weight, b);
            let sum = wa + wb;
            weight[n + created] = if sum > 1073741824 { 1073741824 } else { sum };
            left[created] = a;
            right[created] = b;
            created += 1;
            remaining -= 1;
        }
        // Depths from the root down: every inner node was created after its children.
        let mut k = created;
        while k > 0 {
            k -= 1;
            let d = depth[n + k];
            let child = if d < 1000 { d + 1 } else { 1000 };
            let l = left[k];
            let r = right[k];
            if l < n + k { depth[l] = child; }
            if r < n + k { depth[r] = child; }
        }
    }
    depth.resize(n, 0);
    depth
}

/// Code lengths of at most `limit` bits: the Huffman depths, with the frequencies halved and
/// the tree rebuilt while the longest code is too long. All zero if that never succeeds (the
/// usage check then rejects the code).
fn code_lengths(freq: &Vec<usize>, limit: usize) -> Vec<u8> {
    let n = freq.len();
    let mut f = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        f.push(freq[i]);
        i += 1;
    }
    let mut lens = zeros_u8(n);
    let mut attempts = 0;
    let mut done = false;
    while !done && attempts < 40 {
        let depth = tree_depths(&f);
        let mut longest = 0;
        i = 0;
        while i < n {
            if depth[i] > longest { longest = depth[i]; }
            i += 1;
        }
        if longest <= limit {
            i = 0;
            while i < n {
                lens[i] = depth[i] as u8;
                i += 1;
            }
            done = true;
        } else {
            i = 0;
            while i < n {
                let v = f[i];
                if v > 1 {
                    let half = v / 2 + v % 2;
                    f[i] = half;
                }
                i += 1;
            }
            attempts += 1;
        }
    }
    lens
}

/// Counts the symbols of each positive length in one pass, checking the length limit.
fn canonical_counts(lens: &Vec<u8>, limit: usize) -> (Vec<usize>, bool) {
    let mut count = zeros(limit + 2);
    let mut ok = true;
    let mut k = 0;
    while k < lens.len() {
        let x = lens[k] as usize;
        if 1 <= x && x <= limit {
            count[x] += 1;
        }
        if x > limit { ok = false; }
        k += 1;
    }
    (count, ok)
}

/// Canonical codewords from a length histogram: the next length's first word is twice the
/// sum of the preceding length's first word and symbol count. Checks the Kraft inequality and
/// that every word fits its length.
fn canonical(lens: &Vec<u8>, limit: usize) -> (Vec<usize>, bool) {
    let n = lens.len();
    let (freq, mut ok) = canonical_counts(lens, limit);
    let mut base = zeros(limit + 2);
    let mut l = 1;
    while l <= limit + 1 {
        let previous = l - 1;
        let c = 2 * (base[previous] + freq[previous]);
        base[l] = c;
        l += 1;
    }
    if base[limit + 1] > (1usize << (limit + 1)) { ok = false; }
    let mut count = zeros(limit + 2);
    let mut words = zeros(n);
    let mut sym = 0;
    while sym < n {
        let x = lens[sym] as usize;
        if 1 <= x && x <= limit {
            let w = base[x] + count[x];
            words[sym] = w;
            let e = count[x] + 1;
            count[x] = e;
            if w >= (1usize << x) { ok = false; }
        }
        sym += 1;
    }
    (words, ok)
}

/// A code from frequencies, trimmed to its last used symbol but to at least `least` symbols.
fn make_code(freq: &Vec<usize>, limit: usize, least: usize) -> (Code, bool) {
    let full = code_lengths(freq, limit);
    let mut n = full.len();
    while n > least && full[n - 1] == 0 {
        n -= 1;
    }
    let mut lens = Vec::with_capacity(n);
    let mut i = 0;
    while i < n && i < full.len() {
        lens.push(full[i]);
        i += 1;
    }
    let (words, ok) = canonical(&lens, limit);
    let mut rev = Vec::with_capacity(n);
    i = 0;
    while i < n && i < words.len() {
        let x = lens[i] as u32;
        let w = words[i];
        rev.push(if x <= 16 && w < 65536 { reverse_code(w as u32, x) } else { 0 });
        i += 1;
    }
    (Code { lens, words, rev }, ok)
}

/// Price and validate a body from its symbol counts instead of visiting every token again.
fn cost_histograms(lfreq: &Vec<usize>, dfreq: &Vec<usize>, lit: &Code, dist: &Code) -> (usize, usize, bool) {
    let mut cost = 0;
    let mut fixed_cost = 0;
    let mut ok = lfreq.len() == 286 && dfreq.len() == 30;
    let mut s = 0;
    while s < 286 && s < lfreq.len() {
        let count = lfreq[s];
        if count != 0 {
            let f = if count > 1048576 { 1048576 } else { count };
            if count > 1048576 { ok = false; }
            let x = if s < lit.lens.len() { lit.lens[s] as usize } else { 0 };
            if x == 0 { ok = false; }
            let extra = if s >= 257 { LENGTH_EXTRA[s - 257] as usize } else { 0 };
            let width = if s < 144 { 8 } else if s < 256 { 9 } else if s < 280 { 7 } else { 8 };
            let sum = cost + f * (x + extra);
            cost = if sum > 1073741824 { 1073741824 } else { sum };
            let fixed_sum = fixed_cost + f * (width + extra);
            fixed_cost = if fixed_sum > 1073741824 { 1073741824 } else { fixed_sum };
        }
        s += 1;
    }
    s = 0;
    while s < 30 && s < dfreq.len() {
        let count = dfreq[s];
        if count != 0 {
            let f = if count > 1048576 { 1048576 } else { count };
            if count > 1048576 { ok = false; }
            let x = if s < dist.lens.len() { dist.lens[s] as usize } else { 0 };
            if x == 0 { ok = false; }
            let extra = DIST_EXTRA[s] as usize;
            let sum = cost + f * (x + extra);
            cost = if sum > 1073741824 { 1073741824 } else { sum };
            let fixed_sum = fixed_cost + f * (5 + extra);
            fixed_cost = if fixed_sum > 1073741824 { 1073741824 } else { fixed_sum };
        }
        s += 1;
    }
    (cost, fixed_cost, ok)
}

/// The run-length coding of the code lengths (§3.2.7): a symbol below 16 is a length; 16
/// repeats the previous length 3–6 times; 17 and 18 stand for 3–10 and 11–138 zeros. Returns
/// the symbols and their extra values.
fn rle(all: &Vec<u8>) -> (Vec<usize>, Vec<usize>) {
    let n = all.len();
    let mut syms = Vec::with_capacity(n);
    let mut extras = Vec::with_capacity(n);
    let mut p = 0;
    while p < n {
        let v = all[p];
        let mut r = 1;
        while r < 138 && p + r < n && all[p + r] == v {
            r += 1;
        }
        if v == 0 {
            if r >= 11 {
                syms.push(18);
                extras.push(r - 11);
                p += r;
            } else if r >= 3 {
                syms.push(17);
                extras.push(r - 3);
                p += r;
            } else {
                syms.push(0);
                extras.push(0);
                p += 1;
            }
        } else {
            syms.push(v as usize);
            extras.push(0);
            p += 1;
            let mut rem = r - 1;
            while rem >= 3 {
                let c = if rem > 6 { 6 } else { rem };
                syms.push(16);
                extras.push(c - 3);
                p += c;
                rem -= c;
            }
        }
    }
    (syms, extras)
}

/// The cost in bits of the run-length coded lengths under the code-length code, and whether
/// every symbol used has a codeword.
fn header_cost(syms: &Vec<usize>, cl: &Code) -> (usize, bool) {
    let mut cost = 0;
    let mut ok = true;
    let mut i = 0;
    while i < syms.len() {
        let s = syms[i];
        if s < cl.lens.len() {
            let x = cl.lens[s] as usize;
            if x == 0 { ok = false; }
            let extra = if s == 16 { 2 } else if s == 17 { 3 } else if s == 18 { 7 } else { 0 };
            cost += x + extra;
        } else {
            ok = false;
        }
        i += 1;
    }
    (cost, ok)
}

/// Whether every code passed its checks and the counts fit the header fields.
fn checks(ok1: bool, ok2: bool, ok3: bool, ok4: bool, ok5: bool, nlit: usize, ndist: usize, ncl: usize) -> bool {
    ok1 && ok2 && ok3 && ok4 && ok5 && nlit <= 286 && ndist <= 30 && ncl == 19
}

/// The tables of a dynamic block: the two codes, the code-length code, the run-length coded
/// lengths and how many code-length lengths the header sends.
struct Tables {
    lit: Code,
    dist: Code,
    cl: Code,
    syms: Vec<usize>,
    extras: Vec<usize>,
    hclen: usize,
}

/// Builds the tables for a plan and prices the block as a dynamic block and as a fixed block;
/// `ok` is false if any code failed a check. The codes are fitted to `lcode` and `dcode` (the
/// symbol frequencies, or the smoothed ones of `smoothed`), the prices are the frequencies'.
fn build_tables(data: &[u8], start: usize, lengths: &Vec<u16>, distances: &Vec<u16>, lsym: &Vec<u8>, dsym: &Vec<u8>, lfreq: &Vec<usize>, dfreq: &Vec<usize>, lcode: &Vec<usize>, dcode: &Vec<usize>) -> (Tables, usize, usize, bool) {
    let (lit, ok1) = make_code(lcode, 15, 257);
    let (dist, ok2) = make_code(dcode, 15, 1);
    let (body, fixed_cost, ok3) = cost_histograms(lfreq, dfreq, &lit, &dist);
    let mut all = Vec::with_capacity(316);
    let mut i = 0;
    while i < lit.lens.len() {
        all.push(lit.lens[i]);
        i += 1;
    }
    i = 0;
    while i < dist.lens.len() {
        all.push(dist.lens[i]);
        i += 1;
    }
    let (syms, extras) = rle(&all);
    let mut cfreq = zeros(19);
    i = 0;
    while i < syms.len() {
        let s = syms[i];
        if s < 19 {
            let c = cfreq[s] + 1;
            cfreq[s] = c;
        }
        i += 1;
    }
    let (cl, ok4) = make_code(&cfreq, 7, 19);
    let mut hclen = 19;
    while hclen > 4 && cl.lens[CL_ORDER[hclen - 1]] == 0 {
        hclen -= 1;
    }
    let (header, ok5) = header_cost(&syms, &cl);
    let ok = checks(ok1, ok2, ok3, ok4, ok5, lit.lens.len(), dist.lens.len(), cl.lens.len());
    let cost = 17 + 3 * hclen + header + body;
    (Tables { lit, dist, cl, syms, extras, hclen }, cost, fixed_cost, ok)
}

/// The extra bits of a run-length symbol: 2 for 16, 3 for 17, 7 for 18, none otherwise.
fn item_extra(writer: &mut Writer, s: usize, e: u32) {
    if s == 16 {
        writer.bits(e, 2);
    } else if s == 17 {
        writer.bits(e, 3);
    } else if s == 18 {
        writer.bits(e, 7);
    }
}

/// Writes a dynamic block: the header, the code-length lengths in CL_ORDER, the run-length
/// coded lengths, then the plan's symbols and the end-of-block symbol.
fn dynamic(writer: &mut Writer, data: &[u8], start: usize, lengths: &Vec<u16>, distances: &Vec<u16>, lsym: &Vec<u8>, dsym: &Vec<u8>, tables: &Tables, final_block: bool) {
    let header = if final_block { 5 } else { 4 };
    writer.bits(header, 3);
    writer.bits((tables.lit.lens.len() - 257) as u32, 5);
    writer.bits((tables.dist.lens.len() - 1) as u32, 5);
    writer.bits((tables.hclen - 4) as u32, 4);
    let mut k = 0;
    while k < tables.hclen {
        writer.bits(tables.cl.lens[CL_ORDER[k]] as u32, 3);
        k += 1;
    }
    let mut i = 0;
    while i < tables.syms.len() {
        let s = tables.syms[i];
        let e = tables.extras[i] as u32;
        writer.bits(tables.cl.rev[s], tables.cl.lens[s] as u32);
        item_extra(writer, s, e);
        i += 1;
    }
    let mut p = start;
    let mut t = 0;
    while t < lengths.len() {
        let len = lengths[t] as usize;
        let dist = distances[t] as usize;
        if dist == 0 {
            let s = data[p] as usize;
            writer.bits(tables.lit.rev[s], tables.lit.lens[s] as u32);
        } else {
            let l = lsym[t] as usize;
            let d = dsym[t] as usize;
            let first_value = tables.lit.rev[257 + l];
            let first_count = tables.lit.lens[257 + l] as u32;
            let first_extra = (len - LENGTH_BASE[l]) as u32;
            let first_extra_count = LENGTH_EXTRA[l];
            let first = first_value | (first_extra << first_count);
            let first_count = first_count + first_extra_count;
            let second_value = tables.dist.rev[d];
            let second_count = tables.dist.lens[d] as u32;
            let second_extra = (dist - DIST_BASE[d]) as u32;
            let second_extra_count = DIST_EXTRA[d];
            let second = second_value | (second_extra << second_count);
            let second_count = second_count + second_extra_count;
            writer.pair(first, first_count, second, second_count);
        }
        p += len;
        t += 1;
    }
    writer.bits(tables.lit.rev[256], tables.lit.lens[256] as u32);
}

/// Stores large spans with almost entirely literal plans directly; otherwise writes the
/// cheapest of the three block types (stored output only for a span that fits its length).
fn block1(writer: &mut Writer, data: &[u8], start: usize, end: usize, parsed: &Parsed, final_block: bool, smooth: bool) {
    let span = end - start;
    // Avoid symbol arrays, repeated plan scans and Huffman fitting for spans whose plans
    // contain fewer than one percent copies.
    if span <= 32768 && span >= 4096 && parsed.plan.lengths.len() > span - span / 100 {
        stored(writer, data, start, end, final_block);
        return;
    }
    let stored_cost = (((8 - ((writer.count + 3) & 7)) & 7) + 35) as usize + span * 8;
    let stored_ok = span <= 32768;
    if parsed.fused {
        block2(writer, data, start, end, &parsed.plan, &parsed.lsym, &parsed.dsym, &parsed.lfreq, &parsed.dfreq, final_block, stored_cost, stored_ok, smooth);
    } else {
        let (lsym, dsym, lfreq, dfreq) = symbols_histogram(data, start, &parsed.plan.lengths, &parsed.plan.distances);
        block2(writer, data, start, end, &parsed.plan, &lsym, &dsym, &lfreq, &dfreq, final_block, stored_cost, stored_ok, smooth);
    }
}

/// The tables of a block fitted to its frequencies, or when `smooth` also to the smoothed
/// frequencies (`smoothed`), whichever prices the block lower.
fn fit_tables(data: &[u8], start: usize, lengths: &Vec<u16>, distances: &Vec<u16>, lsym: &Vec<u8>, dsym: &Vec<u8>, lfreq: &Vec<usize>, dfreq: &Vec<usize>, smooth: bool) -> (Tables, usize, usize, bool) {
    let (tables, cost, fixed_cost, ok) = build_tables(data, start, lengths, distances, lsym, dsym, lfreq, dfreq, lfreq, dfreq);
    if smooth {
        let lcode = smoothed(lfreq);
        let dcode = smoothed(dfreq);
        let (tables1, cost1, fixed_cost1, ok1) = build_tables(data, start, lengths, distances, lsym, dsym, lfreq, dfreq, &lcode, &dcode);
        if ok1 && (!ok || cost1 < cost) {
            return (tables1, cost1, fixed_cost1, ok1);
        }
    }
    (tables, cost, fixed_cost, ok)
}

/// Writes the cheapest of the three block types for a plan whose symbol indices and
/// frequencies are known.
fn block2(writer: &mut Writer, data: &[u8], start: usize, end: usize, plan: &Plan, lsym: &Vec<u8>, dsym: &Vec<u8>, lfreq: &Vec<usize>, dfreq: &Vec<usize>, final_block: bool, stored_cost: usize, stored_ok: bool, smooth: bool) {
    let (tables, dynamic_cost, fixed_cost, ok) = fit_tables(data, start, &plan.lengths, &plan.distances, lsym, dsym, lfreq, dfreq, smooth);
    if ok && dynamic_cost < fixed_cost && dynamic_cost < stored_cost {
        dynamic(writer, data, start, &plan.lengths, &plan.distances, lsym, dsym, &tables, final_block);
    } else if stored_ok && stored_cost < fixed_cost {
        stored(writer, data, start, end, final_block);
    } else {
        fixed(writer, data, start, &plan.lengths, &plan.distances, final_block);
    }
}


// ================================================================ smoothed frequencies

/// Whether a run of `stride` equal frequencies of value `symbol` is already cheap to send as
/// one run of code lengths: five zeros, or seven of another value.
fn long_run(symbol: usize, stride: usize) -> bool {
    if symbol == 0 { stride >= 5 } else { stride >= 7 }
}

/// Whether a stretch of `stride` frequencies summing to `sum` gets one common value.
fn collapsing(stride: usize, sum: usize) -> bool {
    if stride >= 4 { true } else { stride >= 3 && sum == 0 }
}

/// Whether the run of equal frequencies `symbol` followed ends at `i` (before `length`, the
/// end of the frequencies looked at).
fn run_ends(c: &Vec<usize>, i: usize, length: usize, symbol: usize) -> bool {
    if i < length && i < c.len() { c[i] != symbol } else { true }
}

/// Whether the stretch of similar frequencies followed ends at `i`: at a frequency in a run
/// already cheap to send (`good`), at one 4 or more away from the stretch's `limit`, or at
/// `length`.
fn stretch_ends(c: &Vec<usize>, good: &Vec<bool>, i: usize, length: usize, limit: usize) -> bool {
    if i < length && i < c.len() && i < good.len() {
        if good[i] {
            true
        } else {
            let x = c[i];
            let diff = if x > limit { x - limit } else { limit - x };
            diff >= 4
        }
    } else {
        true
    }
}

/// Frequencies (each capped at 2^20) whose code lengths run-length code better (zopfli's
/// heuristic): the runs already cheap to send are kept; every other stretch of at least four
/// similar frequencies (three zeros) takes their rounded mean, at least 1 unless all are zero,
/// so that every used symbol keeps a codeword. The trailing zeros are kept.
fn smoothed(freq: &Vec<usize>) -> Vec<usize> {
    let n = freq.len();
    let mut c = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        let v = freq[i];
        c.push(if v > 1048576 { 1048576 } else { v });
        i += 1;
    }
    let mut length = n;
    while length > 0 && c[length - 1] == 0 {
        length -= 1;
    }
    if length == 0 || length > 1024 {
        return c;
    }
    // The frequencies in runs already cheap to send.
    let mut good: Vec<bool> = Vec::new();
    good.resize(length, false);
    let mut symbol = capped_at(&c, 0);
    let mut stride = 0;
    i = 0;
    while i <= length {
        if run_ends(&c, i, length, symbol) {
            if long_run(symbol, stride) {
                good = mark_good(good, i, stride);
            }
            stride = 1;
            if i < length {
                symbol = capped_at(&c, i);
            }
        } else {
            stride += 1;
        }
        i += 1;
    }
    // Collapse the stretches between them.
    stride = 0;
    let mut limit = capped_at(&c, 0);
    let mut sum = 0;
    i = 0;
    while i <= length {
        if stretch_ends(&c, &good, i, length, limit) {
            if collapsing(stride, sum) {
                let mean = if stride > 0 { (sum + stride / 2) / stride } else { 0 };
                let value = if sum == 0 { 0 } else if mean < 1 { 1 } else { mean };
                c = fill_stretch(c, i, stride, value);
            }
            stride = 0;
            sum = 0;
            if i + 3 < length {
                limit = (capped_at(&c, i) + capped_at(&c, i + 1) + capped_at(&c, i + 2) + capped_at(&c, i + 3) + 2) / 4;
            } else if i < length {
                limit = capped_at(&c, i);
            } else {
                limit = 0;
            }
        }
        stride += 1;
        if i < length {
            sum += capped_at(&c, i);
        }
        i += 1;
    }
    c
}

/// The frequency at `i` capped at 2^20 (0 beyond the end).
fn capped_at(c: &Vec<usize>, i: usize) -> usize {
    if i < c.len() {
        let v = c[i];
        if v > 1048576 { 1048576 } else { v }
    } else {
        0
    }
}

/// Marks the `stride` entries before `i` as in a run already cheap to send.
fn mark_good(good: Vec<bool>, i: usize, stride: usize) -> Vec<bool> {
    let mut out = good;
    let mut k = 0;
    while k < stride && k < i {
        let j = i - k - 1;
        if j < out.len() {
            out[j] = true;
        }
        k += 1;
    }
    out
}

/// Sets the `stride` frequencies before `i` to `value`.
fn fill_stretch(c: Vec<usize>, i: usize, stride: usize, value: usize) -> Vec<usize> {
    let mut out = c;
    let mut k = 0;
    while k < stride && k < i {
        let j = i - k - 1;
        if j < out.len() {
            out[j] = value;
        }
        k += 1;
    }
    out
}

// ================================================================ splitting the first block

/// A count plus one, saturating far below the scalar's range.
fn count_up(x: usize) -> usize {
    if x < 1073741824 { x + 1 } else { x }
}

/// Copies the frequencies (286 literal/length, then 30 distance entries) into slot `j` of the
/// table of candidate cuts (316 entries per slot).
fn snapshot(snap: Vec<usize>, j: usize, lit: &Vec<usize>, dist: &Vec<usize>) -> Vec<usize> {
    let mut out = snap;
    let base = j * 316;
    let mut s = 0;
    while s < 286 && s < lit.len() && base + s < out.len() {
        out[base + s] = lit[s];
        s += 1;
    }
    s = 0;
    while s < 30 && s < dist.len() && base + 286 + s < out.len() {
        out[base + 286 + s] = dist[s];
        s += 1;
    }
    out
}

/// Counts a token's symbols (saturating): the literal at `p`, or the length and distance codes
/// of a copy.
fn count_token(data: &[u8], p: usize, len: usize, dd: usize, lit: &mut Vec<usize>, dist: &mut Vec<usize>) {
    if dd == 0 {
        if p < data.len() {
            let s = data[p] as usize;
            let c = count_up(lit[s]);
            lit[s] = c;
        }
    } else {
        let l = length_code(len);
        let d = distance_code(dd);
        if l < 29 && d < 30 {
            let c = count_up(lit[257 + l]);
            lit[257 + l] = c;
            let e = count_up(dist[d]);
            dist[d] = e;
        }
    }
}

/// The candidate cuts of a block's plan: for each of the byte offsets 1024 * (j + 1) (j < 31)
/// from the start, the symbol frequencies of the tokens before it (316 entries per candidate,
/// as `snapshot` lays them out) and the index of the first token at or beyond it; then the
/// frequencies of the whole plan (with the end-of-block symbol).
fn prefix_histograms(data: &[u8], start: usize, lengths: &Vec<u16>, distances: &Vec<u16>) -> (Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>) {
    let mut lit = zeros(286);
    let mut dist = zeros(30);
    let mut snap = zeros(31 * 316);
    let mut cut = zeros(31);
    let mut j = 0;
    let mut p = start;
    let mut t = 0;
    while t < lengths.len() && t < distances.len() {
        while j < 31 && p >= start + 1024 * (j + 1) {
            snap = snapshot(snap, j, &lit, &dist);
            cut[j] = t;
            j += 1;
        }
        let len = lengths[t] as usize;
        let dd = distances[t] as usize;
        count_token(data, p, len, dd, &mut lit, &mut dist);
        if len <= 1073741824 && p <= 1073741824 {
            p += len;
        }
        t += 1;
    }
    while j < 31 {
        snap = snapshot(snap, j, &lit, &dist);
        cut[j] = t;
        j += 1;
    }
    let c = count_up(lit[256]);
    lit[256] = c;
    (snap, cut, lit, dist)
}

/// The estimated bits of writing the tokens before candidate `j` and the rest as two dynamic
/// blocks, each with its own end-of-block symbol.
fn cut_cost(snap: &Vec<usize>, j: usize, lfreq: &Vec<usize>, dfreq: &Vec<usize>) -> usize {
    let base = j * 316;
    let mut la = Vec::with_capacity(286);
    let mut lb = Vec::with_capacity(286);
    let mut s = 0;
    while s < 286 {
        let x = if base + s < snap.len() { snap[base + s] } else { 0 };
        let y = if s < lfreq.len() { lfreq[s] } else { 0 };
        la.push(if s == 256 { count_up(x) } else { x });
        lb.push(if y > x { y - x } else { 0 });
        s += 1;
    }
    let mut da = Vec::with_capacity(30);
    let mut db = Vec::with_capacity(30);
    s = 0;
    while s < 30 {
        let x = if base + 286 + s < snap.len() { snap[base + 286 + s] } else { 0 };
        let y = if s < dfreq.len() { dfreq[s] } else { 0 };
        da.push(x);
        db.push(if y > x { y - x } else { 0 });
        s += 1;
    }
    hist_cost(&la, &da) + hist_cost(&lb, &db)
}

/// The number of tokens before the cheapest cut of a block's plan (0 for none): the first
/// block of a file starts with a cold window, and the tokens before its history fills often
/// fit a code of their own. The candidates on a grid of 4 KB are priced, then the ones within
/// 2 KB of the best.
fn split_point(data: &[u8], start: usize, lengths: &Vec<u16>, distances: &Vec<u16>) -> usize {
    let (snap, cut, lfreq, dfreq) = prefix_histograms(data, start, lengths, distances);
    let whole = hist_cost(&lfreq, &dfreq);
    let mut best = if whole > 64 { whole - 64 } else { 0 };
    let mut bestj = 31;
    let mut j = 3;
    while j < 31 {
        let c = cut_cost(&snap, j, &lfreq, &dfreq);
        if c < best {
            best = c;
            bestj = j;
        }
        j += 4;
    }
    if bestj < 31 {
        let center = bestj;
        j = if center >= 1 { center - 1 } else { 0 };
        while j <= center + 1 && j < 31 {
            if j != center {
                let c = cut_cost(&snap, j, &lfreq, &dfreq);
                if c < best {
                    best = c;
                    bestj = j;
                }
            }
            j += 1;
        }
    }
    if bestj < 31 { cut[bestj] } else { 0 }
}

/// The plan's first `k` tokens and the rest, with the position where the first part ends
/// (the start plus the lengths of the first `k` tokens).
fn split_plan(plan: &Plan, k: usize, start: usize) -> (Plan, Plan, usize) {
    let mut a = Plan { lengths: Vec::new(), distances: Vec::new() };
    let mut b = Plan { lengths: Vec::new(), distances: Vec::new() };
    let mut mid = start;
    let mut t = 0;
    while t < k && t < plan.lengths.len() && t < plan.distances.len() {
        let len = plan.lengths[t];
        a.lengths.push(len);
        a.distances.push(plan.distances[t]);
        mid += len as usize;
        t += 1;
    }
    while t < plan.lengths.len() && t < plan.distances.len() {
        b.lengths.push(plan.lengths[t]);
        b.distances.push(plan.distances[t]);
        t += 1;
    }
    (a, b, mid)
}

/// Whether a block starting at `start` may be cut: the first block of a file, at level 10 every
/// block.
fn cut_candidate(start: usize, level: u8) -> bool {
    if start == 0 { true } else { level >= 10 }
}

/// How many tokens come before the cut of a block (0 for none): at the dense levels, the first
/// block of a file (at level 10 every block) of at least 8 KB whose plan is not almost all
/// literals (those are left to `block1`'s stored shortcut) is cut where `split_point` says.
fn split_choice(data: &[u8], start: usize, span: usize, plan: &Plan, level: u8) -> usize {
    if level >= 9 && cut_candidate(start, level) && span >= 8192 && plan.lengths.len() <= span - span / 100 {
        split_point(data, start, &plan.lengths, &plan.distances)
    } else {
        0
    }
}

/// Writes a block, at the dense levels as two blocks when the first block of a file is
/// cheaper cut in two (`split_choice`).
fn block(writer: &mut Writer, data: &[u8], start: usize, end: usize, parsed: &Parsed, final_block: bool, level: u8) {
    let span = end - start;
    let smooth = level >= 10;
    let k = split_choice(data, start, span, &parsed.plan, level);
    if k > 0 && k < parsed.plan.lengths.len() && parsed.plan.lengths.len() == parsed.plan.distances.len() {
        let (a, b, mid) = split_plan(&parsed.plan, k, start);
        if start < mid && mid < end {
            block1(writer, data, start, mid, &unfused(a), false, smooth);
            block1(writer, data, mid, end, &unfused(b), final_block, smooth);
        } else {
            block1(writer, data, start, end, parsed, final_block, smooth);
        }
    } else {
        block1(writer, data, start, end, parsed, final_block, smooth);
    }
}

// ================================================================ block merging

/// A block not yet written: the plan of the chunks parsed since `start`, their symbol
/// frequencies and the estimated bits of writing them as one block (the frequencies and the
/// estimate are kept only at the levels that merge blocks).
struct Pending {
    start: usize,
    parsed: Parsed,
    cost: usize,
}

/// An empty pending block starting at `start`.
fn no_pending(start: usize) -> Pending {
    Pending { start, parsed: unfused(Plan { lengths: Vec::new(), distances: Vec::new() }), cost: 0 }
}

/// The sum of two frequency tables, entry by entry over the first one's length, saturating.
fn add_hist(a: &Vec<usize>, b: &Vec<usize>) -> Vec<usize> {
    let mut v = Vec::with_capacity(a.len());
    let mut i = 0;
    while i < a.len() {
        let x = a[i];
        let y = if i < b.len() { b[i] } else { 0 };
        let xc = if x > 1073741824 { 1073741824 } else { x };
        let yc = if y > 1073741824 { 1073741824 } else { y };
        let s = xc + yc;
        v.push(s);
        i += 1;
    }
    v
}

/// The bits of the symbols of one code: each frequency times the codeword length (15 for a
/// symbol without one) plus the extra bits of a length symbol (from 257 on) or, when `dist`,
/// of a distance symbol; saturating at 2^30.
fn weighted_bits(freq: &Vec<usize>, lens: &Vec<u8>, dist: bool) -> usize {
    let mut total = 0;
    let mut s = 0;
    while s < freq.len() && s < lens.len() {
        let f = freq[s];
        if f > 0 {
            let l = lens[s] as usize;
            let code = if l == 0 { 15 } else { l };
            let extra = if dist {
                if s < 30 { DIST_EXTRA[s] as usize } else { 0 }
            } else if s >= 257 && s < 286 {
                LENGTH_EXTRA[s - 257] as usize
            } else {
                0
            };
            let fc = if f > 1048576 { 1048576 } else { f };
            let add = fc * (code + extra);
            let sum = total + add;
            total = if sum > 1073741824 { 1073741824 } else { sum };
        }
        s += 1;
    }
    total
}

/// The estimated bits of a dynamic block with these symbol frequencies: the header with its
/// run-length coded lengths under their own code, then the body under length-limited Huffman
/// codes of the frequencies; 2^30 unless the tables have the histogram's shape.
fn hist_cost(lfreq: &Vec<usize>, dfreq: &Vec<usize>) -> usize {
    if lfreq.len() == 286 && dfreq.len() == 30 {
        let llens = code_lengths(lfreq, 15);
        let dlens = code_lengths(dfreq, 15);
        let body = weighted_bits(lfreq, &llens, false) + weighted_bits(dfreq, &dlens, true);
        let mut all = Vec::with_capacity(316);
        let mut i = 0;
        while i < llens.len() {
            all.push(llens[i]);
            i += 1;
        }
        i = 0;
        while i < dlens.len() {
            all.push(dlens[i]);
            i += 1;
        }
        let (syms, _) = rle(&all);
        let mut cfreq = zeros(19);
        i = 0;
        while i < syms.len() {
            let s = syms[i];
            if s < 19 {
                let c = cfreq[s] + 1;
                cfreq[s] = c;
            }
            i += 1;
        }
        let cl = Code { lens: code_lengths(&cfreq, 7), words: Vec::new(), rev: Vec::new() };
        let (header, _) = header_cost(&syms, &cl);
        let total = 74 + header + body;
        if total > 1073741824 { 1073741824 } else { total }
    } else {
        1073741824
    }
}

/// The frequencies of a chunk's plan and the estimated bits of writing it alone: as a dynamic
/// block, or stored if that is cheaper.
fn plan_cost(data: &[u8], start: usize, end: usize, plan: &Plan) -> (Vec<usize>, Vec<usize>, usize) {
    let (lfreq, dfreq) = plan_histogram(data, start, &plan.lengths, &plan.distances);
    let dynamic_bits = hist_cost(&lfreq, &dfreq);
    let span = end - start;
    let stored_bits = if span <= 32768 { 40 + 8 * span } else { 1073741824 };
    let cost = if stored_bits < dynamic_bits { stored_bits } else { dynamic_bits };
    (lfreq, dfreq, cost)
}

/// The chunk's parse with its frequencies and cost at the levels that merge blocks (which
/// count them here, the frequencies replacing whatever the parse brought); as it is, at cost
/// 0, below them.
fn costs_at(data: &[u8], start: usize, end: usize, level: u8, parsed: Parsed) -> (Parsed, usize) {
    if level >= 9 {
        let (lfreq, dfreq, cost) = plan_cost(data, start, end, &parsed.plan);
        (Parsed { plan: parsed.plan, lsym: Vec::new(), dsym: Vec::new(), lfreq, dfreq, fused: false }, cost)
    } else {
        (parsed, 0)
    }
}

/// The frequencies and estimated cost of the pending block and the chunk written as one block,
/// at the levels that merge blocks; nothing below them.
fn merged_costs(level: u8, lf0: &Vec<usize>, df0: &Vec<usize>, lf1: &Vec<usize>, df1: &Vec<usize>) -> (Vec<usize>, Vec<usize>, usize) {
    if level >= 9 {
        let lf2 = add_hist(lf0, lf1);
        let df2 = add_hist(df0, df1);
        let c2 = hist_cost(&lf2, &df2);
        (lf2, df2, c2)
    } else {
        (Vec::new(), Vec::new(), 0)
    }
}

/// Whether the chunk just parsed joins the pending block: at the dense levels, when the
/// estimate says one block (`c2`) is smaller than two (`c0` and `c1`) and the result stays
/// within a million bytes.
fn merge_decision(level: u8, pstart: usize, start: usize, end: usize, c0: usize, c1: usize, c2: usize) -> bool {
    let a = if c0 > 1073741824 { 1073741824 } else { c0 };
    let b = if c1 > 1073741824 { 1073741824 } else { c1 };
    level >= 9 && start > 0 && end - pstart <= 1048576 && c2 < a + b
}

/// The plan followed by another.
fn append_plan(plan: Plan, more: &Plan) -> Plan {
    let mut out = plan;
    out.lengths.extend_from_slice(&more.lengths);
    out.distances.extend_from_slice(&more.distances);
    out
}

/// Whether a chunk ending at `end` is written at once: at a level that never merges, when it
/// is not the last chunk and nothing is pending (the pending block starts at `start`).
fn flush_now(level: u8, end: usize, len: usize, pstart: usize, start: usize) -> bool {
    level < 9 && end < len && pstart == start
}

/// One chunk: parses it, then either joins it to the pending block or writes the pending block
/// (if there is one) and starts a new one with it. At the levels that never merge, a chunk
/// that is not the last is written at once instead, while its plan is still in cache, and
/// nothing is left pending (the pending block is then empty: its start is `start`). Returns
/// the prices for the next chunk and the pending block.
fn chunk(data: &[u8], start: usize, end: usize, level: u8, writer: &mut Writer, head: &mut Vec<u32>, chain: &mut Vec<u32>, lcost: Vec<u32>, dcost: Vec<u32>, pending: Pending) -> (Vec<u32>, Vec<u32>, Pending) {
    let (parsed, lcost1, dcost1) = parse(data, start, end, level, head, chain, lcost, dcost);
    if flush_now(level, end, data.len(), pending.start, start) {
        block(writer, data, start, end, &parsed, false, level);
        return (lcost1, dcost1, no_pending(end));
    }
    let (parsed1, cost1) = costs_at(data, start, end, level, parsed);
    let (lfreq2, dfreq2, cost2) = merged_costs(level, &pending.parsed.lfreq, &pending.parsed.dfreq, &parsed1.lfreq, &parsed1.dfreq);
    if merge_decision(level, pending.start, start, end, pending.cost, cost1, cost2) {
        let merged = append_plan(pending.parsed.plan, &parsed1.plan);
        (lcost1, dcost1, Pending { start: pending.start, parsed: Parsed { plan: merged, lsym: Vec::new(), dsym: Vec::new(), lfreq: lfreq2, dfreq: dfreq2, fused: false }, cost: cost2 })
    } else if pending.start < start {
        block(writer, data, pending.start, start, &pending.parsed, false, level);
        (lcost1, dcost1, Pending { start, parsed: parsed1, cost: cost1 })
    } else {
        (lcost1, dcost1, Pending { start, parsed: parsed1, cost: cost1 })
    }
}

/// The plan of a block at a level above 0, with the prices for the next block. Levels 8 and 9
/// are cheap optimal parses (one or two passes); level 10 walks deeper and refits the prices
/// up to five times, as long as they still move; the levels below are greedy and leave the
/// prices as they are. Level 8 and the
/// greedy levels above 1 key their candidates by five bytes (shorter chains and walks, and at
/// the greedy levels smaller output too); level 1 (where the longer hash costs time), and the
/// two densest levels (where the copies of four bytes count) by four.
fn parse(data: &[u8], start: usize, end: usize, level: u8, head: &mut Vec<u32>, chain: &mut Vec<u32>, lcost: Vec<u32>, dcost: Vec<u32>) -> (Parsed, Vec<u32>, Vec<u32>) {
    // Sampling a literal-only chunk avoids constructing symbol arrays and histograms that
    // the stored-block path would immediately discard.
    let literal_only = level == 1 && incompressible(data, start, end);
    if literal_only {
        return (unfused(literal_plan(end - start)), lcost, dcost);
    }
    if level >= 8 {
        let (plan, lcost1, dcost1) = if level >= 10 {
            optimal_passes(data, start, end, head, chain, 6, 40, lcost, dcost, true, true)
        } else if level == 9 {
            optimal_passes(data, start, end, head, chain, 2, 32, lcost, dcost, true, false)
        } else {
            optimal_passes(data, start, end, head, chain, 1, 32, lcost, dcost, true, false)
        };
        (unfused(plan), lcost1, dcost1)
    } else {
        (greedy(data, start, end, level, head, chain, level > 1), lcost, dcost)
    }
}

pub fn compress(data: &[u8], level: u8) -> Vec<u8> {
    let xfl = if level == 0 { 0 } else if level < 5 { 4 } else { 2 };
    // Reserve room for the input and stored-block framing before emitting any bytes, and at
    // least 4 MiB: an output buffer that large comes from mmap the first time, and releasing it
    // raises the allocator's trim threshold, so that the tables of later calls (a megabyte at
    // the optimal levels) are reused from the heap instead of being returned to the system and
    // faulted in again on every call (170 µs per call at level 8). Untouched capacity costs no
    // memory.
    let need = data.len() + (data.len() / 32768) * 5 + 32;
    let mut writer = Writer { out: Vec::with_capacity(if need < 4194304 { 4194304 } else { need }), bits: 0u64, count: 0 };
    writer.out.push(31);
    writer.out.push(139);
    writer.out.push(8);
    writer.out.push(0);
    writer.out.push(0);
    writer.out.push(0);
    writer.out.push(0);
    writer.out.push(0);
    writer.out.push(xfl);
    writer.out.push(255);
    // The hash chains use the first half of `chain`; the optimal levels use two links per
    // position. Four-byte heads and links halve the tables and fit every position of a specified input.
    // Level 1 follows no links: it gets no chain table (zeroing its 256 KB cost 1% per call).
    let mut head = zeros_u32(if level == 1 { 16384 } else if level >= 9 { 65536 } else { 32768 });
    let mut chain = zeros_u32(if level == 1 { 0 } else { 65536 });
    // The prices of the optimal parse: each block's final codes price the next block.
    let mut lcost = zeros_u32(545);
    let mut dcost = zeros_u32(30);
    // The chunks of 32 KB are parsed one at a time; the block not yet written collects the
    // chunks since its start (one, unless the level merges blocks), and the last one is final.
    let mut pending = no_pending(0);
    let mut start = 0;
    let mut done = false;
    while !done {
        let span = if data.len() - start < 32768 { data.len() - start } else { 32768 };
        let end = start + span;
        done = end == data.len();
        let (lcost1, dcost1, pending1) = chunk(data, start, end, level, &mut writer, &mut head, &mut chain, lcost, dcost, pending);
        lcost = lcost1;
        dcost = dcost1;
        pending = pending1;
        start = end;
    }
    block(&mut writer, data, pending.start, data.len(), &pending.parsed, true, level);
    writer.align();
    let crc = crc32(data);
    writer.bits(crc & 65535, 16);
    writer.bits(crc >> 16, 16);
    let size = data.len() as u32;
    writer.bits(size & 65535, 16);
    writer.bits(size >> 16, 16);
    writer.out
}


// ======================================================================== decompress
//
// The decoder, optimised separately in `example/gzip-decompress` and merged here. It keeps its own
// CRC-32 (`crc32_wide`, slicing by 16 with a compile-time table), which is faster than the
// compressor's; both are proved equal to `crc32_spec`.

macro_rules! require { ($value:expr) => { match $value { Some(value) => value, None => return None } }; }

// Eight shift-and-xor steps of the CRC register.
const fn crc_byte(c: u32) -> u32 {
    let mut c = c;
    let mut n = 0;
    while n < 8 {
        if c % 2 == 1 {
            c = (c / 2) ^ 0xedb8_8320;
        } else {
            c /= 2;
        }
        n += 1;
    }
    c
}

// Entry 256 * j + k is the register 8 * (j + 1) steps after k.
const fn crc_table() -> [u32; 4096] {
    let mut t = [0u32; 4096];
    let mut k = 0usize;
    while k < 256 {
        t[k] = crc_byte(k as u32);
        k += 1;
    }
    while k < 4096 {
        t[k] = crc_byte(t[k - 256]);
        k += 1;
    }
    t
}

// The four bytes from i as a little-endian word.
#[inline(always)]
fn word_at(data: &[u8], i: usize) -> u32 {
    data[i] as u32 + 256 * (data[i + 1] as u32) + 65536 * (data[i + 2] as u32) + 16777216 * (data[i + 3] as u32)
}

// The register 32 * (m + 1) steps after w: the xor of the table entries of its four bytes.
#[inline(always)]
fn crc_word(t: &[u32; 4096], w: u32, m: usize) -> u32 {
    t[1024 * m + 768 + (w % 256) as usize] ^ t[1024 * m + 512 + ((w / 256) % 256) as usize]
        ^ t[1024 * m + 256 + ((w / 65536) % 256) as usize] ^ t[1024 * m + (w / 16777216) as usize]
}

// Sixteen bytes at a time: xoring a little-endian word into the register and taking 32 steps is
// the same as four byte steps, and the steps are linear over xor, so the four words of a chunk
// go through 128, 96, 64 and 32 steps independently of each other.
//
// The part of a chunk's step that does not depend on the register (its three upper words) is
// computed one chunk ahead, so that the register's dependency chain per chunk is only the xor
// with the chunk's first word, four table lookups and the xor with that precomputed part;
// written as one expression the compiler chains all sixteen lookups behind the register.
#[inline(always)]
fn crc_rest_wide(t: &[u32; 4096], b: &[u8]) -> u32 {
    crc_word(t, word_at(b, 4), 2) ^ crc_word(t, word_at(b, 8), 1) ^ crc_word(t, word_at(b, 12), 0)
}

// The table, computed once when the program is compiled.
const CRC_TABLE: [u32; 4096] = crc_table();

fn crc32_wide(data: &[u8]) -> u32 {
    let t: &[u32; 4096] = &CRC_TABLE;
    let mut c = 0xffff_ffffu32;
    let mut i = 0;
    if data.len() >= 16 {
        let b0 = &data[0..16];
        let mut rest = crc_rest_wide(t, b0);
        let mut w0 = word_at(b0, 0);
        while data.len() - i >= 32 {
            let b = &data[i + 16..i + 32];
            let rest_next = crc_rest_wide(t, b);
            let w_next = word_at(b, 0);
            c = crc_word(t, c ^ w0, 3) ^ rest;
            rest = rest_next;
            w0 = w_next;
            i += 16;
        }
        c = crc_word(t, c ^ w0, 3) ^ rest;
        i += 16;
    }
    while i < data.len() {
        c = crc_byte(c ^ data[i] as u32);
        i += 1;
    }
    c ^ 0xffff_ffff
}

const fn length_extra(k: u32) -> u32 {
    if k < 8 || k == 28 { 0 } else { k / 4 - 1 }
}

const fn distance_extra(k: u32) -> u32 {
    if k < 4 { 0 } else { k / 2 - 1 }
}

const fn length_base(k: u32) -> u32 {
    let bases = [3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258];
    bases[k as usize]
}

const fn distance_base(k: u32) -> u32 {
    let bases = [1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577];
    bases[k as usize]
}

struct Reader { byte: usize, bit: u32 }

fn read_bit(s: &[u8], r: &mut Reader) -> Option<u32> {
    if r.byte >= s.len() { return None; }
    let b = ((s[r.byte] as u32) >> r.bit) % 2;
    r.bit += 1;
    if r.bit == 8 { r.bit = 0; r.byte += 1; }
    Some(b)
}

fn read_field(s: &[u8], r: &mut Reader, count: u32) -> Option<u32> {
    if count == 0 { return Some(0); }
    let b = require!(read_bit(s, r));
    let rest = require!(read_field(s, r, count - 1));
    Some(b + 2 * rest)
}

fn read_u16(s: &[u8], p: usize) -> Option<u32> {
    if p > s.len() || s.len() - p < 2 { return None; }
    Some(s[p] as u32 + 256 * s[p + 1] as u32)
}

fn read_u32(s: &[u8], p: usize) -> Option<u32> {
    if p > s.len() || s.len() - p < 4 { return None; }
    Some(s[p] as u32 + 256 * s[p + 1] as u32 + 65536 * s[p + 2] as u32 + 16777216 * s[p + 3] as u32)
}

fn skip_zero(s: &[u8], p: usize) -> Option<usize> {
    let mut q = p;
    while q < s.len() && s[q] != 0 { q += 1; }
    if q < s.len() { Some(q + 1) } else { None }
}

fn header_extra(s: &[u8], present: bool) -> Option<usize> {
    if !present { return Some(10); }
    let n = require!(read_u16(s, 10)) as usize;
    if n > s.len() - 12 { return None; }
    Some(12 + n)
}

fn header_zero(s: &[u8], p: usize, present: bool) -> Option<usize> {
    if present { skip_zero(s, p) } else { Some(p) }
}

fn header_crc(s: &[u8], p: usize, present: bool) -> Option<usize> {
    if !present { return Some(p); }
    if s.len() - p < 2 { return None; }
    Some(p + 2)
}

fn read_header(s: &[u8]) -> Option<usize> {
    if s.len() < 10 { return None; }
    if s[0] != 31 || s[1] != 139 || s[2] != 8 || s[3] >= 32 { return None; }
    let f = s[3];
    let a = require!(header_extra(s, (f / 4) % 2 == 1));
    let b = require!(header_zero(s, a, (f / 8) % 2 == 1));
    let c = require!(header_zero(s, b, (f / 16) % 2 == 1));
    header_crc(s, c, (f / 2) % 2 == 1)
}

fn fixed_lit() -> Vec<u8> {
    let mut lens = Vec::new();
    let mut i = 0;
    while i < 288 {
        lens.push(if i < 144 { 8 } else if i < 256 { 9 } else if i < 280 { 7 } else { 8 });
        i += 1;
    }
    lens
}

fn fixed_dist() -> Vec<u8> {
    let mut lens = Vec::new();
    let mut i = 0;
    while i < 32 { lens.push(5); i += 1; }
    lens
}

fn count_shorter(lens: &[u8], k: usize, n: u32) -> u32 {
    let mut i = 0;
    let mut c = 0;
    while i < k {
        let l = lens[i] as u32;
        if l > 0 && l < n { c += 1u32 << (n - l); }
        i += 1;
    }
    c
}

fn count_earlier(lens: &[u8], k: usize, n: u32) -> u32 {
    let mut i = 0;
    let mut c = 0;
    while i < k {
        if lens[i] as u32 == n { c += 1; }
        i += 1;
    }
    c
}

fn codeword(lens: &[u8], sym: usize) -> u32 {
    let n = lens[sym] as u32;
    count_shorter(lens, lens.len(), n) + count_earlier(lens, sym, n)
}

fn read_code(s: &[u8], r: &mut Reader, count: u32) -> Option<u32> {
    let mut prefix = 0u32;
    let mut n = 0u32;
    while n < count {
        let b = require!(read_bit(s, r));
        prefix = 2 * prefix + b;
        n += 1;
    }
    Some(prefix)
}

// Canonical codewords depend only on the block's code-length table. The count of shorter codes
// is taken once per length, and the count of earlier symbols of each length is kept running.
#[inline(never)]
fn codeword_table(lens: &[u8]) -> (Vec<u32>, [u16; 512], [usize; 17]) {
    // Count all lengths in one pass. Four independent histograms let consecutive symbols
    // increment the same length without waiting on the previous increment.
    let mut count = [0u32; 16];
    let mut c1 = [0u32; 16];
    let mut c2 = [0u32; 16];
    let mut c3 = [0u32; 16];
    let mut i = 0;
    while lens.len() - i >= 4 {
        let n0 = lens[i] as usize;
        let n1 = lens[i + 1] as usize;
        let n2 = lens[i + 2] as usize;
        let n3 = lens[i + 3] as usize;
        if n0 < 16 { count[n0] += 1; }
        if n1 < 16 { c1[n1] += 1; }
        if n2 < 16 { c2[n2] += 1; }
        if n3 < 16 { c3[n3] += 1; }
        i += 4;
    }
    while i < lens.len() {
        let n = lens[i] as usize;
        if n < 16 { count[n] += 1; }
        i += 1;
    }
    let mut n = 0;
    while n < 16 {
        count[n] += c1[n] + c2[n] + c3[n];
        n += 1;
    }
    // shorter[n] = count_shorter(lens, lens.len(), n), by the recurrence
    // count_shorter(n + 1) = 2 * (count_shorter(n) + count[n]) for n >= 1; it is 0 for n <= 1.
    // start[n]: how many symbols have a length below n, where the group of length n starts in
    // the sorted order.
    let mut shorter = [0u32; 16];
    let mut start = [0usize; 17];
    let mut n = 1usize;
    while n < 15 {
        shorter[n + 1] = 2 * (shorter[n] + count[n]);
        n += 1;
    }
    let mut n = 0usize;
    while n < 16 {
        start[n + 1] = start[n] + count[n] as usize;
        n += 1;
    }
    let mut seen = [0u32; 16];
    let mut sorted = [0u16; 512];
    let mut table = vec![0u32; lens.len()];
    let mut sym = 0;
    while sym < lens.len() {
        let n = lens[sym] as usize;
        let code = if n < 16 {
            let c = shorter[n] + seen[n];
            sorted[(start[n] + seen[n] as usize) % 512] = sym as u16;
            seen[n] += 1;
            c
        } else {
            codeword(lens, sym)
        };
        table[sym] = code;
        sym += 1;
    }
    (table, sorted, start)
}

fn cached_codeword(_lens: &[u8], codes: &[u32], sym: usize) -> u32 {
    codes[sym]
}

fn read_symbol_at(s: &[u8], r: &mut Reader, lens: &[u8], codes: &[u32], sym: usize) -> Option<u32> {
    if sym == lens.len() { return None; }
    let n = lens[sym] as u32;
    if n > 0 {
        let mut trial = Reader { byte: r.byte, bit: r.bit };
        match read_code_fast(s, &mut trial, n) {
            Some(code) => {
                if cached_codeword(lens, codes, sym) == code {
                    *r = trial;
                    return Some(sym as u32);
                }
            }
            None => {}
        }
    }
    read_symbol_at(s, r, lens, codes, sym + 1)
}

// Eleven-bit prefixes cover the common short codes. Every hit is validated by
// the decoder, and longer codes use the ordinary symbol search.
// The stream from the reader's position on, as a number (least significant bit first): bits
// 0..17 of the result are the next 17 bits. None within three bytes of the end of input.
#[inline(always)]
fn peek(s: &[u8], r: &Reader) -> Option<u32> {
    if r.bit >= 8 || r.byte >= s.len() || s.len() - r.byte < 3 { return None; }
    let w = s[r.byte] as u32 + 256 * (s[r.byte + 1] as u32) + 65536 * (s[r.byte + 2] as u32);
    Some(w >> r.bit)
}

#[inline(always)]
fn skip_bits(r: &mut Reader, n: u32) {
    let bit = r.bit + n;
    r.byte += (bit / 8) as usize;
    r.bit = bit % 8;
}

#[inline(always)]
fn read_field_fast(s: &[u8], r: &mut Reader, count: u32) -> Option<u32> {
    if count == 0 { return Some(0); }
    if count > 16 { return read_field(s, r, count); }
    match peek(s, r) {
        Some(p) => {
            skip_bits(r, count);
            Some(p % (1u32 << count))
        }
        None => read_field(s, r, count),
    }
}

// The first n bits of code, in the opposite order.
#[inline(always)]
fn reverse_bits(code: u32, n: u32) -> u32 {
    let mut rev = 0u32;
    let mut c = code;
    let mut k = 0u32;
    while k < n {
        rev = 2 * rev + c % 2;
        c /= 2;
        k += 1;
    }
    rev
}

#[inline(always)]
fn read_code_fast(s: &[u8], r: &mut Reader, n: u32) -> Option<u32> {
    if n > 16 { return read_code(s, r, n); }
    match peek(s, r) {
        Some(p) => {
            let code = reverse_bits(p, n);
            skip_bits(r, n);
            Some(code)
        }
        None => read_code(s, r, n),
    }
}

// The count of extra bits that goes with a symbol of a table: of length code sym - 257 in a
// literal/length table (symbols 257..=285), of distance code sym in a distance table (symbols
// 0..=29); zero for any other symbol.
const fn entry_extra(sym: u32, is_dist: bool) -> u32 {
    if is_dist {
        if sym <= 29 { distance_extra(sym) } else { 0 }
    } else if sym > 256 && sym <= 285 {
        length_extra(sym - 257)
    } else {
        0
    }
}

// The base value that goes with a symbol of a table, as for entry_extra.
const fn entry_base(sym: u32, is_dist: bool) -> u32 {
    if is_dist {
        if sym <= 29 { distance_base(sym) } else { 0 }
    } else if sym > 256 && sym <= 285 {
        length_base(sym - 257)
    } else {
        0
    }
}

// A table entry: the bits the symbol takes (its codeword length n plus its extra-bit count) in
// bits 0..5, the symbol in bits 6..15 and its base value above, so that one load gives the
// decoder everything it needs about a symbol, and the bit count, which the next lookup waits
// for, comes out with one mask. A length code (257..=285 of a literal/length table, whose base
// is below 512) also carries its codeword length n in bits 24..28, so that the decoder needs no
// second lookup to find where its extra bits start.
// The part of each symbol's entry that does not depend on its codeword length: its extra-bit
// count, the symbol and its base value, for the 320 symbols a table can have; computed once
// when the program is compiled.
const fn entry_tab(is_dist: bool) -> [u32; 320] {
    let mut t = [0u32; 320];
    let mut sym = 0u32;
    while sym < 320 {
        let x = entry_extra(sym, is_dist);
        let b = entry_base(sym, is_dist);
        t[sym as usize] = x + 64 * sym + 32768 * b;
        sym += 1;
    }
    t
}

const LIT_TAB: [u32; 320] = entry_tab(false);
const DIST_TAB: [u32; 320] = entry_tab(true);

// The packed entry of a symbol below 320 whose codeword has n bits:
// the symbol's part from the table, plus n and a length code's length field.
#[inline(always)]
fn pack_fast(sym: u32, n: u32, is_dist: bool) -> u32 {
    let len_field = if !is_dist && sym > 256 && sym <= 285 { 16777216 * n } else { 0 };
    let part = if is_dist { DIST_TAB[sym as usize] } else { LIT_TAB[sym as usize] };
    n + part + len_field
}

// Indexed by the next eleven bits of the stream as peek returns them: the packed entry of the
// symbol whose codeword (of at most eleven bits) they start with, or the entry of symbol 320
// where the codeword is longer. A codeword is stored first bit first and peek has the first bit
// lowest, hence the reversal; an entry is written only where reversing its index gives the
// codeword back.
// Entry i is the eight bits of i in the opposite order: the reversal of i / 2 shifted down,
// with the lowest bit of i on top. Entries 2j and 2j + 1 are both taken from entry j.
#[inline(never)]
fn rev_table() -> [u8; 256] {
    let mut r = [0u8; 256];
    let mut j = 0;
    while j < 128 {
        let h = r[j] / 2;
        r[2 * j] = h;
        r[2 * j + 1] = h + 128;
        j += 1;
    }
    r
}

// The first n bits of code (n in 1..=16) in the opposite order, as reverse_bits: the two low
// bytes reversed and swapped make the sixteen-bit reversal, shifted down to n bits.
#[inline(always)]
fn reverse_fast(r: &[u8; 256], code: u32, n: u32) -> u32 {
    (256 * (r[(code % 256) as usize] as u32) + r[((code / 256) % 256) as usize] as u32) >> (16 - n)
}

// Only the first 2^bits of the 2048 entries are used (bits in 1..=11): a lookup masks the stream
// bits to bits, so a code's entries are written only that far, and a codeword longer than bits
// gets the sentinel. r is the byte-reversal table.
// The symbols come grouped by codeword length (sorted, with the groups starting at start[n], as
// codeword_table gives them): each code of length n writes one entry at its reversed codeword,
// below 2^n, and the first 2^n entries are then doubled to 2^(n+1), since the entry of a code
// of at most n bits depends only on the index's low n bits. The order is only a hint: a symbol
// is used only where its length is checked to be the level's.
#[inline(never)]
fn decode_table(lens: &[u8], codes: &[u32], sorted: &[u16; 512], start: &[usize; 17], is_dist: bool,
    bits: u32, r: &[u8; 256]) -> [u32; 2048] {
    let mut table = [20480u32; 2048];
    // The used size, at most 2048 (bits is at most 11; a larger request fills nothing).
    let size = if bits <= 11 { 1usize << bits } else { 0 };
    let mut n = 1u32;
    while n <= bits && n <= 11 {
        let step = 1u32 << n;
        let st = step as usize;
        let end = start[n as usize + 1];
        let mut j = start[n as usize];
        while j < end {
            let sym = sorted[j % 512] as usize;
            if sym < lens.len() && sym < codes.len() && lens[sym] as u32 == n {
                let code = codes[sym];
                if code < step {
                    let rev = reverse_fast(r, code, n);
                    table[(rev as usize) % 2048] = pack_fast(sym as u32, n, is_dist);
                }
            }
            j += 1;
        }
        if 2 * st <= size {
            let mut k = 0;
            while k < st {
                table[st + k] = table[k];
                k += 1;
            }
        }
        n += 1;
    }
    table
}

// A symbol whose codeword of twelve to fifteen bits may be what the stream bits p start with, or
// lens.len(). Codewords are compared as numbers, the first fifteen stream bits reversed and cut
// to length; this is only a hint, which read_symbol_slow validates.
fn find_long(lens: &[u8], codes: &[u32], p: u32) -> usize {
    let rev = reverse_bits(p, 15);
    let mut sym = 0;
    while sym < lens.len() && sym < codes.len() {
        let n = lens[sym] as u32;
        if n > 11 && n <= 15 && codes[sym] == rev >> (15 - n) { break; }
        sym += 1;
    }
    sym
}

// Long codewords usually share their first six stream bits. Cache the remaining nine bits;
// collisions only make the hint miss, since the full codeword is checked before using it.
#[inline(never)]
fn long_hints(lens: &[u8], codes: &[u32], r: &[u8; 256]) -> [u16; 512] {
    let mut hints = [320u16; 512];
    let mut sym = 0;
    while sym < lens.len() && sym < codes.len() && sym < 320 {
        let n = lens[sym] as u32;
        if n > 11 && n <= 15 {
            let rev = reverse_fast(r, codes[sym], n);
            let step = 1usize << n;
            let mut k = rev as usize;
            while k < 32768 {
                hints[k / 64] = sym as u16;
                k += step;
            }
        }
        sym += 1;
    }
    hints
}

fn read_symbol_hinted(s: &[u8], r: &mut Reader, lens: &[u8], codes: &[u32],
    table: &[u32; 2048], hints: &[u16; 512]) -> Option<u32> {
    match peek(s, r) {
        Some(p) => {
            let sym = hints[((p / 64) % 512) as usize] as usize;
            if sym < lens.len() && sym < codes.len() {
                let n = lens[sym] as u32;
                if n > 11 && n <= 15 && reverse_bits(p, n) == codes[sym] {
                    skip_bits(r, n);
                    return Some(sym as u32);
                }
            }
        }
        None => {}
    }
    read_symbol_fast(s, r, lens, codes, table, 2047)
}

// A codeword too long for the table: try the hinted symbol before the ordinary symbol search.
fn read_symbol_slow(s: &[u8], r: &mut Reader, lens: &[u8], codes: &[u32]) -> Option<u32> {
    match peek(s, r) {
        Some(p) => {
            let sym = find_long(lens, codes, p);
            if sym < lens.len() && sym < codes.len() {
                let n = lens[sym] as u32;
                if n > 0 && n <= 15 && reverse_bits(p, n) == codes[sym] {
                    skip_bits(r, n);
                    return Some(sym as u32);
                }
            }
        }
        None => {}
    }
    read_symbol_at(s, r, lens, codes, 0)
}

#[inline(always)]
fn read_symbol_fast(s: &[u8], r: &mut Reader, lens: &[u8], codes: &[u32], table: &[u32; 2048], mask: u32) -> Option<u32> {
    match peek(s, r) {
        Some(p) => {
            let sym = ((table[((p % 2048) & mask) as usize] / 64) % 512) as usize;
            if sym < lens.len() {
                skip_bits(r, lens[sym] as u32);
                return Some(sym as u32);
            }
        }
        None => {}
    }
    read_symbol_slow(s, r, lens, codes)
}

fn lengths_bounded(lens: &[u8], k: usize, max: u32) -> bool {
    if k == 0 { true }
    else { lens[k - 1] as u32 <= max && lengths_bounded(lens, k - 1, max) }
}

fn valid(lens: &[u8], max: u32) -> bool {
    lengths_bounded(lens, lens.len(), max)
        && count_shorter(lens, lens.len(), max + 1) <= (1u32 << (max + 1))
}

fn read_length_run(s: &[u8], r: &mut Reader, cl: &[u8], codes: &[u32], table: &[u32; 2048], all: &[u8]) -> Option<(u8, usize)> {
    let sym = require!(read_symbol_fast(s, r, cl, codes, table, 127));
    if sym < 16 { Some((sym as u8, 1)) }
    else if sym == 16 {
        if all.len() == 0 { return None; }
        Some((all[all.len() - 1], 3 + require!(read_field_fast(s, r, 2)) as usize))
    } else if sym == 17 { Some((0, 3 + require!(read_field_fast(s, r, 3)) as usize)) }
    else if sym == 18 { Some((0, 11 + require!(read_field_fast(s, r, 7)) as usize)) }
    else { None }
}

fn repeat_value(all: &mut Vec<u8>, value: u8, count: usize) {
    let mut k = 0;
    while k < count { all.push(value); k += 1; }
}

fn read_lengths(s: &[u8], r: &mut Reader, cl: &[u8], codes: &[u32], table: &[u32; 2048], all: &mut Vec<u8>, total: usize) -> Option<()> {
    if all.len() == total { return Some(()); }
    let (value, count) = require!(read_length_run(s, r, cl, codes, table, all));
    if count > total - all.len() { return None; }
    repeat_value(all, value, count);
    read_lengths(s, r, cl, codes, table, all, total)
}

// The run that a code-length symbol sym starts, its codeword n bits long, when q holds the stream
// bits after the codeword: the value, how many times it repeats, and the bits the whole run
// takes. None for symbol 16 with nothing to repeat.
fn run_window(sym: u32, n: u32, q: u64, all: &[u8]) -> Option<(u8, usize, u32)> {
    if sym < 16 { return Some((sym as u8, 1, n)); }
    if sym == 16 {
        if all.len() == 0 { return None; }
        return Some((all[all.len() - 1], 3 + (q % 4) as usize, n + 2));
    }
    if sym == 17 { return Some((0, 3 + (q % 8) as usize, n + 3)); }
    if sym == 18 { return Some((0, 11 + (q % 128) as usize, n + 7)); }
    None
}

// The code lengths read through the bit window: a run takes at most seven code bits and seven
// extra bits, so a refilled window (56 bits or more) always holds a whole one, and the table
// (of seven bits) decodes the codeword. The reader takes over when fewer than 14 bits can be
// had or the table has no entry (a codeword of a symbol the table does not name).
fn read_lengths_fast(s: &[u8], r: &mut Reader, cl: &[u8], codes: &[u32], table: &[u32; 2048], all: &mut Vec<u8>, total: usize) -> Option<()> {
    let (w0, nb0, c0) = window_at(s, r);
    let mut buf = w0;
    let mut nbits = nb0;
    let mut cpos = c0;
    while all.len() < total {
        let (w, nb, c) = refill(s, buf, nbits, cpos);
        buf = w;
        nbits = nb;
        cpos = c;
        if nbits < 14 { break; }
        let e = table[(buf % 128) as usize];
        let sym = (e / 64) % 512;
        if sym >= cl.len() as u32 { break; }
        let n = e % 32;
        let (value, count, bits) = require!(run_window(sym, n, buf >> n, all));
        if count > total - all.len() { return None; }
        repeat_value(all, value, count);
        buf = buf >> bits;
        nbits -= bits;
    }
    *r = reader_at(cpos, nbits);
    read_lengths(s, r, cl, codes, table, all, total)
}

fn cl_order(k: usize) -> usize {
    let order = [16usize,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15];
    order[k]
}

fn read_clens(s: &[u8], r: &mut Reader, cl: &mut Vec<u8>, k: usize, nc: usize) -> Option<()> {
    if k == nc { return Some(()); }
    let value = require!(read_field_fast(s, r, 3));
    cl[cl_order(k)] = value as u8;
    read_clens(s, r, cl, k + 1, nc)
}

fn table_slice(all: &[u8], start: usize, count: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(count);
    let mut k = 0;
    while k < count { out.push(all[start + k]); k += 1; }
    out
}

fn dynamic_tables(s: &[u8], r: &mut Reader) -> Option<(Vec<u8>, Vec<u8>)> {
    let nl = 257 + require!(read_field_fast(s, r, 5)) as usize;
    let nd = 1 + require!(read_field_fast(s, r, 5)) as usize;
    let nc = 4 + require!(read_field_fast(s, r, 4)) as usize;
    let mut cl = Vec::with_capacity(19);
    repeat_value(&mut cl, 0, 19);
    require!(read_clens(s, r, &mut cl, 0, nc));
    if !valid(&cl, 7) { return None; }
    let (cl_codes, cl_sorted, cl_start) = codeword_table(&cl);
    let cl_table = decode_table(&cl, &cl_codes, &cl_sorted, &cl_start, false, 7, &rev_table());
    let mut all = Vec::with_capacity(nl + nd);
    require!(read_lengths_fast(s, r, &cl, &cl_codes, &cl_table, &mut all, nl + nd));
    let lit = table_slice(&all, 0, nl);
    let dist = table_slice(&all, nl, nd);
    if valid(&lit, 15) && valid(&dist, 15) { Some((lit, dist)) } else { None }
}

// Writes w as eight little-endian bytes at i: the bytes are copied in as one slice so that a
// single bounds check covers them and the compiler keeps the store whole.
#[inline(always)]
fn store8(v: &mut Vec<u8>, i: usize, w: u64) {
    let x = [(w % 256) as u8, ((w / 256) % 256) as u8, ((w / 65536) % 256) as u8,
        ((w / 16777216) % 256) as u8, ((w / 4294967296) % 256) as u8,
        ((w / 1099511627776) % 256) as u8, ((w / 281474976710656) % 256) as u8,
        ((w / 72057594037927936) % 256) as u8];
    v[i..i + 8].copy_from_slice(&x);
}

// Copies len bytes from d back to position n, writing in chunks of eight that may run up to
// 23 bytes past n + len. Requires 1 <= d <= n and n + len + 24 <= out.len().
// Writes w as eight little-endian bytes at i of a slice, as store8.
#[inline(always)]
fn store8w(b: &mut [u8], i: usize, w: u64) {
    let x = [(w % 256) as u8, ((w / 256) % 256) as u8, ((w / 65536) % 256) as u8,
        ((w / 16777216) % 256) as u8, ((w / 4294967296) % 256) as u8,
        ((w / 1099511627776) % 256) as u8, ((w / 281474976710656) % 256) as u8,
        ((w / 72057594037927936) % 256) as u8];
    b[i..i + 8].copy_from_slice(&x);
}

// The chunks of a copy from the third on, out of line so that the loop's code does not weigh on
// the decoder's registers: only one copy in thirty is longer than sixteen bytes.
#[inline(never)]
fn copy_tail(o: &mut [u8], d: usize, len: usize) {
    let mut k = 16;
    while k < len {
        store8w(o, d + k, load8s(o, k));
        k += 8;
    }
}

// start is n - d, computed by the caller.
#[inline(always)]
fn copy_at(out: &mut Vec<u8>, start: usize, n: usize, d: usize, len: usize) {
    if d >= 8 {
        // The source and destination both lie in this one window of the buffer, so that one
        // bounds check covers every chunk: the source chunk k is at k, its destination at d + k.
        // The window's length is written as a sum so that the compiler sees it is d + len + 24.
        let o = &mut out[start..][..d + len + 24];
        let w0 = load8a(o, 0);
        let w1 = load8a(o, 8);
        // Repair overlap only within the requested bytes; bytes after len are scratch.
        let w2 = if len > d && d < 16 { let s = 8 * (d - 8); w1 % (1u64 << s) + (w0 << s) } else { w1 };
        store8w(o, d, w0);
        store8w(o, d + 8, w2);
        if len > 16 { copy_tail(o, d, len); }
    } else if d == 1 {
        let w = (out[n - 1] as u64) * 72340172838076673;
        let mut k = 0;
        while k < len { store8(out, n + k, w); k += 8; }
    } else {
        let mut k = 0;
        while k < len { out[n + k] = out[n + k - d]; k += 1; }
    }
}

#[inline(always)]
fn read_match(s: &[u8], r: &mut Reader, dist: &[u8], codes: &[u32], table: &[u32; 2048], lc: u32) -> Option<(usize, usize)> {
    let len = (length_base(lc) + require!(read_field_fast(s, r, length_extra(lc)))) as usize;
    let dc = require!(read_symbol_fast(s, r, dist, codes, table, 1023));
    if dc > 29 { return None; }
    let d = (distance_base(dc) + require!(read_field_fast(s, r, distance_extra(dc)))) as usize;
    Some((len, d))
}

// The code lengths in an array indexed by any nine-bit symbol, so that the lookup of a table
// entry's symbol needs no bounds check: zero beyond lens.
#[inline(never)]
fn lens_array(lens: &[u8]) -> [u8; 512] {
    let mut a = [0u8; 512];
    let mut i = 0;
    while i < lens.len() && i < 512 {
        a[i] = lens[i];
        i += 1;
    }
    a
}

fn decode_symbols(s: &[u8], r: &mut Reader, lit: &[u8], dist: &[u8], out: &mut Vec<u8>, n: usize) -> Option<usize> {
    let (lit_codes, lit_sorted, lit_start) = codeword_table(lit);
    let (dist_codes, dist_sorted, dist_start) = codeword_table(dist);
    // Distance codewords are rarely longer than ten bits: a 1024-entry table is enough, and the
    // longer ones take the slow path.
    let rv = rev_table();
    let table = decode_table(lit, &lit_codes, &lit_sorted, &lit_start, false, 11, &rv);
    let dist_table = decode_table(dist, &dist_codes, &dist_sorted, &dist_start, true, 10, &rv);
    let distn = lens_array(dist);
    let distq = dist_lens(&dist_table, &distn);
    decode_symbols_cached(s, r, lit, dist, &lit_codes, &dist_codes, &table, &dist_table, &distq, &rv, out, n)
}

// The codeword length of the symbol of each of the 1024 entries of the distance table, indexed
// like the table (by the next ten stream bits), so that the decoder finds the length of a
// distance code at the index it already has instead of through the entry's symbol.
#[inline(never)]
fn dist_lens(table: &[u32; 2048], distn: &[u8; 512]) -> [u8; 1024] {
    let mut a = [0u8; 1024];
    let mut i = 0;
    while i < 1024 {
        a[i] = distn[((table[i] / 64) % 512) as usize];
        i += 1;
    }
    a
}

#[inline(always)]
fn load8a(s: &[u8], i: usize) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&s[i..i + 8]);
    b[0] as u64 + 256 * (b[1] as u64) + 65536 * (b[2] as u64) + 16777216 * (b[3] as u64)
        + 4294967296 * (b[4] as u64) + 1099511627776 * (b[5] as u64)
        + 281474976710656 * (b[6] as u64) + 72057594037927936 * (b[7] as u64)
}

// The eight bytes of s from i as a little-endian number, through one subslice as load8.
#[inline(always)]
fn load8s(s: &[u8], i: usize) -> u64 {
    let b = &s[i..i + 8];
    b[0] as u64 + 256 * (b[1] as u64) + 65536 * (b[2] as u64) + 16777216 * (b[3] as u64)
        + 4294967296 * (b[4] as u64) + 1099511627776 * (b[5] as u64)
        + 281474976710656 * (b[6] as u64) + 72057594037927936 * (b[7] as u64)
}

// The bit window (buf, nbits, cpos) at a reader's position: bits 0..nbits of buf are the stream
// bits from position 8 * cpos - nbits on, which is the reader's position, and the bits above are
// zero. At the end of input (byte == len, bit == 0) the window is empty.
#[inline(always)]
fn window_at(s: &[u8], r: &Reader) -> (u64, u32, usize) {
    if r.byte < s.len() && r.bit < 8 {
        ((s[r.byte] as u64) >> r.bit, 8 - r.bit, r.byte + 1)
    } else {
        (0, 0, r.byte)
    }
}

// The reader at the position 8 * cpos - nbits of a window. Requires (nbits + 7) / 8 <= cpos.
#[inline(always)]
fn reader_at(cpos: usize, nbits: u32) -> Reader {
    Reader { byte: cpos - ((nbits + 7) / 8) as usize, bit: (8 - nbits % 8) % 8 }
}

// The window refilled from the eight bytes at cpos when they exist: they are ored in above the
// window's bits (where they agree with whatever is already there) and cpos moves past the whole
// bytes that fit, so that the window holds 56 to 63 bits at the same position. Requires
// cpos <= s.len() and nbits <= 63.
#[inline(always)]
fn refill(s: &[u8], buf: u64, nbits: u32, cpos: usize) -> (u64, u32, usize) {
    // The bytes from cpos as one slice: its length check is the only bounds check of the load.
    // The new count nbits | 56 is nbits % 8 + 56 as nbits < 64.
    if s.len() >= 8 && cpos <= s.len() - 8 {
        (buf | (load8s(s, cpos) << nbits), nbits | 56, cpos + 7 - (nbits / 8) as usize)
    } else {
        (buf, nbits, cpos)
    }
}

// The next token from the window p of nbits bits (bits 0..nbits are the next stream bits), when
// at least 56 are there and its codewords are in the tables: (1, byte, 0, bits, rest) for a
// literal, (2, length, distance, bits, rest) for a copy, where bits is what the token occupies
// (at most 11 + 5 + 11 + 13 of the 56 bits in sight) and rest is the window after it, p >> bits.
// (0, 0, 0, 0, 0) for anything else. The bit counts and base values come packed in the table
// entries; the codeword lengths come from the length tables.
// The copy whose length symbol (a length code, 257..=285, in lit) has the table entry e: the
// length's extra bits, the distance symbol and its extra bits follow in the window p. The length
// code's codeword length is in bits 24..28 of e; distq holds the codeword length of the symbol
// of each distance table entry, at the entry's index, as dist_lens gives them.
#[inline(always)]
fn peek_copy(p: u64, q2: u64, e: u32, distq: &[u8; 1024], dist_table: &[u32; 2048],
    n_out: usize, limit: usize) -> (u32, u32, u32, u32, u64) {
    let n = e / 16777216;
    let t = e % 32;
    let e2 = dist_table[(q2 % 1024) as usize];
    // A base of at least one marks the entry of a distance code 0..=29: the other symbols and
    // the sentinel have base zero. Past limit, the slow path checks the room exactly.
    if e2 >= 32768 && n_out <= limit {
        let dn = distq[(q2 % 1024) as usize] as u32;
        let t2 = e2 % 32;
        let rest = q2 >> (e2 % 64);
        // The extra bits are bits n..t of p: the remainder of p below t (p less q2 shifted
        // back), shifted down by n; the same for the distance with q2, dn and t2.
        let len = e / 32768 % 512 + ((p - (q2 << t)) >> n) as u32;
        let d = e2 / 32768 + ((q2 - (rest << t2)) >> dn) as u32;
        return (2, len, d, t + t2, rest);
    }
    (0, 0, 0, 0, 0)
}

// e is the table entry at the window's position. A token is decoded only when the window holds
// lo bits, at least 45: a copy takes at most 40 (two codewords of at most eleven bits, five and
// thirteen extra bits) and a literal at most eleven.
#[inline(always)]
fn peek_token(p: u64, q: u64, nbits: u32, lo: u32, e: u32, distq: &[u8; 1024], dist_table: &[u32; 2048],
    n_out: usize, limit: usize) -> (u32, u32, u32, u32, u64) {
    if nbits < lo { return (0, 0, 0, 0, 0); }
    // The symbol is below 256 exactly when bit 14 of the entry is clear.
    if e % 32768 < 16384 { return (1, (e / 64) % 256, 0, e % 32, q); }
    // A base of at least three marks the entry of a length code 257..=285: the end-of-block
    // symbol, 286, 287 and the sentinel have base zero and no bits above 14.
    if e >= 32768 { return peek_copy(p, q, e, distq, dist_table, n_out, limit); }
    (0, 0, 0, 0, 0)
}

// Decodes the tokens of a block into out from position n on, up to and including the
// end-of-block symbol, and returns the position after them. out is a buffer whose length never
// changes; its bytes from the returned position on are scratch. None when the stream is not a
// block, or when the tokens would write past out.len() - 24 (so the content is longer than the
// buffer was sized for).
//
// The stream is read through a bit window (buf, nbits, cpos): bits 0..nbits of buf are the
// stream bits from position 8 * cpos - nbits on, and every bit above is zero or the stream's
// bit at the same place. Refilling ors the eight bytes at cpos in above the window's bits, which
// agree with the bits already there, and advances cpos by the whole bytes that fit: the load
// address never depends on the token being decoded. The reader is only computed for the slow
// path and at the end.
//
// The loop keeps the table entry at the window's position as part of its state, looked up from
// the window before it is refilled: a refilled window holds all 64 of its bits from the stream,
// a token takes at most 40 of them and a literal at most eleven, so at least eleven are left
// after a literal and a token, and the low eleven bits of a window are the same after the
// refill. When no refill was possible (fewer than eight bytes left) the entry may be stale, but
// then the window holds fewer than 56 bits when it is next needed and the slow path takes over.
//
// After a literal, which takes at most eleven bits of the 56 the window held, the next token is
// decoded from the same window without a refill: that saves the refill of every token that
// follows a literal.
//
// The next entry and the refilled window after a token: the entry is looked up from the window
// `rest` of `nrest` bits as it is, then the window is refilled.
#[inline(always)]
fn advance(s: &[u8], table: &[u32; 2048], rest: u64, nrest: u32, cpos: usize) -> (u32, u64, u32, usize) {
    let e = table[(rest % 2048) as usize];
    let (w, nb, c) = refill(s, rest, nrest, cpos);
    (e, w, nb, c)
}

fn decode_symbols_cached(s: &[u8], r: &mut Reader, lit: &[u8], dist: &[u8],
    lit_codes: &[u32], dist_codes: &[u32], table: &[u32; 2048], dist_table: &[u32; 2048],
    distq: &[u8; 1024], rv: &[u8; 256], out: &mut Vec<u8>, n: usize) -> Option<usize> {
    let hints = long_hints(lit, lit_codes, rv);
    let mut n = n;
    // Positions up to limit have room for any copy (at most 289 bytes) and the chunk slack, so
    // the fast path checks one bound per copy; beyond it the slow path checks exactly.
    let limit = if out.len() >= 320 { out.len() - 320 } else { 0 };
    let (w0, nb0, c0) = window_at(s, r);
    let (w1, nb1, c1) = refill(s, w0, nb0, c0);
    let mut buf = w1;
    let mut nbits = nb1;
    let mut cpos = c1;
    let mut e = table[(buf % 2048) as usize];
    loop {
        let q = buf >> (e % 64);
        let (kind, a, b, bits, rest) = peek_token(buf, q, nbits, 56, e, distq, dist_table, n, limit);
        if kind == 2 {
            // A copy only up to limit, so that it has room: at most 289 bytes and the slack.
            let len = a as usize;
            let d = b as usize;
            // The source's start, before the check that it exists: the compiler folds the
            // subtraction and the comparison into one.
            let start = n.wrapping_sub(d);
            if d > n { return None; }
            let (e1, w, nb, c) = advance(s, table, rest, nbits - bits, cpos);
            e = e1;
            buf = w;
            nbits = nb;
            cpos = c;
            copy_at(out, start, n, d, len);
            n += len;
            continue;
        }
        if kind == 1 {
            if n >= out.len() { return None; }
            out[n] = a as u8;
            n += 1;
            // The window still holds at least 45 bits: the next token needs no refill.
            let nb2 = nbits - bits;
            let e2 = table[(rest % 2048) as usize];
            let q2 = rest >> (e2 % 64);
            let (kind2, a2, b2, bits2, rest2) = peek_token(rest, q2, nb2, 45, e2, distq, dist_table, n, limit);
            if kind2 == 1 {
                if n >= out.len() { return None; }
                out[n] = a2 as u8;
                n += 1;
                let (e1, w, nb, c) = advance(s, table, rest2, nb2 - bits2, cpos);
                e = e1;
                buf = w;
                nbits = nb;
                cpos = c;
                continue;
            }
            if kind2 == 2 {
                let len = a2 as usize;
                let d = b2 as usize;
                let start = n.wrapping_sub(d);
                if d > n { return None; }
                let (e1, w, nb, c) = advance(s, table, rest2, nb2 - bits2, cpos);
                e = e1;
                buf = w;
                nbits = nb;
                cpos = c;
                copy_at(out, start, n, d, len);
                n += len;
                continue;
            }
            let (e1, w, nb, c) = advance(s, table, rest, nb2, cpos);
            e = e1;
            buf = w;
            nbits = nb;
            cpos = c;
            continue;
        }
        *r = reader_at(cpos, nbits);
        let sym = require!(read_symbol_hinted(s, r, lit, lit_codes, table, &hints));
        if sym == 256 { return Some(n); }
        if sym < 256 {
            if n >= out.len() { return None; }
            out[n] = sym as u8;
            n += 1;
        } else {
            if sym > 285 { return None; }
            let lc = sym - 257;
            let (len, d) = require!(read_match(s, r, dist, dist_codes, dist_table, lc));
            if d > n || n > out.len() || out.len() - n < len + 24 { return None; }
            copy_at(out, n - d, n, d, len);
            n += len;
        }
        let (w2, nb2, c2) = window_at(s, r);
        let (w3, nb3, c3) = refill(s, w2, nb2, c2);
        buf = w3;
        nbits = nb3;
        cpos = c3;
        e = table[(buf % 2048) as usize];
    }
}

fn align_reader(r: &mut Reader) {
    if r.bit != 0 { r.byte += 1; r.bit = 0; }
}

fn decode_stored(s: &[u8], r: &mut Reader, out: &mut Vec<u8>, n: usize) -> Option<usize> {
    align_reader(r);
    let len = require!(read_u16(s, r.byte)) as usize;
    let neg = require!(read_u16(s, r.byte + 2));
    if len as u32 + neg != 65535 { return None; }
    r.byte += 4;
    if len > s.len() - r.byte || n > out.len() || len > out.len() - n { return None; }
    let end = r.byte + len;
    let mut n = n;
    while r.byte < end { out[n] = s[r.byte]; n += 1; r.byte += 1; }
    Some(n)
}

fn decode_block(s: &[u8], r: &mut Reader, out: &mut Vec<u8>, n: usize) -> Option<usize> {
    let kind = require!(read_field(s, r, 2));
    if kind == 0 { decode_stored(s, r, out, n) }
    else if kind == 1 { decode_symbols(s, r, &fixed_lit(), &fixed_dist(), out, n) }
    else if kind == 2 {
        let (lit, dist) = require!(dynamic_tables(s, r));
        decode_symbols(s, r, &lit, &dist, out, n)
    } else { None }
}

fn decode_blocks(s: &[u8], r: &mut Reader, out: &mut Vec<u8>, n: usize) -> Option<usize> {
    let final_block = require!(read_bit(s, r)) == 1;
    let n1 = require!(decode_block(s, r, out, n));
    if final_block { Some(n1) } else { decode_blocks(s, r, out, n1) }
}

pub fn decompress(s: &[u8]) -> Option<Vec<u8>> {
    let start = require!(read_header(s));
    // The trailer's length field sizes the output buffer: content longer than it cannot be a
    // member anyway. Capped at MAXOUT, plus slack for the chunked copies.
    let claimed = require!(read_u32(s, s.len() - 4)) as usize;
    let cap = if claimed > 1073741824 { 1073741824 } else { claimed };
    let mut out = vec![0u8; cap + 290];
    let mut r = Reader { byte: start, bit: 0 };
    let n = require!(decode_blocks(s, &mut r, &mut out, 0));
    align_reader(&mut r);
    if r.byte > s.len() || s.len() - r.byte != 8 { return None; }
    if n > 1073741824 || n > out.len() { return None; }
    out.resize(n, 0);
    if require!(read_u32(s, r.byte)) != crc32_wide(&out) { return None; }
    if require!(read_u32(s, r.byte + 4)) != out.len() as u32 { return None; }
    Some(out)
}
