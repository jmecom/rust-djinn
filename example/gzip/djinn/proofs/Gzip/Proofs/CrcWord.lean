import Gzip.Proofs.Crc

open Aeneas Std Result
open Gzip.Spec

namespace Gzip.Proofs.Crc

-- ================================================================ several bytes at once

theorem bits_add (c a b : ℕ) : bits c (a + b) = bits (bits c a) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [Nat.add_succ, bits, ih]; rfl

/-- A byte xored into the register after `n` shifts is the same as xoring it `n` bits up
before them: the shifts are linear. -/
theorem bits_merge (x b n : ℕ) : bits (bits x n ^^^ b) 8 = bits (x ^^^ b * 2 ^ n) (n + 8) := by
  rw [bits_add, bits_linear x (b * 2 ^ n) n, bits_mul_pow]

theorem one_lt (c : ℕ) (h : c < 2 ^ 32) : one c < 2 ^ 32 := by
  unfold one
  split
  · have h1 : c / 2 < 2 ^ 32 := by omega
    have h2 : 3988292384 < 2 ^ 32 := by norm_num
    exact Nat.xor_lt_two_pow h1 h2
  · omega

theorem bits_lt (c n : ℕ) (h : c < 2 ^ 32) : bits c n < 2 ^ 32 := by
  induction n with
  | zero => exact h
  | succ n ih => exact one_lt _ ih

theorem reg_lt (data : List U8) (n : ℕ) : reg data n < 2 ^ 32 := by
  induction n with
  | zero => norm_num [reg]
  | succ n ih =>
      rw [reg]
      apply bits_lt
      have hb : (data[n]!).val < 2 ^ 32 := by
        have := (data[n]!).hBounds
        scalar_tac
      exact Nat.xor_lt_two_pow ih hb

/-- Xoring a value below `2 ^ k` with a multiple of `2 ^ k` is adding them. -/
theorem xor_shift_add (a b k : ℕ) (ha : a < 2 ^ k) : a ^^^ b * 2 ^ k = a + b * 2 ^ k := by
  have hm : (a ^^^ b * 2 ^ k) % 2 ^ k = a := by
    rw [Nat.xor_mod_two_pow, Nat.mul_mod_left, Nat.mod_eq_of_lt ha]
    simp
  have hd : (a ^^^ b * 2 ^ k) / 2 ^ k = b := by
    rw [Nat.xor_div_two_pow, Nat.div_eq_of_lt ha, Nat.mul_div_cancel _ (Nat.two_pow_pos k)]
    simp
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  have := Nat.div_add_mod (a ^^^ b * 2 ^ k) (2 ^ k)
  rw [hd, hm, Nat.mul_comm] at this
  omega

/-- A little-endian word of four bytes, xored together or added: the same number. -/
theorem word_xor_sum (b0 b1 b2 b3 : ℕ) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) :
    b0 ^^^ b1 * 2 ^ 8 ^^^ b2 * 2 ^ 16 ^^^ b3 * 2 ^ 24 =
      b0 + b1 * 2 ^ 8 + b2 * 2 ^ 16 + b3 * 2 ^ 24 := by
  rw [xor_shift_add b0 b1 8 h0]
  rw [xor_shift_add (b0 + b1 * 2 ^ 8) b2 16 (by omega)]
  rw [xor_shift_add (b0 + b1 * 2 ^ 8 + b2 * 2 ^ 16) b3 24 (by omega)]

/-- Splitting the low byte off the input of a long shift. -/
theorem bits_split (x n : ℕ) : bits x (n + 8) = bits (x / 256) n ^^^ bits (x % 256) (n + 8) := by
  have hl : x % 256 < 256 := Nat.mod_lt _ (by decide)
  have he : x = x / 256 * 256 ^^^ x % 256 := by
    have hd : (x / 256 * 256 ^^^ x % 256) / 256 = x / 256 := by
      change (x / 256 * 2 ^ 8 ^^^ x % 256) / 2 ^ 8 = x / 256
      rw [Nat.xor_div_two_pow]
      simp [Nat.div_eq_of_lt hl]
    have hm : (x / 256 * 256 ^^^ x % 256) % 256 = x % 256 := by
      change (x / 256 * 2 ^ 8 ^^^ x % 256) % 2 ^ 8 = x % 256
      rw [Nat.xor_mod_two_pow]
      simp
    omega
  have hh : bits (x / 256 * 256) (n + 8) = bits (x / 256) n := by
    rw [Nat.add_comm, bits_add]
    have hm : bits (x / 256 * 256) 8 = x / 256 := bits_mul_pow (x / 256) 8
    rw [hm]
  conv_lhs => rw [he]
  rw [bits_linear, hh]

/-- The shift of a 32-bit word, byte by byte: each byte shifted the rest of the way. -/
theorem bits_bytes (w n : ℕ) :
    bits w (n + 32) = bits (w / 16777216) (n + 8) ^^^ bits (w / 65536 % 256) (n + 16) ^^^
      bits (w / 256 % 256) (n + 24) ^^^ bits (w % 256) (n + 32) := by
  have h1 : bits w (n + 32) = bits (w / 256) (n + 24) ^^^ bits (w % 256) (n + 32) :=
    bits_split w (n + 24)
  have h2 : bits (w / 256) (n + 24) = bits (w / 256 / 256) (n + 16) ^^^ bits (w / 256 % 256) (n + 24) :=
    bits_split (w / 256) (n + 16)
  have h3 : bits (w / 256 / 256) (n + 16) = bits (w / 256 / 256 / 256) (n + 8) ^^^
      bits (w / 256 / 256 % 256) (n + 16) := bits_split (w / 256 / 256) (n + 8)
  have e1 : w / 256 / 256 = w / 65536 := by omega
  have e2 : w / 65536 / 256 = w / 16777216 := by omega
  rw [h1, h2, h3, e1, e2]

/-- A shifted byte shifted the rest of the way. -/
theorem bits_shifted (b k m : ℕ) : bits (b * 2 ^ k) (k + m) = bits b m := by
  rw [bits_add, bits_mul_pow]

/-- The register after eight more bytes: the first four are xored into the register and its
bytes shifted the rest of the way (`bits_bytes`), the last four shifted on their own. -/
theorem reg_eight (data : List U8) (p : ℕ) (h : p + 8 ≤ data.length) :
    reg data (p + 8) =
      bits (reg data p ^^^ (data[p]!).val ^^^ (data[p + 1]!).val * 2 ^ 8 ^^^
          (data[p + 2]!).val * 2 ^ 16 ^^^ (data[p + 3]!).val * 2 ^ 24) 64 ^^^
      bits (data[p + 4]!).val 32 ^^^ bits (data[p + 5]!).val 24 ^^^
      bits (data[p + 6]!).val 16 ^^^ bits (data[p + 7]!).val 8 := by
  have e : ∀ k, reg data (p + k + 1) = bits (reg data (p + k) ^^^ (data[p + k]!).val) 8 :=
    fun k => rfl
  have h8 : reg data (p + 8) = bits (bits (bits (bits (bits (bits (bits (bits (reg data p ^^^
      (data[p]!).val) 8 ^^^ (data[p + 1]!).val) 8 ^^^ (data[p + 2]!).val) 8 ^^^
      (data[p + 3]!).val) 8 ^^^ (data[p + 4]!).val) 8 ^^^ (data[p + 5]!).val) 8 ^^^
      (data[p + 6]!).val) 8 ^^^ (data[p + 7]!).val) 8 := by
    simp only [reg, Nat.add_zero]
  rw [h8]
  simp only [bits_merge, Nat.reduceAdd, Nat.reducePow]
  rw [bits_linear, bits_linear, bits_linear, bits_linear]
  have s4 : bits ((data[p + 4]!).val * 4294967296) 64 = bits (data[p + 4]!).val 32 :=
    bits_shifted _ 32 32
  have s5 : bits ((data[p + 5]!).val * 1099511627776) 64 = bits (data[p + 5]!).val 24 :=
    bits_shifted _ 40 24
  have s6 : bits ((data[p + 6]!).val * 281474976710656) 64 = bits (data[p + 6]!).val 16 :=
    bits_shifted _ 48 16
  have s7 : bits ((data[p + 7]!).val * 72057594037927936) 64 = bits (data[p + 7]!).val 8 :=
    bits_shifted _ 56 8
  rw [s4, s5, s6, s7]


/-- The register after sixteen more bytes: the first four are xored into the register and its
bytes shifted the rest of the way (`bits_bytes`), the other twelve shifted on their own. -/
theorem reg_sixteen (data : List U8) (p : ℕ) (h : p + 16 ≤ data.length) :
    reg data (p + 16) =
      bits (reg data p ^^^ (data[p]!).val ^^^ (data[p + 1]!).val * 2 ^ 8 ^^^
          (data[p + 2]!).val * 2 ^ 16 ^^^ (data[p + 3]!).val * 2 ^ 24) 128 ^^^
      bits (data[p + 4]!).val 96 ^^^ bits (data[p + 5]!).val 88 ^^^
      bits (data[p + 6]!).val 80 ^^^ bits (data[p + 7]!).val 72 ^^^
      bits (data[p + 8]!).val 64 ^^^ bits (data[p + 9]!).val 56 ^^^
      bits (data[p + 10]!).val 48 ^^^ bits (data[p + 11]!).val 40 ^^^
      bits (data[p + 12]!).val 32 ^^^ bits (data[p + 13]!).val 24 ^^^
      bits (data[p + 14]!).val 16 ^^^ bits (data[p + 15]!).val 8 := by
  have h16 : reg data (p + 16) = bits (bits (bits (bits (bits (bits (bits (bits (bits (bits (bits
      (bits (bits (bits (bits (bits (reg data p ^^^
      (data[p]!).val) 8 ^^^ (data[p + 1]!).val) 8 ^^^ (data[p + 2]!).val) 8 ^^^
      (data[p + 3]!).val) 8 ^^^ (data[p + 4]!).val) 8 ^^^ (data[p + 5]!).val) 8 ^^^
      (data[p + 6]!).val) 8 ^^^ (data[p + 7]!).val) 8 ^^^ (data[p + 8]!).val) 8 ^^^
      (data[p + 9]!).val) 8 ^^^ (data[p + 10]!).val) 8 ^^^ (data[p + 11]!).val) 8 ^^^
      (data[p + 12]!).val) 8 ^^^ (data[p + 13]!).val) 8 ^^^ (data[p + 14]!).val) 8 ^^^
      (data[p + 15]!).val) 8 := by
    simp only [reg, Nat.add_zero]
  rw [h16]
  simp only [bits_merge, Nat.reduceAdd, Nat.reducePow]
  rw [bits_linear, bits_linear, bits_linear, bits_linear, bits_linear, bits_linear,
    bits_linear, bits_linear, bits_linear, bits_linear, bits_linear, bits_linear]
  have s4 : bits ((data[p + 4]!).val * 4294967296) 128 = bits (data[p + 4]!).val 96 :=
    bits_shifted _ 32 96
  have s5 : bits ((data[p + 5]!).val * 1099511627776) 128 = bits (data[p + 5]!).val 88 :=
    bits_shifted _ 40 88
  have s6 : bits ((data[p + 6]!).val * 281474976710656) 128 = bits (data[p + 6]!).val 80 :=
    bits_shifted _ 48 80
  have s7 : bits ((data[p + 7]!).val * 72057594037927936) 128 = bits (data[p + 7]!).val 72 :=
    bits_shifted _ 56 72
  have s8 : bits ((data[p + 8]!).val * 18446744073709551616) 128 = bits (data[p + 8]!).val 64 :=
    bits_shifted _ 64 64
  have s9 : bits ((data[p + 9]!).val * 4722366482869645213696) 128 = bits (data[p + 9]!).val 56 :=
    bits_shifted _ 72 56
  have s10 : bits ((data[p + 10]!).val * 1208925819614629174706176) 128 = bits (data[p + 10]!).val 48 :=
    bits_shifted _ 80 48
  have s11 : bits ((data[p + 11]!).val * 309485009821345068724781056) 128 = bits (data[p + 11]!).val 40 :=
    bits_shifted _ 88 40
  have s12 : bits ((data[p + 12]!).val * 79228162514264337593543950336) 128 = bits (data[p + 12]!).val 32 :=
    bits_shifted _ 96 32
  have s13 : bits ((data[p + 13]!).val * 20282409603651670423947251286016) 128 = bits (data[p + 13]!).val 24 :=
    bits_shifted _ 104 24
  have s14 : bits ((data[p + 14]!).val * 5192296858534827628530496329220096) 128 = bits (data[p + 14]!).val 16 :=
    bits_shifted _ 112 16
  have s15 : bits ((data[p + 15]!).val * 1329227995784915872903807060280344576) 128 = bits (data[p + 15]!).val 8 :=
    bits_shifted _ 120 8
  rw [s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15]

/-- The part of the register after the sixteen bytes from `p` that comes from their last
twelve bytes alone: it does not depend on the register, so it can be computed ahead. -/
def rest (data : List U8) (p : ℕ) : ℕ :=
  bits (data[p + 4]!).val 96 ^^^ bits (data[p + 5]!).val 88 ^^^
    bits (data[p + 6]!).val 80 ^^^ bits (data[p + 7]!).val 72 ^^^
    bits (data[p + 8]!).val 64 ^^^ bits (data[p + 9]!).val 56 ^^^
    bits (data[p + 10]!).val 48 ^^^ bits (data[p + 11]!).val 40 ^^^
    bits (data[p + 12]!).val 32 ^^^ bits (data[p + 13]!).val 24 ^^^
    bits (data[p + 14]!).val 16 ^^^ bits (data[p + 15]!).val 8

/-- The register after sixteen more bytes: the register xored with the word of the first four,
shifted all the way, and the part of the other twelve. -/
theorem reg_split (data : List U8) (p : ℕ) (h : p + 16 ≤ data.length) (c w : ℕ)
    (hc : c = reg data p)
    (hw : w = (data[p]!).val + (data[p + 1]!).val * 256 + (data[p + 2]!).val * 65536 +
      (data[p + 3]!).val * 16777216) :
    bits (c ^^^ w) 128 ^^^ rest data p = reg data (p + 16) := by
  have hl0 : (data[p]!).val < 256 := by have := (data[p]!).hBounds; scalar_tac
  have hl1 : (data[p + 1]!).val < 256 := by have := (data[p + 1]!).hBounds; scalar_tac
  have hl2 : (data[p + 2]!).val < 256 := by have := (data[p + 2]!).hBounds; scalar_tac
  have hw' : w = (data[p]!).val ^^^ (data[p + 1]!).val * 2 ^ 8 ^^^ (data[p + 2]!).val * 2 ^ 16 ^^^
      (data[p + 3]!).val * 2 ^ 24 := by
    rw [word_xor_sum _ _ _ _ hl0 hl1 hl2, hw]
    norm_num
  rw [reg_sixteen data p h, hc, hw', rest]
  simp only [Nat.xor_assoc]

end Gzip.Proofs.Crc
