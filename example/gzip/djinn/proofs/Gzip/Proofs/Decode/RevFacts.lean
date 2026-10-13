import Gzip.Proofs.Decode.PeekFacts

/-! # Bit reversal through a byte table

`rev p n` (PeekFacts) reverses the low `n` bits of `p`. The decoder's tables reverse codewords
through a 256-entry table of reversed bytes: the reversal of sixteen bits is the two reversed
bytes swapped, and the reversal of fewer bits is that shifted down. -/

open Aeneas Std
open Gzip.Proofs.Decode.PeekFacts

namespace Gzip.Proofs.Decode.RevFacts

/-- Reversing `m + n` bits: the low `m` bits reversed land above the next `n` reversed. -/
theorem rev_split (p m n : Nat) : rev p (m + n) = 2 ^ n * rev p m + rev (p / 2 ^ m) n := by
  induction n with
  | zero => simp [rev]
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 by omega]
    simp only [rev]
    rw [ih, Nat.div_div_eq_div_mul, ← pow_add, pow_succ]
    ring

/-- Reversing fewer bits is the longer reversal shifted down. -/
theorem rev_div (p m n : Nat) (h : n ≤ m) : rev p n = rev p m / 2 ^ (m - n) := by
  have hs := rev_split p n (m - n)
  rw [show n + (m - n) = m by omega] at hs
  rw [hs, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt (rev_lt _ _)]
  omega

/-- The lowest bit reversed is the highest. -/
theorem rev_succ_low (p n : Nat) : rev p (n + 1) = 2 ^ n * (p % 2) + rev (p / 2) n := by
  have hs := rev_split p 1 n
  rw [show 1 + n = n + 1 by omega] at hs
  rw [hs]
  simp [rev]

/-- The reversal of a byte from the reversal of its half. -/
theorem rev_byte_step (i : Nat) (hi : i < 256) :
    rev i 8 = rev (i / 2) 8 / 2 + 128 * (i % 2) := by
  have h1 : rev i 8 = 2 ^ 7 * (i % 2) + rev (i / 2) 7 := rev_succ_low i 7
  have h2 : rev (i / 2) 8 = 2 * rev (i / 2) 7 + (i / 2) / 2 ^ 7 % 2 := rfl
  have h3 : (i / 2) / 2 ^ 7 % 2 = 0 := by
    rw [Nat.div_eq_of_lt (by omega)]
  rw [h2, h3, Nat.add_zero, h1]
  omega

/-- Sixteen bits reversed: the reversed low byte above the reversed high byte. -/
theorem rev_sixteen (x : Nat) :
    rev x 16 = 256 * rev (x % 256) 8 + rev (x / 256 % 256) 8 := by
  have hs := rev_split x 8 8
  rw [show (8 : Nat) + 8 = 16 by norm_num] at hs
  rw [hs]
  have e1 := rev_mod x 8 8 (Nat.le_refl 8)
  have e2 := rev_mod (x / 2 ^ 8) 8 8 (Nat.le_refl 8)
  norm_num at e1 e2 ⊢
  rw [e1, e2]

/-- The reversal of `n ≤ 16` bits through the swapped reversed bytes. -/
theorem rev_of_bytes (code n : Nat) (hn : n ≤ 16) :
    rev code n = (256 * rev (code % 256) 8 + rev (code / 256 % 256) 8) / 2 ^ (16 - n) := by
  rw [← rev_sixteen, rev_div code 16 n hn]

end Gzip.Proofs.Decode.RevFacts
