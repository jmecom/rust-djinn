import Gzip.Proofs.WordPrefix

open Aeneas Std

set_option maxHeartbeats 2000000

namespace Gzip.Proofs.PrefixFlags

def equalityFlags64 (a b : ℕ) : ℕ :=
  (if a % 256 = b % 256 then 1 else 0) +
  (if a % 65536 = b % 65536 then 1 else 0) +
  (if a % 16777216 = b % 16777216 then 1 else 0) +
  (if a % 4294967296 = b % 4294967296 then 1 else 0) +
  (if a % 1099511627776 = b % 1099511627776 then 1 else 0) +
  (if a % 281474976710656 = b % 281474976710656 then 1 else 0) +
  (if a % 72057594037927936 = b % 72057594037927936 then 1 else 0)

theorem lowest_bit_mod (x k : ℕ) (hbit : x.testBit k = true)
    (hpre : ∀ j < k, x.testBit j = false) (n : ℕ) :
    x % 2 ^ n = 0 ↔ n ≤ k := by
  constructor
  · intro hz
    by_contra hn
    have hkn : k < n := by omega
    have hb := congrArg (fun z : ℕ => z.testBit k) hz
    simp only [Nat.testBit_mod_two_pow, hbit, Nat.zero_testBit] at hb
    simp [hkn] at hb
  · intro hn
    apply Nat.zero_of_testBit_eq_false
    intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases hin : i < n
    · have hik : i < k := by omega
      simp [hin, hpre i hik]
    · simp [hin]

theorem lowest_bit_flags (x k : ℕ) (hk : k < 64) (hbit : x.testBit k = true)
    (hpre : ∀ j < k, x.testBit j = false) :
    equalityFlags64 x 0 = k / 8 := by
  have h8 := lowest_bit_mod x k hbit hpre 8
  have h16 := lowest_bit_mod x k hbit hpre 16
  have h24 := lowest_bit_mod x k hbit hpre 24
  have h32 := lowest_bit_mod x k hbit hpre 32
  have h40 := lowest_bit_mod x k hbit hpre 40
  have h48 := lowest_bit_mod x k hbit hpre 48
  have h56 := lowest_bit_mod x k hbit hpre 56
  norm_num only [Nat.reducePow] at h8 h16 h24 h32 h40 h48 h56
  simp only [equalityFlags64, Nat.zero_mod, h8, h16, h24, h32, h40, h48, h56]
  split_ifs <;> omega

theorem xor_mod_zero (a b n : ℕ) :
    (a ^^^ b) % 2 ^ n = 0 ↔ a % 2 ^ n = b % 2 ^ n := by
  rw [← Nat.and_two_pow_sub_one_eq_mod (a ^^^ b) n, Nat.and_xor_distrib_right,
    Nat.and_two_pow_sub_one_eq_mod a n, Nat.and_two_pow_sub_one_eq_mod b n]
  exact Nat.xor_eq_zero_iff

theorem xor_equalityFlags64 (a b : ℕ) :
    equalityFlags64 (a ^^^ b) 0 = equalityFlags64 a b := by
  have h8 := xor_mod_zero a b 8
  have h16 := xor_mod_zero a b 16
  have h24 := xor_mod_zero a b 24
  have h32 := xor_mod_zero a b 32
  have h40 := xor_mod_zero a b 40
  have h48 := xor_mod_zero a b 48
  have h56 := xor_mod_zero a b 56
  norm_num only [Nat.reducePow] at h8 h16 h24 h32 h40 h48 h56
  simp only [equalityFlags64, Nat.zero_mod, h8, h16, h24, h32, h40, h48, h56]

theorem equalityFlags64_split (a b : ℕ) :
    equalityFlags64 a b =
      if a % 4294967296 = b % 4294967296 then
        4 + WordPrefix.prefixValue (a / 4294967296) (b / 4294967296)
      else WordPrefix.prefixValue (a % 4294967296) (b % 4294967296) := by
  have ha8 : a % 4294967296 % 256 = a % 256 := by omega
  have hb8 : b % 4294967296 % 256 = b % 256 := by omega
  have ha16 : a % 4294967296 % 65536 = a % 65536 := by omega
  have hb16 : b % 4294967296 % 65536 = b % 65536 := by omega
  have ha24 : a % 4294967296 % 16777216 = a % 16777216 := by omega
  have hb24 : b % 4294967296 % 16777216 = b % 16777216 := by omega
  by_cases h32 : a % 4294967296 = b % 4294967296
  · have h8 : a % 256 = b % 256 := by omega
    have h16 : a % 65536 = b % 65536 := by omega
    have h24 : a % 16777216 = b % 16777216 := by omega
    have h40 : (a % 1099511627776 = b % 1099511627776) ↔
        (a / 4294967296 % 256 = b / 4294967296 % 256) := by omega
    have h48 : (a % 281474976710656 = b % 281474976710656) ↔
        (a / 4294967296 % 65536 = b / 4294967296 % 65536) := by omega
    have h56 : (a % 72057594037927936 = b % 72057594037927936) ↔
        (a / 4294967296 % 16777216 = b / 4294967296 % 16777216) := by omega
    simp only [equalityFlags64, WordPrefix.prefixValue, h32, h8, h16, h24,
      ite_true, h40, h48, h56]
    omega
  · have h40 : a % 1099511627776 ≠ b % 1099511627776 := by omega
    have h48 : a % 281474976710656 ≠ b % 281474976710656 := by omega
    have h56 : a % 72057594037927936 ≠ b % 72057594037927936 := by omega
    simp only [equalityFlags64, WordPrefix.prefixValue, h32, h40, h48, h56,
      ite_false, ha8, hb8, ha16, hb16, ha24, hb24, Nat.add_zero]

end Gzip.Proofs.PrefixFlags
