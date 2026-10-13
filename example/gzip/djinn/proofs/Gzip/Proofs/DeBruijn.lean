import Gzip.Proofs.LowBit
import Gzip.Proofs.PrefixFlags

open Aeneas Std

set_option maxHeartbeats 0

namespace Gzip.Proofs.DeBruijn

def counts64 : List ℕ :=
  [0, 1, 48, 2, 57, 49, 28, 3, 61, 58, 50, 42, 38, 29, 17, 4,
    62, 55, 59, 36, 53, 51, 43, 22, 45, 39, 33, 30, 24, 18, 12, 5,
    63, 47, 56, 27, 60, 41, 37, 16, 54, 35, 52, 21, 44, 32, 23, 11,
    46, 26, 40, 15, 34, 20, 31, 10, 25, 14, 19, 9, 13, 8, 7, 6]

def flags64 (x : ℕ) : ℕ :=
  (if x % 256 = 0 then 1 else 0) +
  (if x % 65536 = 0 then 1 else 0) +
  (if x % 16777216 = 0 then 1 else 0) +
  (if x % 4294967296 = 0 then 1 else 0) +
  (if x % 1099511627776 = 0 then 1 else 0) +
  (if x % 281474976710656 = 0 then 1 else 0) +
  (if x % 72057594037927936 = 0 then 1 else 0)

def index64 (x : ℕ) : ℕ :=
  ((x &&& ((18446744073709551616 - x) % 18446744073709551616)) *
    285870213051386505 % 18446744073709551616) / 288230376151711744

theorem index64_lt (x : ℕ) : index64 x < 64 := by
  unfold index64
  have hm := Nat.mod_lt ((x &&& ((18446744073709551616 - x) %
    18446744073709551616)) * 285870213051386505)
      (by decide : 0 < 18446744073709551616)
  omega

theorem counts64_bound (i : ℕ) (hi : i < 64) : counts64[i]! < 64 := by
  interval_cases i <;> decide

theorem bytesNat64 (x : ℕ) (hx : x < 18446744073709551616) (hne : x ≠ 0) :
    counts64[index64 x]! / 8 = flags64 x := by
  let xb := BitVec.ofNat 64 x
  have hxv : xb.toNat = x := by
    simp only [xb, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hx
  have hxb : xb ≠ 0 := by
    intro he
    have hz := congrArg BitVec.toNat he
    change xb.toNat = 0 at hz
    rw [hxv] at hz
    exact hne hz
  obtain ⟨k, hk, hiso, hbit, hpre⟩ := isolated64 xb hxb
  rw [hxv] at hbit hpre
  have hlow := congrArg BitVec.toNat hiso
  simp only [BitVec.toNat_and, BitVec.toNat_neg, BitVec.toNat_ofNat, hxv] at hlow
  norm_num only [Nat.reducePow] at hlow
  have hf := PrefixFlags.lowest_bit_flags x k hk hbit hpre
  have hf' : flags64 x = k / 8 := by
    simpa only [flags64, PrefixFlags.equalityFlags64, Nat.zero_mod] using hf
  rw [hf']
  unfold index64
  rw [hlow]
  interval_cases k <;> decide

end Gzip.Proofs.DeBruijn
