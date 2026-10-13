import Gzip.Code.Funs
import Mathlib.Tactic.IntervalCases

open Aeneas Std Result
open Gzip.solution

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Gzip.Proofs.PrefixModel

def index64 (x : ℕ) : ℕ :=
  ((x &&& ((18446744073709551616 - x) % 18446744073709551616)) *
    285870213051386505 % 18446744073709551616) / 288230376151711744

theorem table_bound (k : ℕ) (hk : k < 64) : (CTZ64.val[k]!).val ≤ 63 := by
  interval_cases k <;> norm_num [CTZ64, Array.make]

theorem raw_spec (x y : U64) :
    prefix7 x y ⦃ r =>
      r.val = (if x.val ^^^ y.val = 0 then 7
        else (CTZ64.val[index64 (x.val ^^^ y.val)]!).val / 8) ∧ r.val ≤ 7 ⦄ := by
  unfold prefix7
  step as ⟨z, hz⟩
  have hzv : z.val = x.val ^^^ y.val := by rw [hz, UScalar.val_xor]
  split
  · rename_i hzero
    have hz0 : z.val = 0 := by have h := congrArg UScalar.val hzero; simpa using h
    simp only [WP.spec_ok]
    simp [← hzv, hz0]
  · rename_i hne
    step as ⟨wide, hwide⟩
    have hwv : wide.val = z.val := by
      rw [hwide, UScalar.cast_val_eq]
      norm_num
      have := z.hBounds
      scalar_tac
    step as ⟨negative, hnegative⟩
    step as ⟨neg, hneg⟩
    step as ⟨low, hlow⟩
    step as ⟨lowwide, hlowwide⟩
    have hlwv : lowwide.val = low.val := by
      rw [hlowwide, UScalar.cast_val_eq]
      norm_num
      have := low.hBounds
      scalar_tac
    step as ⟨product, hproduct⟩
    step as ⟨mixed, hmixed⟩
    step as ⟨shifted, hshifted⟩
    step as ⟨index, hindex⟩
    have hsb : shifted.val < 64 := by
      have hb := mixed.hBounds
      norm_num [U64.numBits_eq] at hb
      rw [hshifted, Nat.shiftRight_eq_div_pow]
      norm_num
      omega
    have hcast : index.val = shifted.val := by
      rw [hindex, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
    have hib : index.val < 64 := by rw [hcast]; exact hsb
    have hiv : index.val = index64 z.val := by
      rw [hcast, hshifted]
      simp only [Nat.shiftRight_eq_div_pow]
      rw [hmixed, UScalar.cast_val_eq, hproduct, hlwv, hlow, UScalar.val_and,
        hneg, UScalar.cast_val_eq, hnegative, hwv]
      norm_num [index64]
    step as ⟨entry, hentry⟩
    have heq : entry = CTZ64.val[index.val]! := by
      rw [hentry, ← getElem!_pos CTZ64.val index.val]
    have heb : entry.val ≤ 63 := by rw [heq]; exact table_bound index.val hib
    step as ⟨bytes, hbytes⟩
    try simp only [WP.spec_ok]
    have hnonzero : z.val ≠ 0 := by
      intro hz0
      apply hne
      exact (UScalar.eq_equiv _ _).mpr (by simpa using hz0)
    have hbb : bytes.val ≤ 7 := by rw [hbytes]; omega
    have hcastOut : (UScalar.cast .Usize bytes).val = bytes.val := by
      rw [UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      rcases System.Platform.numBits_eq with h | h <;> simp only [UScalarTy.numBits, h] <;> omega
    rw [hcastOut, hbytes]
    rw [← hzv, if_neg hnonzero, heq, hiv]
    exact ⟨rfl, by have := table_bound (index64 z.val) (by rw [← hiv]; exact hib); omega⟩


end Gzip.Proofs.PrefixModel
