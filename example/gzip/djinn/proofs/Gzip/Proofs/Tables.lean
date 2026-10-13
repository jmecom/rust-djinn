import Gzip.Proofs.Indices
import Gzip.Proofs.Bits

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Indices Gzip.Proofs.Writer

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Gzip.Proofs.Tables

def lengthCode (len : ℕ) : ℕ := (LENGTH_CODE.val[len]!).val
def distLow (d : ℕ) : ℕ := (DIST_CODE_LOW.val[d]!).val
def distHigh (k : ℕ) : ℕ := (DIST_CODE_HIGH.val[k]!).val

unseal LENGTH_CODE LENGTH_BASE LENGTH_EXTRA in
theorem length_table : ∀ len : Fin 259, 3 ≤ len.val →
    lengthCode len.val ≤ 28 ∧ lb (lengthCode len.val) ≤ len.val ∧
      len.val - lb (lengthCode len.val) < 2 ^ le (lengthCode len.val) := by
  decide

unseal DIST_CODE_LOW DIST_BASE DIST_EXTRA in
theorem dist_low_table : ∀ d : Fin 257, 1 ≤ d.val →
    distLow d.val ≤ 29 ∧ db (distLow d.val) ≤ d.val ∧
      d.val - db (distLow d.val) < 2 ^ de (distLow d.val) := by
  decide

unseal DIST_CODE_HIGH DIST_BASE DIST_EXTRA in
theorem dist_high_table : ∀ k : Fin 256, 2 ≤ k.val →
    distHigh k.val ≤ 29 ∧ db (distHigh k.val) ≤ 128 * k.val + 1 ∧
      128 * k.val + 128 < db (distHigh k.val) + 2 ^ de (distHigh k.val) := by
  decide

theorem length_code_len : LENGTH_CODE.val.length = 259 := by
  simp [LENGTH_CODE, Array.make]

theorem dist_low_len : DIST_CODE_LOW.val.length = 257 := by
  simp [DIST_CODE_LOW, Array.make]

theorem dist_high_len : DIST_CODE_HIGH.val.length = 256 := by
  simp [DIST_CODE_HIGH, Array.make]

@[step]
theorem length_code_spec (len : Usize) (h3 : 3 ≤ len.val) (h258 : len.val ≤ 258) :
    length_code len ⦃ l => l.val ≤ 28 ∧ lb l.val ≤ len.val ∧ len.val - lb l.val < 2 ^ le l.val ⦄ := by
  unfold length_code
  have hlt : len < 259#usize := by scalar_tac
  rw [if_pos hlt]
  step as ⟨i, hi⟩
  have ht := length_table ⟨len.val, by omega⟩ h3
  simp only [Fin.val_mk] at ht
  have hi' : i.val = lengthCode len.val := by
    rw [hi, lengthCode, getElem!_pos LENGTH_CODE.val len.val (by rw [length_code_len]; omega)]
  have hc : (UScalar.cast .Usize i).val = i.val := by scalar_tac
  simp only [hc, hi']
  exact ht

@[step]
theorem distance_code_spec (dist : Usize) (h1 : 1 ≤ dist.val) (h32 : dist.val ≤ 32768) :
    distance_code dist ⦃ d => d.val ≤ 29 ∧ db d.val ≤ dist.val ∧ dist.val - db d.val < 2 ^ de d.val ⦄ := by
  unfold distance_code
  split
  · rename_i hlt
    have hlt' : dist.val < 257 := by scalar_tac
    step as ⟨i, hi⟩
    have ht := dist_low_table ⟨dist.val, hlt'⟩ h1
    simp only [Fin.val_mk] at ht
    have hi' : i.val = distLow dist.val := by
      rw [hi, distLow, getElem!_pos DIST_CODE_LOW.val dist.val (by rw [dist_low_len]; omega)]
    have hc : (UScalar.cast .Usize i).val = i.val := by scalar_tac
    simp only [hc, hi']
    exact ht
  · rename_i hge
    have hge' : 257 ≤ dist.val := by scalar_tac
    have hlt : dist < 32769#usize := by scalar_tac
    rw [if_pos hlt]
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    case hy => rcases System.Platform.numBits_eq with h | h <;> simp [h]
    have hk : i1.val = (dist.val - 1) / 128 := by
      rw [hi1, Nat.shiftRight_eq_div_pow, hi]
    have hk2 : 2 ≤ i1.val := by rw [hk]; omega
    have hk256 : i1.val < 256 := by rw [hk]; omega
    step as ⟨i2, hi2⟩
    have ht := dist_high_table ⟨i1.val, hk256⟩ hk2
    simp only [Fin.val_mk] at ht
    have hi2' : i2.val = distHigh i1.val := by
      rw [hi2, distHigh, getElem!_pos DIST_CODE_HIGH.val i1.val (by rw [dist_high_len]; omega)]
    have hc : (UScalar.cast .Usize i2).val = i2.val := by scalar_tac
    simp only [hc, hi2']
    have hlo : 128 * i1.val + 1 ≤ dist.val := by rw [hk]; omega
    have hhi : dist.val ≤ 128 * i1.val + 128 := by rw [hk]; omega
    exact ⟨ht.1, by omega, by omega⟩

@[step]
theorem reverse_code_spec (value count : U32) (hc : count.val ≤ 16) :
    reverse_code value count ⦃ r => r.val = reverse16 value.val / 2 ^ (16 - count.val) ⦄ := by
  unfold reverse_code
  step*
  simp only [r_post, i_post, i1_post, i2_post, i3_post, v_post, i4_post, i5_post, i6_post, i7_post, v1_post,
    i8_post, i9_post, i10_post, i11_post, v2_post, i12_post, i13_post, i14_post, i15_post, v3_post,
    i16_post, UScalar.val_and, UScalar.val_or, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, U32.size,
    U32.numBits_eq, reverse16, reverseStage]
  rfl

end Gzip.Proofs.Tables
