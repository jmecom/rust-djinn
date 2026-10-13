import Gzip.Proofs.Decode.BaseTables

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.TablesImpl Gzip.Proofs.Decode.Encoding

namespace Gzip.Proofs.Decode.BaseImpl

set_option maxRecDepth 4096 in
theorem lengthBases_range : ∀ k : Fin 29, 3 ≤ lengthBases[k.val]! ∧ lengthBases[k.val]! ≤ 258 := by decide

set_option maxRecDepth 4096 in
theorem distanceBases_range : ∀ k : Fin 30, 1 ≤ distanceBases[k.val]! ∧ distanceBases[k.val]! ≤ 24577 := by decide

theorem lbase_range (k b : ℤ) (h : lbase_spec k b) : 3 ≤ b ∧ b ≤ 258 := by
  have he := lbase_values k b h
  rw [lbase_spec] at h
  have hk0 : 0 ≤ k := h.1
  have hk28 := (h.2 hk0).1
  rw [he]
  exact lengthBases_range ⟨k.toNat, by omega⟩

theorem dbase_range (k b : ℤ) (h : dbase_spec k b) : 1 ≤ b ∧ b ≤ 24577 := by
  have he := dbase_values k b h
  rw [dbase_spec] at h
  have hk0 : 0 ≤ k := h.1
  have hk29 := (h.2 hk0).1
  rw [he]
  exact distanceBases_range ⟨k.toNat, by omega⟩

theorem pow_two_le (e : Nat) (he : e ≤ 16) : 2 ^ e ≤ 65536 := by
  calc
    _ ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) he
    _ = _ := by norm_num

theorem shift_one (e : Nat) (he : e ≤ 16) : 1 <<< e % U32.size = 2 ^ e := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt]
  have hb := pow_two_le e he
  scalar_tac

@[step]
theorem length_base_correct (k : U32) (hk : k.val ≤ 28) :
    length_base k ⦃ b => lbase_spec k.val b.val ∧ 3 ≤ b.val ∧ b.val ≤ 258 ⦄ := by
  unfold length_base
  step*
  simp only [← getElem!_pos] at b_post
  have hival : i.val = k.val := by scalar_tac
  rw [hival] at b_post
  have ht := Gzip.Proofs.Decode.BaseTables.length_table k.val hk
  have he : (b.val : ℤ) = lengthBases[k.val]! := by
    interval_cases hv : k.val <;> simp_all [lengthBases, UScalar.cast_val_eq, Array.make]
  have hr := lbase_range _ _ ht
  exact ⟨he ▸ ht, by omega⟩

@[step]
theorem distance_base_correct (k : U32) (hk : k.val ≤ 29) :
    distance_base k ⦃ b => dbase_spec k.val b.val ∧ 1 ≤ b.val ∧ b.val ≤ 24577 ⦄ := by
  unfold distance_base
  step*
  simp only [← getElem!_pos] at b_post
  have hival : i.val = k.val := by scalar_tac
  rw [hival] at b_post
  have ht := Gzip.Proofs.Decode.BaseTables.distance_table k.val hk
  have he : (b.val : ℤ) = distanceBases[k.val]! := by
    interval_cases hv : k.val <;> simp_all [distanceBases, UScalar.cast_val_eq, Array.make]
  have hr := dbase_range _ _ ht
  exact ⟨he ▸ ht, by omega⟩

end Gzip.Proofs.Decode.BaseImpl
