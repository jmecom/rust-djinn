/-  Proofs.lean — the implementer's file. Written once by `cargo djinn
    translate`, never overwritten. Replace every `sorry`; add any helper
    lemmas you need (loop invariants, bridging lemmas) in this file. -/
import Aeneas
import ClampDemo.Spec
import ClampDemo.Vocab
import ClampDemo.Code.Funs

open Aeneas Std Result
open ClampDemo.Spec
open Djinn.Vocab

namespace ClampDemo.Proofs

/-! ## clamp -/

theorem clamp.unambiguous :
    ∀ (x : I32) (lo : I32) (hi : I32) (o₁ : I32) (o₂ : I32),
      clamp_spec x lo hi o₁ → clamp_spec x lo hi o₂ → o₁ = o₂ := by
  intro x lo hi o₁ o₂ h₁ h₂
  obtain ⟨_, _, hl₁, hh₁, hm₁⟩ := h₁
  obtain ⟨_, _, hl₂, hh₂, hm₂⟩ := h₂
  by_cases hl : x.val < lo.val
  · exact (hl₁ hl).trans (hl₂ hl).symm
  by_cases hh : x.val > hi.val
  · exact (hh₁ hh).trans (hh₂ hh).symm
  exact (hm₁ (by omega)).trans (hm₂ (by omega)).symm

/-! ## count_negative -/

theorem count_negative.unambiguous :
    ∀ (v : List I32) (o₁ : Usize) (o₂ : Usize),
      count_negative_spec v o₁ → count_negative_spec v o₂ → o₁ = o₂ := by
  intro v o₁ o₂ h₁ h₂
  apply UScalar.eq_of_val_eq
  have h₁ := h₁.2
  have h₂ := h₂.2
  omega

/-! ## min -/

theorem min.unambiguous :
    ∀ (a : I32) (b : I32) (o₁ : I32) (o₂ : I32),
      min_spec a b o₁ → min_spec a b o₂ → o₁ = o₂ := by
  intro a b o₁ o₂ h₁ h₂
  obtain ⟨_, ha₁, hb₁, rfl | rfl⟩ := h₁
  all_goals obtain ⟨_, ha₂, hb₂, rfl | rfl⟩ := h₂
  all_goals apply IScalar.eq_of_val_eq; omega

/-! ## max -/

theorem max.unambiguous :
    ∀ (a : I32) (b : I32) (o₁ : I32) (o₂ : I32),
      max_spec a b o₁ → max_spec a b o₂ → o₁ = o₂ := by
  intro a b o₁ o₂ h₁ h₂
  obtain ⟨_, ha₁, hb₁, rfl | rfl⟩ := h₁
  all_goals obtain ⟨_, ha₂, hb₂, rfl | rfl⟩ := h₂
  all_goals apply IScalar.eq_of_val_eq; omega

theorem clamp.impl_correct (x lo hi : I32) (h : clamp_pre x lo hi) :
    ClampDemo.spec.clamp x lo hi ⦃ r => clamp_spec x lo hi r ⦄ := by
  unfold ClampDemo.spec.clamp ClampDemo.solution.clamp
  simp only [clamp_pre] at h
  split <;> (try split) <;> step* <;>
    simp_all [clamp_spec, clamp_pre, IScalar.lt_equiv] <;> omega

theorem min.impl_correct (a b : I32) (h : min_pre a b) :
    ClampDemo.spec.min a b ⦃ r => min_spec a b r ⦄ := by
  unfold ClampDemo.spec.min ClampDemo.solution.min
  split <;> step* <;> simp_all [min_spec, min_pre, IScalar.le_equiv] <;> omega

theorem max.impl_correct (a b : I32) (h : max_pre a b) :
    ClampDemo.spec.max a b ⦃ r => max_spec a b r ⦄ := by
  unfold ClampDemo.spec.max ClampDemo.solution.max
  split <;> step* <;> simp_all [max_spec, max_pre, IScalar.le_equiv] <;> omega

def CountInv (v : Aeneas.Std.Slice I32) (count i : Usize) : Prop :=
  i.val ≤ v.val.length ∧
  count.val = (v.val.take i.val).countP (fun y => decide (y.val < 0))

theorem count_body (v : Aeneas.Std.Slice I32) (count i : Usize)
    (h : CountInv v count i) :
    ClampDemo.solution.count_negative_loop.body v count i ⦃ r =>
      match r with
      | .done c => count_negative_spec v.val c
      | .cont s => CountInv v s.1 s.2 ∧ v.val.length - s.2.val < v.val.length - i.val ⦄ := by
  obtain ⟨hi, hc⟩ := h
  have hci : count.val ≤ i.val := by
    have := List.countP_le_length (p := fun y : I32 => decide (y.val < 0))
      (l := v.val.take i.val)
    simp only [List.length_take] at this
    omega
  unfold ClampDemo.solution.count_negative_loop.body
  step*
  · rename_i hlt
    have hil : i.val < v.val.length := by
      simpa only [UScalar.lt_equiv, Slice.len_val, Slice.length] using hlt
    have ht : (v.val.take (i.val + 1)).countP (fun y => decide (y.val < 0)) =
        count.val + if i2.val < 0 then 1 else 0 := by
      rw [List.take_add_one, List.countP_append]
      simp [List.getElem?_eq_getElem hil, ← hc, i2_post]
    split
    · step* <;> try scalar_tac
      all_goals simp_all [CountInv, IScalar.lt_equiv] <;> omega
    · step* <;> try scalar_tac
      all_goals simp_all [CountInv, IScalar.lt_equiv] <;> omega
  · rename_i hstop
    have he : i.val = v.val.length := by
      simp only [UScalar.lt_equiv, Slice.len_val, Slice.length] at hstop
      omega
    simp only [he, List.take_length] at hc
    exact ⟨trivial, by omega⟩

theorem count_negative.impl_correct (v : Aeneas.Std.Slice I32)
    (_h : count_negative_pre v.val) :
    ClampDemo.spec.count_negative v ⦃ r => count_negative_spec v.val r ⦄ := by
  unfold ClampDemo.spec.count_negative ClampDemo.solution.count_negative
    ClampDemo.solution.count_negative_loop
  apply loop.spec_decr_nat (fun (_, i) => v.val.length - i.val)
    (fun (count, i) => CountInv v count i)
  · rintro ⟨count, i⟩ hinv
    simp only at hinv ⊢
    refine Aeneas.Std.WP.spec_mono (count_body v count i hinv) ?_
    intro r hr
    cases r <;> exact hr
  · simp [CountInv]

end ClampDemo.Proofs
