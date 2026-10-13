/-  Proofs.lean — the implementer's file. Written once by `cargo djinn
    translate`, never overwritten. Replace every `sorry`; add any helper
    lemmas you need (loop invariants, bridging lemmas) in this file. -/
import Aeneas
import Broken.Spec
import Broken.Code.Funs

open Aeneas Std Result
open Broken.Spec

namespace Broken.Proofs

/-! ## max_ambiguous -/

theorem max_ambiguous.unambiguous :
    ∀ (list : List I32) (o₁ : I32) (o₂ : I32),
      max_ambiguous_spec list o₁ → max_ambiguous_spec list o₂ → o₁ = o₂ := by
  sorry

theorem max_ambiguous.impl_correct :
    ∀ (list : Aeneas.Std.Slice I32), max_ambiguous_pre list.val →
      Broken.spec.max_ambiguous list ⦃ r => max_ambiguous_spec list.val r ⦄ := by
  sorry

/-! ## abs_partial -/

theorem abs_partial.unambiguous :
    ∀ (i : I64) (o₁ : I64) (o₂ : I64),
      abs_partial_spec i o₁ → abs_partial_spec i o₂ → o₁ = o₂ := by
  sorry

theorem abs_partial.impl_correct :
    ∀ (i : I64), abs_partial_pre i →
      Broken.spec.abs_partial i ⦃ n => abs_partial_spec i n ⦄ := by
  sorry

/-! ## sorted_offbyone -/

theorem sorted_offbyone.unambiguous :
    ∀ (v : List I32) (o₁ : Bool) (o₂ : Bool),
      sorted_offbyone_spec v o₁ → sorted_offbyone_spec v o₂ → o₁ = o₂ := by
  sorry

theorem sorted_offbyone.wf :
    ∀ (v : List I32) (b : Bool),
      sorted_offbyone_spec v b →
      ∀ i : ℤ, 0 ≤ i → i < (v.length : ℤ) → (0 ≤ i ∧ i < (v.length : ℤ)) ∧ (0 ≤ (i + 1) ∧ (i + 1) < (v.length : ℤ)) := by
  sorry

theorem sorted_offbyone.impl_correct :
    ∀ (v : Aeneas.Std.Slice I32), sorted_offbyone_pre v.val →
      Broken.spec.sorted_offbyone v ⦃ b => sorted_offbyone_spec v.val b ⦄ := by
  sorry

/-! ## max_pos -/

theorem max_pos.unambiguous :
    ∀ (list : List I32) (o₁ : I32) (o₂ : I32),
      max_pos_spec list o₁ → max_pos_spec list o₂ → o₁ = o₂ := by
  sorry

theorem max_pos.ens_0 :
    ∀ (list : List I32) (r : I32),
      max_pos_spec list r → r.val > 0 := by
  sorry

theorem max_pos.impl_correct :
    ∀ (list : Aeneas.Std.Slice I32), max_pos_pre list.val →
      Broken.spec.max_pos list ⦃ r => max_pos_spec list.val r ⦄ := by
  sorry

/-! ## two_values -/

theorem two_values.unambiguous :
    ∀ (x : I32) (o₁ : I32) (o₂ : I32),
      two_values_spec x o₁ → two_values_spec x o₂ → o₁ = o₂ := by
  sorry

theorem two_values.impl_correct :
    ∀ (x : I32), two_values_pre x →
      Broken.spec.two_values x ⦃ r => two_values_spec x r ⦄ := by
  sorry

/-! ## clamp_ok -/

theorem clamp_ok.unambiguous :
    ∀ (x : I32) (lo : I32) (hi : I32) (o₁ : I32) (o₂ : I32),
      clamp_ok_spec x lo hi o₁ → clamp_ok_spec x lo hi o₂ → o₁ = o₂ := by
  sorry

theorem clamp_ok.impl_correct :
    ∀ (x : I32) (lo : I32) (hi : I32), clamp_ok_pre x lo hi →
      Broken.spec.clamp_ok x lo hi ⦃ r => clamp_ok_spec x lo hi r ⦄ := by
  sorry

end Broken.Proofs
