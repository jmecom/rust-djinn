/-  Obligations.lean — what `cargo djinn verify` would regenerate. TRUSTED.
    Each theorem is pinned by its type and takes its proof from `Calib.Proofs`
    by name. Names of the translated functions come from translation.json. -/
import Calib.Spec
import Calib.Code.Funs
import Calib.Proofs

open Aeneas Std
open Calib.Spec

namespace Calib.Obligations

/-! ### perm  (rel, total) -/

theorem perm.exists :
    ∀ (list : List I32), perm_pre list → ∃ t, perm_spec list t :=
  Calib.Proofs.perm.exists

/-! ### sort  (func) -/

theorem sort.unambiguous :
    ∀ (v_old o₁ o₂ : List I32),
      sort_spec v_old o₁ → sort_spec v_old o₂ → o₁ = o₂ :=
  Calib.Proofs.sort.unambiguous

theorem sort.wf :
    ∀ (v_old v : List I32), sort_spec v_old v →
      ∀ i : ℤ, 0 ≤ i → i < (v.length : ℤ) - 1 →
        (0 ≤ i ∧ i < (v.length : ℤ)) ∧ (0 ≤ i + 1 ∧ i + 1 < (v.length : ℤ)) :=
  Calib.Proofs.sort.wf

theorem sort.impl_correct :
    ∀ (v : alloc.vec.Vec I32), sort_pre v.val →
      Calib.sort v ⦃ v' => sort_spec v.val v'.val ⦄ :=
  Calib.Proofs.sort.impl_correct

theorem sort.exists :
    ∀ (v : alloc.vec.Vec I32), sort_pre v.val → ∃ v', sort_spec v.val v' := by
  intro v h
  have hs := sort.impl_correct v h
  rw [Aeneas.Std.WP.spec_equiv_exists] at hs
  obtain ⟨v', _, h2⟩ := hs
  exact ⟨_, h2⟩

/-! ### max  (func) -/

theorem max.unambiguous :
    ∀ (list : List I32) (r₁ r₂ : I32),
      max_spec list r₁ → max_spec list r₂ → r₁ = r₂ :=
  Calib.Proofs.max.unambiguous

theorem max.ens_0 :
    ∀ (list : List I32) (r : I32), max_spec list r → r ∈ list :=
  Calib.Proofs.max.ens_0

theorem max.impl_correct :
    ∀ (list : Aeneas.Std.Slice I32), max_pre list.val →
      Calib.max list ⦃ r => max_spec list.val r ⦄ :=
  Calib.Proofs.max.impl_correct

theorem max.exists :
    ∀ (list : Aeneas.Std.Slice I32), max_pre list.val → ∃ r, max_spec list.val r := by
  intro list h
  have hs := max.impl_correct list h
  rw [Aeneas.Std.WP.spec_equiv_exists] at hs
  obtain ⟨r, _, h2⟩ := hs
  exact ⟨_, h2⟩

end Calib.Obligations
