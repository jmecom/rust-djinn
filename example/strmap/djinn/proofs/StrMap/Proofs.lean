import Aeneas
import StrMap.Spec
import StrMap.Vocab
import StrMap.Code.Funs

open Aeneas Std Result
open StrMap.Spec
open Djinn.Vocab

namespace StrMap.Proofs

theorem byte_len.unambiguous :
    ∀ (s : List U8) (o₁ : Usize) (o₂ : Usize),
      byte_len_spec s o₁ → byte_len_spec s o₂ → o₁ = o₂ := by
  intro s o₁ o₂ h1 h2
  simp_all [byte_len_spec]
  apply UScalar.eq_of_val_eq; omega

theorem byte_len.impl_correct :
    ∀ (s : String), byte_len_pre (Djinn.Vocab.bytes s) →
      StrMap.spec.byte_len s ⦃ r => byte_len_spec (Djinn.Vocab.bytes s) r ⦄ := by
  intro s hpre
  unfold StrMap.spec.byte_len StrMap.solution.byte_len alloc.string.String.len
  split
  · rename_i h
    simp [byte_len_spec, byte_len_pre, h]
  · rename_i h
    exfalso
    simp [byte_len_pre] at hpre
    omega

theorem has_key.unambiguous :
    ∀ (m : List (U32 × U64)) (k : U32) (o₁ : Bool) (o₂ : Bool),
      has_key_spec m k o₁ → has_key_spec m k o₂ → o₁ = o₂ := by
  intro m k o₁ o₂ h1 h2
  simp_all [has_key_spec]

theorem has_key.impl_correct :
    ∀ (m : std.collections.hash.map.HashMap U32 U64 std.hash.random.RandomState Global) (k : U32), has_key_pre m.entries k →
      StrMap.spec.has_key m k ⦃ r => has_key_spec m.entries k r ⦄ := by
  intro m k hpre
  unfold StrMap.spec.has_key StrMap.solution.has_key std.collections.hash.map.HashMap.contains_key
  rw [Djinn.Vocab.find_eq _ _ (by intro x; rfl) (by intro a b; rfl)]
  simp [has_key_pre] at hpre
  simp [has_key_spec, has_key_pre, Djinn.Vocab.mapGet]
  omega

theorem lookup.unambiguous :
    ∀ (m : List (U32 × U64)) (k : U32) (o₁ : Option U64) (o₂ : Option U64),
      lookup_spec m k o₁ → lookup_spec m k o₂ → o₁ = o₂ := by
  intro m k o₁ o₂ h1 h2
  simp_all [lookup_spec]

theorem lookup.impl_correct :
    ∀ (m : std.collections.hash.map.HashMap U32 U64 std.hash.random.RandomState Global) (k : U32), lookup_pre m.entries k →
      StrMap.spec.lookup m k ⦃ r => lookup_spec m.entries k r ⦄ := by
  intro m k hpre
  unfold StrMap.spec.lookup StrMap.solution.lookup std.collections.hash.map.HashMap.get core.option.OptionShared0T.copied
  rw [Djinn.Vocab.find_eq _ _ (by intro x; rfl) (by intro a b; rfl)]
  simp [lookup_pre] at hpre
  simp [lookup_spec, lookup_pre, Djinn.Vocab.mapGet]
  omega

/-! ## obligations added by a later `translate` (specification changed) -/

theorem lookup_next.unambiguous :
    ∀ (m : List (U32 × U64)) (k : U32) (o₁ : Option U64) (o₂ : Option U64),
      lookup_next_spec m k o₁ → lookup_next_spec m k o₂ → o₁ = o₂ := by
  intro m k o₁ o₂ h1 h2
  obtain ⟨_, v1, hv1, rfl⟩ := h1
  obtain ⟨_, v2, hv2, rfl⟩ := h2
  rw [hv1] at hv2
  simp_all

/-- The ambient function, as a relation: one result, with its value. -/
theorem bump_spec (k : U32) :
    ∃ z, StrMap.spec.bump k = ok z ∧ (z.val = if k.val < 1000000 then k.val + 1 else k.val) := by
  unfold StrMap.spec.bump
  split
  · rename_i hlt
    have h := UScalar.add_spec (x := k) (y := 1#u32) (by scalar_tac)
    rw [Aeneas.Std.WP.spec_equiv_exists] at h
    obtain ⟨z, hz, hzv⟩ := h
    refine ⟨z, hz, ?_⟩
    simp at hzv
    have : k.val < 1000000 := by scalar_tac
    simp [this, hzv]
  · rename_i hge
    refine ⟨k, rfl, ?_⟩
    have : ¬ k.val < 1000000 := by scalar_tac
    simp [this]

theorem lookup_next.impl_correct :
    ∀ (m : std.collections.hash.map.HashMap U32 U64 std.hash.random.RandomState Global) (k : U32), lookup_next_pre m.entries k →
      StrMap.spec.lookup_next m k ⦃ r => lookup_next_spec m.entries k r ⦄ := by
  intro m k hpre
  simp [lookup_next_pre] at hpre
  obtain ⟨z, hz, _⟩ := bump_spec k
  unfold StrMap.spec.lookup_next StrMap.solution.lookup_next
  simp only [hz, bind_ok]
  unfold std.collections.hash.map.HashMap.get core.option.OptionShared0T.copied
  have hf := Djinn.Vocab.find_eq (V := U64) core.borrow.Borrow.Blanket.borrow
    (liftFun2 core.cmp.impls.PartialEqU32.eq) (by intro x; rfl) (by intro a b; rfl) m.entries z
  rw [hf]
  simp [lookup_next_spec, lookup_next_pre, Djinn.Vocab.mapGet, hpre, hz]

end StrMap.Proofs
