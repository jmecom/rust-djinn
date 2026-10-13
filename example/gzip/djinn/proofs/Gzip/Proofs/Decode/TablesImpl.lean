import Gzip.Proofs.Decode.ReaderImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.Encoding

namespace Gzip.Proofs.Decode.TablesImpl

def LitInv (lens : alloc.vec.Vec U8) (i : I32) : Prop :=
  0 ≤ i.val ∧ i.val ≤ 288 ∧ (lens.val.length : ℤ) = i.val ∧
  ∀ k : Nat, k < lens.val.length → fixedlen_spec k (lens.val[k]!).val

theorem lit_body (lens : alloc.vec.Vec U8) (i : I32) (h : LitInv lens i) :
    fixed_lit_loop.body lens i ⦃ r => match r with
      | .done v => fixedlit_spec v.val
      | .cont (v, j) => LitInv v j ∧ (288 - j.val).toNat < (288 - i.val).toNat ⦄ := by
  obtain ⟨hi0, hi288, hlen, hvals⟩ := h
  unfold fixed_lit_loop.body
  step*
  case h2 =>
    refine ⟨trivial, by scalar_tac, ?_⟩
    intro k hk0 hk288
    exact ⟨(lens.val[k.toNat]!).val, by simpa only [Int.toNat_of_nonneg hk0] using hvals k.toNat (by scalar_tac), rfl⟩
  all_goals
    refine ⟨⟨by scalar_tac, by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
    · rw [lens1_post, List.length_append]
      simp only [List.length_singleton, Nat.cast_add, Nat.cast_one]
      omega
    · intro k hk
      rw [lens1_post] at hk ⊢
      by_cases hlt : k < lens.val.length
      · simpa only [List.getElem!_append_left _ _ _ hlt] using hvals k hlt
      · have he : k = lens.val.length := by simp only [List.length_append, List.length_singleton] at hk; omega
        subst k
        simp only [List.getElem!_append_right lens.val _ lens.val.length (Nat.le_refl _), Nat.sub_self, List.getElem!_cons_zero]
        unfold fixedlen_spec fixedlen_pre
        (try split_ifs) <;> scalar_tac

@[step]
theorem fixed_lit_correct : fixed_lit ⦃ lens => fixedlit_spec lens.val ⦄ := by
  unfold fixed_lit fixed_lit_loop
  apply loop.spec_decr_nat (fun (_, i) => (288 - i.val).toNat)
    (fun (lens, i) => LitInv lens i)
  · rintro ⟨lens, i⟩ hinv
    apply WP.spec_mono (lit_body lens i hinv)
    intro r hr
    cases r <;> exact hr
  · exact ⟨by decide, by decide, rfl, by simp⟩

def DistInv (lens : alloc.vec.Vec U8) (i : I32) : Prop :=
  0 ≤ i.val ∧ i.val ≤ 32 ∧ (lens.val.length : ℤ) = i.val ∧
  ∀ l ∈ lens.val, l.val = 5

theorem dist_body (lens : alloc.vec.Vec U8) (i : I32) (h : DistInv lens i) :
    fixed_dist_loop.body lens i ⦃ r => match r with
      | .done v => fixeddist_spec v.val
      | .cont (v, j) => DistInv v j ∧ (32 - j.val).toNat < (32 - i.val).toNat ⦄ := by
  obtain ⟨hi0, hi32, hlen, hvals⟩ := h
  unfold fixed_dist_loop.body
  step*
  · refine ⟨⟨by scalar_tac, by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
    · rw [lens1_post, List.length_append]
      simp only [List.length_singleton, Nat.cast_add, Nat.cast_one]
      omega
    · simpa only [lens1_post, List.mem_append, List.mem_singleton] using
        (show ∀ l, l ∈ lens.val ∨ l = 5#u8 → l.val = 5 from by
          intro l hl; rcases hl with hl | rfl; exact hvals l hl; rfl)
  · exact ⟨trivial, by scalar_tac, by intro l hl; exact_mod_cast hvals l hl⟩

@[step]
theorem fixed_dist_correct : fixed_dist ⦃ lens => fixeddist_spec lens.val ⦄ := by
  unfold fixed_dist fixed_dist_loop
  apply loop.spec_decr_nat (fun (_, i) => (32 - i.val).toNat)
    (fun (lens, i) => DistInv lens i)
  · rintro ⟨lens, i⟩ hinv
    apply WP.spec_mono (dist_body lens i hinv)
    intro r hr
    cases r <;> exact hr
  · exact ⟨by decide, by decide, rfl, by simp⟩

@[step]
theorem length_extra_correct (k : U32) (hk : k.val ≤ 28) :
    length_extra k ⦃ e => lextra_spec k.val e.val ∧ e.val ≤ 5 ⦄ := by
  unfold length_extra
  step*
  all_goals
    unfold lextra_spec lextra_pre
    (try split_ifs) <;> scalar_tac

@[step]
theorem distance_extra_correct (k : U32) (hk : k.val ≤ 29) :
    distance_extra k ⦃ e => dextra_spec k.val e.val ∧ e.val ≤ 13 ⦄ := by
  unfold distance_extra
  step*
  all_goals
    unfold dextra_spec dextra_pre
    (try split_ifs) <;> scalar_tac

end Gzip.Proofs.Decode.TablesImpl
