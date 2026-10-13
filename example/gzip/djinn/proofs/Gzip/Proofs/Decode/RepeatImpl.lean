import Gzip.Proofs.Decode.CopyImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution

namespace Gzip.Proofs.Decode.RepeatImpl

def RepInv (prev : List U8) (value : U8) (count k : Usize) (out : alloc.vec.Vec U8) : Prop :=
  k.val ≤ count.val ∧ out.val = prev ++ List.replicate k.val value

theorem repeat_body (prev : List U8) (out : alloc.vec.Vec U8) (value : U8) (count k : Usize)
    (hcap : prev.length + count.val ≤ 320) (h : RepInv prev value count k out) :
    repeat_value_loop.body value count out k ⦃ z => match z with
      | .done v => v.val = prev ++ List.replicate count.val value
      | .cont (v, j) => RepInv prev value count j v ∧ count.val - j.val < count.val - k.val ⦄ := by
  obtain ⟨hk, ho⟩ := h
  have hsize : out.val.length = prev.length + k.val := by rw [ho]; simp
  unfold repeat_value_loop.body
  step*
  refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
  rw [all1_post, ho, k1_post, List.replicate_succ', List.append_assoc]

@[step]
theorem repeat_value_correct (out : alloc.vec.Vec U8) (value : U8) (count : Usize)
    (hcap : out.val.length + count.val ≤ 320) :
    repeat_value out value count ⦃ v => v.val = out.val ++ List.replicate count.val value ⦄ := by
  unfold repeat_value repeat_value_loop
  apply loop.spec_decr_nat (fun (_, k) => count.val - k.val)
    (fun (v, k) => RepInv out.val value count k v)
  · rintro ⟨v, k⟩ hinv
    apply WP.spec_mono (repeat_body out.val v value count k hcap hinv)
    intro z hz
    cases z <;> exact hz
  · exact ⟨by simp, by simp⟩

end Gzip.Proofs.Decode.RepeatImpl
