import Gzip.Proofs.Decode.ClImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution

namespace Gzip.Proofs.Decode.SliceImpl

def SliceInv (all : List U8) (start count k : Usize) (out : alloc.vec.Vec U8) : Prop :=
  k.val ≤ count.val ∧ out.val = (all.drop start.val).take k.val

theorem slice_body (all : Aeneas.Std.Slice U8) (start count k : Usize) (out : alloc.vec.Vec U8)
    (hb : start.val + count.val ≤ all.val.length) (hc : count.val ≤ 320)
    (h : SliceInv all.val start count k out) :
    table_slice_loop.body all start count out k ⦃ z => match z with
      | .done v => v.val = (all.val.drop start.val).take count.val
      | .cont (v, j) => SliceInv all.val start count j v ∧ count.val - j.val < count.val - k.val ⦄ := by
  obtain ⟨hk, ho⟩ := h
  have hsize : out.val.length = k.val := by
    rw [ho, List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
  unfold table_slice_loop.body
  step*
  refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
  have hlt : k.val < (all.val.drop start.val).length := by simp only [List.length_drop]; scalar_tac
  rw [out1_post, ho, k1_post, List.take_succ_eq_append_getElem hlt]
  congr 2
  rw [List.getElem_drop]
  simpa only [i_post] using i1_post

@[step]
theorem table_slice_correct (all : Aeneas.Std.Slice U8) (start count : Usize)
    (hb : start.val + count.val ≤ all.val.length) (hc : count.val ≤ 320) :
    table_slice all start count ⦃ v => v.val = (all.val.drop start.val).take count.val ⦄ := by
  unfold table_slice table_slice_loop
  apply loop.spec_decr_nat (fun (_, k) => count.val - k.val)
    (fun (v, k) => SliceInv all.val start count k v)
  · rintro ⟨v, k⟩ hinv
    apply WP.spec_mono (slice_body all start count k v hb hc hinv)
    intro z hz
    cases z <;> exact hz
  · exact ⟨by simp, by simp [alloc.vec.Vec.with_capacity]⟩

end Gzip.Proofs.Decode.SliceImpl
