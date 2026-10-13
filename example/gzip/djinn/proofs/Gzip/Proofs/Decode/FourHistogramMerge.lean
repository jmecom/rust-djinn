import Gzip.Proofs.Decode.FourHistogramFacts

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.FourHistogramFacts

namespace Gzip.Proofs.Decode.FourHistogramMerge

def FinalSeen (lens : List U8) (a : Array U32 16#usize) : Prop :=
  ∀ m : Nat, m < 16 → earlier_spec lens lens.length m (a.val[m]!).val ∧
    (a.val[m]!).val ≤ lens.length

theorem merge_body (lens : Aeneas.Std.Slice U8) (a b c d : Array U32 16#usize) (n : Usize)
    (hl : lens.val.length ≤ 320) (hn : n.val ≤ 16)
    (h : MergeSeen lens.val a.val b.val c.val d.val n.val) :
    codeword_table_loop2.body b c d a n ⦃ r => match r with
    | .done v => FinalSeen lens.val v
    | .cont (v, j) => j.val ≤ 16 ∧ MergeSeen lens.val v.val b.val c.val d.val j.val ∧
        16 - j.val < 16 - n.val ⦄ := by
  unfold codeword_table_loop2.body
  split
  · rename_i hlt
    have hn16 : n.val < 16 := by scalar_tac
    have hbin := h n.val hn16
    rw [if_neg (by omega : ¬ n.val < n.val)] at hbin
    have hsum := hbin.2
    unfold total4 at hsum
    step as ⟨v0, hv0⟩
    have he0 : v0 = b.val[n.val]! := by
      rw [Djinn.Vocab.val_getElem! b.val n.val (by scalar_tac)]; exact hv0
    step as ⟨v1, hv1⟩
    have he1 : v1 = c.val[n.val]! := by
      rw [Djinn.Vocab.val_getElem! c.val n.val (by scalar_tac)]; exact hv1
    rw [← he0, ← he1] at hsum
    step as ⟨v2, hv2⟩
    all_goals try scalar_tac
    step as ⟨v3, hv3⟩
    have he3 : v3 = d.val[n.val]! := by
      rw [Djinn.Vocab.val_getElem! d.val n.val (by scalar_tac)]; exact hv3
    rw [← he3] at hsum
    step as ⟨v4, hv4⟩
    all_goals try scalar_tac
    step as ⟨v5, hv5⟩
    have he5 : v5 = a.val[n.val]! := by
      rw [Djinn.Vocab.val_getElem! a.val n.val (by scalar_tac)]; exact hv5
    rw [← he5] at hsum
    step as ⟨v6, hv6⟩
    all_goals try scalar_tac
    have hv6' : v6.val = total4 a.val b.val c.val d.val n.val := by
      simp only [total4, ← he0, ← he1, ← he3, ← he5]
      scalar_tac
    step as ⟨a', ha'⟩
    step as ⟨n', hn'⟩
    all_goals try scalar_tac
    try rw [WP.spec_ok]
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    intro m hm
    rw [ha', Array.set_val_eq]
    have hj : n'.val = n.val + 1 := by scalar_tac
    rw [hj]
    by_cases he : m = n.val
    · subst m
      rw [if_pos (by omega : n.val < n.val + 1),
        Djinn.Vocab.getElem!_set _ _ _ _ (by scalar_tac), if_pos rfl, hv6']
      exact hbin
    · have hkeep : (a.val.set n.val v6)[m]! = a.val[m]! := by
        rw [Djinn.Vocab.getElem!_set _ _ _ _ (by scalar_tac), if_neg he]
      have hprev := h m hm
      by_cases hmn : m < n.val
      · rw [if_pos (by omega : m < n.val + 1), hkeep]
        simpa only [if_pos hmn] using hprev
      · rw [if_neg (by omega : ¬ m < n.val + 1)]
        simpa only [total4, hkeep, if_neg hmn] using hprev
  · rw [WP.spec_ok]
    have he : n.val = 16 := by scalar_tac
    intro m hm
    have hprev := h m hm
    simpa only [if_pos (by omega : m < n.val)] using hprev

theorem merge_loop_correct (lens : Aeneas.Std.Slice U8) (a b c d : Array U32 16#usize) (n : Usize)
    (hl : lens.val.length ≤ 320) (hn : n.val ≤ 16)
    (h : MergeSeen lens.val a.val b.val c.val d.val n.val) :
    codeword_table_loop2 a b c d n ⦃ v => FinalSeen lens.val v ⦄ := by
  unfold codeword_table_loop2
  apply loop.spec_decr_nat (fun (_, j) => 16 - j.val)
    (fun (v, j) => j.val ≤ 16 ∧ MergeSeen lens.val v.val b.val c.val d.val j.val)
  · rintro ⟨v, j⟩ ⟨hj, hinv⟩
    apply WP.spec_mono (merge_body lens v b c d j hl hj hinv)
    intro r hr
    cases r with
    | done z => exact hr
    | cont z =>
      rcases z with ⟨v', j'⟩
      exact ⟨⟨hr.1, hr.2.1⟩, hr.2.2⟩
  · exact ⟨hn, h⟩

end Gzip.Proofs.Decode.FourHistogramMerge
