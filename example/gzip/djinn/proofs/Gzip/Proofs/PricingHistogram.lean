import Gzip.Proofs.Fused

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Plans Gzip.Proofs.Matches

set_option maxHeartbeats 3000000

namespace Gzip.Proofs.PricingHistogram

structure State (data : List U8) (stop : ℕ) (ls ds : List U16)
    (lit dist : alloc.vec.Vec Usize) (p t : Usize) : Prop where
  position : p.val ≤ stop ∧ stop ≤ data.length
  lengths : ls.length = ds.length
  index : t.val ≤ ls.length
  runs : Runs data stop p.val stop (ls.drop t.val) (ds.drop t.val)
  counts : Fused.Counts lit dist t.val

theorem body (data : Aeneas.Std.Slice U8) (stop : ℕ) (ls ds : alloc.vec.Vec U16)
    (lit dist : alloc.vec.Vec Usize) (p t : Usize)
    (hv : Symbolize.ValidPlan ls.val ds.val)
    (h : State data.val stop ls.val ds.val lit dist p t)
    (hsize : ls.val.length ≤ 1048576) :
    plan_histogram_loop.body data ls ds lit dist p t ⦃ r =>
      match r with
      | .done (lit', dist') => Fused.Counts lit' dist' ls.val.length
      | .cont (lit', dist', p', t') =>
          State data.val stop ls.val ds.val lit' dist' p' t' ∧ t'.val = t.val + 1 ⦄ := by
  obtain ⟨hp, hlen, ht, hr, hc⟩ := h
  unfold plan_histogram_loop.body
  dsimp only
  split
  · rename_i hlt
    have hlt' : t.val < ls.val.length := by scalar_tac
    obtain ⟨hstep, htail⟩ := Tokens.runs_head hr hlt' hlen
    have hpos := step_positive hstep
    have hpend := runs_bound htail
    step as ⟨rawlen, hlenget⟩
    step as ⟨len, hlcast⟩
    step as ⟨rawdist, hdistget⟩
    step as ⟨dd, hdcast⟩
    have hlget : len.val = (ls.val[t.val]!).val := by
      rw [hlcast]
      change (widen rawlen).val = _
      rw [widen_val, hlenget, getElem!_pos ls.val t.val hlt']
    have hdget : dd.val = (ds.val[t.val]!).val := by
      rw [hdcast]
      change (widen rawdist).val = _
      rw [widen_val, hdistget, getElem!_pos ds.val t.val (by omega)]
    simp only [Step] at hstep
    rw [← hlget, ← hdget] at hstep
    rw [← hlget] at htail hpos hpend
    obtain ⟨hz, hnz⟩ := hv.2 t.val hlt'
    rw [← hlget, ← hdget] at hz hnz
    have hpair : (if dd = 0#usize then ok (0#usize, 0#usize) else do
        let l ← length_code len
        let d ← distance_code dd
        ok (l, d)) ⦃ _ => True ⦄ := by
      split
      · simp only [WP.spec_ok]
      · rename_i hdn0
        have hdn : dd.val ≠ 0 := by scalar_tac
        obtain ⟨h3, h258, h1, h32⟩ := hnz hdn
        step as ⟨l, hl0, hl1, hl2⟩
        step as ⟨d, hd0, hd1, hd2⟩
        try simp only [WP.spec_ok]
    step as ⟨l, d⟩
    have hcs := Fused.count_spec data p dd l d lit dist t.val (by omega) (by omega) hc
    step as ⟨lit1, dist1, hc1⟩
    step as ⟨p1, hp1⟩
    step as ⟨t1, ht1⟩
    try simp only [WP.spec_ok]
    refine ⟨⟨⟨by omega, hp.2⟩, hlen, by omega, ?_, ?_⟩, ht1⟩
    · simpa only [hp1, ht1] using htail
    · rw [ht1]
      exact hc1
  · rename_i hge
    have he : t.val = ls.val.length := by scalar_tac
    simp only [WP.spec_ok]
    rw [← he]
    exact hc

@[step]
theorem loop (data : Aeneas.Std.Slice U8) (stop : ℕ) (ls ds : alloc.vec.Vec U16)
    (lit dist : alloc.vec.Vec Usize) (p t : Usize)
    (hv : Symbolize.ValidPlan ls.val ds.val)
    (h : State data.val stop ls.val ds.val lit dist p t)
    (hsize : ls.val.length ≤ 1048576) :
    plan_histogram_loop data ls ds lit dist p t ⦃ r => Fused.Counts r.1 r.2 ls.val.length ⦄ := by
  unfold plan_histogram_loop
  apply loop.spec_decr_nat (fun (_, _, _, j) => ls.val.length - j.val)
    (fun (lit', dist', p', t') => State data.val stop ls.val ds.val lit' dist' p' t')
  · rintro ⟨lit', dist', p', t'⟩ h'
    refine WP.spec_mono (body data stop ls ds lit' dist' p' t' hv h' hsize) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨lit'', dist'', p'', t''⟩ := state
        exact ⟨hr.1, by change ls.val.length - t''.val < ls.val.length - t'.val; have := hr.1.index; have := hr.2; omega⟩
  · exact h

theorem correct (data : Aeneas.Std.Slice U8) (start : Usize) (ls ds : alloc.vec.Vec U16) (stop : ℕ)
    (hr : Runs data.val stop start.val stop ls.val ds.val) (hd : stop ≤ data.val.length)
    (hsize : ls.val.length ≤ 1048576) :
    plan_histogram data start ls ds ⦃ r => r.1.val.length = 286 ∧ r.2.val.length = 30 ⦄ := by
  have hvalid := Symbolize.runs_valid hr
  unfold plan_histogram
  step as ⟨lit, hlit⟩
  step as ⟨dist, hdist⟩
  have hlen := runs_lengths hr
  have hstate : State data.val stop ls.val ds.val lit dist start 0#usize := by
    refine ⟨⟨runs_bound hr, hd⟩, hlen.1, by simp, by simpa using hr, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hlit, List.length_replicate]
    · rw [hdist, List.length_replicate]
    · intro i hi
      rw [hlit, List.getElem!_replicate] <;> scalar_tac
    · intro i hi
      rw [hdist, List.getElem!_replicate] <;> scalar_tac
  have hl := loop data stop ls ds lit dist start 0#usize hvalid hstate hsize
  step as ⟨lit1, dist1, hc⟩
  have h256 : (256 : ℕ) < lit1.val.length := by rw [hc.litLen]; omega
  step as ⟨i, hi⟩
  have hib : i.val ≤ ls.val.length := by rw [hi, ← getElem!_pos lit1.val 256 h256]; exact hc.litBound 256 (by omega)
  step as ⟨c, hcc⟩
  step as ⟨x, back, hx, hback⟩
  simp only [hback, alloc.vec.Vec.set_val_eq, List.length_set, WP.spec_ok]
  exact ⟨hc.litLen, hc.distLen⟩

end Gzip.Proofs.PricingHistogram
