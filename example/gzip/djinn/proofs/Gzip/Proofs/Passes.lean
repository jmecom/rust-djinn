import Gzip.Proofs.Dp
import Gzip.Proofs.Greedy
import Gzip.Proofs.Symbolize
import Gzip.Proofs.Histogram
import Gzip.Proofs.Fused
import Gzip.Proofs.PricingHistogram
import Gzip.Proofs.Canon

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Plans Gzip.Proofs.Dp

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Gzip.Proofs.Passes

/-- Every entry of a list of prices is at most 15. -/
def Small (v : List U32) : Prop := ∀ k < v.length, (v[k]!).val ≤ 15

theorem small_nil : Small [] := by
  intro k hk
  simp at hk

theorem small_append {v : List U32} (h : Small v) (x : U32) (hx : x.val ≤ 15) : Small (v ++ [x]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  by_cases hkv : k < v.length
  · rw [List.getElem!_append_left v [x] k hkv]
    exact h k hkv
  · have he : k = v.length := by omega
    subst he
    rw [List.getElem!_append_right v [x] v.length (Nat.le_refl _)]
    simpa using hx

-- ================================================================ a block's own price list

theorem code0_body (lit : Code) (lcost : alloc.vec.Vec U32) (i : Usize)
    (hi : i.val ≤ 286) (hlen : lcost.val.length = i.val) (hsmall : Small lcost.val) :
    code_costs_loop0.body lit lcost i ⦃ r =>
      match r with
      | .done v => v.val.length = 286 ∧ Small v.val
      | .cont (v, j) => j.val = i.val + 1 ∧ j.val ≤ 286 ∧ v.val.length = j.val ∧ Small v.val ⦄ := by
  unfold code_costs_loop0.body
  split
  · dsimp only
    have hxSpec : (if i < alloc.vec.Vec.len lit.lens then do
        let i2 ← alloc.vec.Vec.index_usize lit.lens i
        ok (UScalar.cast .U32 i2)
      else ok 0#u32) ⦃ x => x.val < 256 ⦄ := by
      split
      · step as ⟨i2, hi2⟩
        try simp only [WP.spec_ok]
        scalar_tac
      · step*
    step as ⟨x, hx⟩
    split
    · step*
      refine ⟨i2_post, by scalar_tac, ?_, ?_⟩
      · rw [lcost1_post, List.length_append, List.length_singleton, i2_post, hlen]
      · rw [lcost1_post]; exact small_append hsmall _ (by simp)
    · split
      · step*
        refine ⟨i2_post, by scalar_tac, ?_, ?_⟩
        · rw [lcost1_post, List.length_append, List.length_singleton, i2_post, hlen]
        · rw [lcost1_post]; exact small_append hsmall _ (by simp)
      · step*
        refine ⟨i2_post, by scalar_tac, ?_, ?_⟩
        · rw [lcost1_post, List.length_append, List.length_singleton, i2_post, hlen]
        · rw [lcost1_post]; exact small_append hsmall _ (by scalar_tac)
  · step*

theorem code0_loop (lit : Code) (lcost : alloc.vec.Vec U32) (i : Usize)
    (hi : i.val ≤ 286) (hlen : lcost.val.length = i.val) (hsmall : Small lcost.val) :
    code_costs_loop0 lit lcost i ⦃ v => v.val.length = 286 ∧ Small v.val ⦄ := by
  unfold code_costs_loop0
  apply loop.spec_decr_nat (fun (_, j) => 286 - j.val)
    (fun (v, j) => j.val ≤ 286 ∧ v.val.length = j.val ∧ Small v.val)
  · rintro ⟨v, j⟩ ⟨hj, hvl, hvs⟩
    refine WP.spec_mono (code0_body lit v j hj hvl hvs) ?_
    intro r hr
    cases r with
    | done v => exact hr
    | cont state =>
        obtain ⟨v', j'⟩ := state
        obtain ⟨he, hj', hl', hs'⟩ := hr
        exact ⟨⟨hj', hl', hs'⟩, by change 286 - j'.val < 286 - j.val; omega⟩
  · exact ⟨hi, hlen, hsmall⟩

/-- Every entry from 286 on of a price list (the prices of the lengths) is at most 20. -/
def Big (v : List U32) : Prop := ∀ k, 286 ≤ k → k < v.length → (v[k]!).val ≤ 20

theorem small286_append {v : List U32} (h : ∀ k < 286, (v[k]!).val ≤ 15) (hv : 286 ≤ v.length)
    (x : U32) : ∀ k < 286, ((v ++ [x])[k]!).val ≤ 15 := by
  intro k hk
  rw [List.getElem!_append_left v [x] k (by omega)]
  exact h k hk

theorem big_append {v : List U32} (h : Big v) (x : U32) (hx : x.val ≤ 20) : Big (v ++ [x]) := by
  intro k hk1 hk2
  rw [List.length_append, List.length_singleton] at hk2
  by_cases hkv : k < v.length
  · rw [List.getElem!_append_left v [x] k hkv]
    exact h k hk1 hkv
  · have he : k = v.length := by omega
    subst he
    rw [List.getElem!_append_right v [x] v.length (Nat.le_refl _)]
    simpa using hx

/-- The prices of the lengths: the length symbol's bits (at most 15) with its extra bits (at
most 5), appended from length 3 on. -/
theorem code2_body (lcost : alloc.vec.Vec U32) (len : Usize)
    (h3 : 3 ≤ len.val) (h259 : len.val ≤ 259) (hlen : lcost.val.length = 286 + len.val)
    (hsmall : ∀ k < 286, (lcost.val[k]!).val ≤ 15) (hbig : Big lcost.val) :
    code_costs_loop1.body lcost len ⦃ r =>
      match r with
      | .done v => v.val.length = 545 ∧ (∀ k < 286, (v.val[k]!).val ≤ 15) ∧ Big v.val
      | .cont (v, j) => j.val = len.val + 1 ∧ j.val ≤ 259 ∧ v.val.length = 286 + j.val ∧
          (∀ k < 286, (v.val[k]!).val ≤ 15) ∧ Big v.val ⦄ := by
  unfold code_costs_loop1.body
  split
  · have h258 : len.val ≤ 258 := by scalar_tac
    step as ⟨lc, hlc0, hlc1, hlc2⟩
    step as ⟨i1, hi1⟩
    have hi1b : i1.val < lcost.val.length := by omega
    step as ⟨i2, hi2⟩
    have hi2b : i2.val ≤ 15 := by
      rw [hi2, ← getElem!_pos lcost.val i1.val hi1b]
      exact hsmall i1.val (by omega)
    have hle := Costs.length_extra_bound lc.val (by omega)
    have hll : lc.val < LENGTH_EXTRA.val.length := by simp [LENGTH_EXTRA, Array.make]; omega
    rw [getElem!_pos LENGTH_EXTRA.val lc.val hll] at hle
    step as ⟨i3, hi3⟩
    step as ⟨x, hx⟩
    have hxb : x.val ≤ 20 := by scalar_tac
    have hcap : lcost.val.length < Usize.max := by scalar_tac
    step as ⟨lcost1, hlcost1⟩
    step as ⟨len1, hlen1⟩
    try simp only [WP.spec_ok]
    refine ⟨hlen1, by scalar_tac, ?_, ?_, ?_⟩
    · rw [hlcost1, List.length_append, List.length_singleton, hlen1, hlen]
      omega
    · rw [hlcost1]; exact small286_append hsmall (by omega) x
    · rw [hlcost1]; exact big_append hbig x hxb
  · have h259' : 259 ≤ len.val := by scalar_tac
    step*
    all_goals (try simp only [WP.spec_ok])
    all_goals exact ⟨by omega, hsmall, hbig⟩

theorem code2_loop (lcost : alloc.vec.Vec U32) (len : Usize)
    (h3 : 3 ≤ len.val) (h259 : len.val ≤ 259) (hlen : lcost.val.length = 286 + len.val)
    (hsmall : ∀ k < 286, (lcost.val[k]!).val ≤ 15) (hbig : Big lcost.val) :
    code_costs_loop1 lcost len ⦃ v =>
      v.val.length = 545 ∧ (∀ k < 286, (v.val[k]!).val ≤ 15) ∧ Big v.val ⦄ := by
  unfold code_costs_loop1
  apply loop.spec_decr_nat (fun (_, j) => 259 - j.val)
    (fun (v, j) => 3 ≤ j.val ∧ j.val ≤ 259 ∧ v.val.length = 286 + j.val ∧
      (∀ k < 286, (v.val[k]!).val ≤ 15) ∧ Big v.val)
  · rintro ⟨v, j⟩ ⟨hj3, hj, hvl, hvs, hvb⟩
    refine WP.spec_mono (code2_body v j hj3 hj hvl hvs hvb) ?_
    intro r hr
    cases r with
    | done v => exact hr
    | cont state =>
        obtain ⟨v', j'⟩ := state
        obtain ⟨he, hj', hl', hs', hb'⟩ := hr
        exact ⟨⟨by omega, hj', hl', hs', hb'⟩, by change 259 - j'.val < 259 - j.val; omega⟩
  · exact ⟨h3, h259, hlen, hsmall, hbig⟩

theorem code1_body (dist : Code) (dcost : alloc.vec.Vec U32) (i : Usize)
    (hi : i.val ≤ 30) (hlen : dcost.val.length = i.val) (hsmall : Small dcost.val) :
    code_costs_loop2.body dist i dcost ⦃ r =>
      match r with
      | .done v => v.val.length = 30 ∧ Small v.val
      | .cont (j, v) => j.val = i.val + 1 ∧ j.val ≤ 30 ∧ v.val.length = j.val ∧ Small v.val ⦄ := by
  unfold code_costs_loop2.body
  split
  · dsimp only
    have hxSpec : (if i < alloc.vec.Vec.len dist.lens then do
        let i2 ← alloc.vec.Vec.index_usize dist.lens i
        ok (UScalar.cast .U32 i2)
      else ok 0#u32) ⦃ x => x.val < 256 ⦄ := by
      split
      · step as ⟨i2, hi2⟩
        try simp only [WP.spec_ok]
        scalar_tac
      · step*
    step as ⟨x, hx⟩
    split
    · step*
      refine ⟨i2_post, by scalar_tac, ?_, ?_⟩
      · rw [dcost1_post, List.length_append, List.length_singleton, i2_post, hlen]
      · rw [dcost1_post]; exact small_append hsmall _ (by simp)
    · split
      · step*
        refine ⟨i2_post, by scalar_tac, ?_, ?_⟩
        · rw [dcost1_post, List.length_append, List.length_singleton, i2_post, hlen]
        · rw [dcost1_post]; exact small_append hsmall _ (by simp)
      · step*
        refine ⟨i2_post, by scalar_tac, ?_, ?_⟩
        · rw [dcost1_post, List.length_append, List.length_singleton, i2_post, hlen]
        · rw [dcost1_post]; exact small_append hsmall _ (by scalar_tac)
  · step*

theorem code1_loop (dist : Code) (dcost : alloc.vec.Vec U32) (i : Usize)
    (hi : i.val ≤ 30) (hlen : dcost.val.length = i.val) (hsmall : Small dcost.val) :
    code_costs_loop2 dist i dcost ⦃ v => v.val.length = 30 ∧ Small v.val ⦄ := by
  unfold code_costs_loop2
  apply loop.spec_decr_nat (fun (j, _) => 30 - j.val)
    (fun (j, v) => j.val ≤ 30 ∧ v.val.length = j.val ∧ Small v.val)
  · rintro ⟨j, v⟩ ⟨hj, hvl, hvs⟩
    refine WP.spec_mono (code1_body dist v j hj hvl hvs) ?_
    intro r hr
    cases r with
    | done v => exact hr
    | cont state =>
        obtain ⟨j', v'⟩ := state
        obtain ⟨he, hj', hl', hs'⟩ := hr
        exact ⟨⟨hj', hl', hs'⟩, by change 30 - j'.val < 30 - j.val; omega⟩
  · exact ⟨hi, hlen, hsmall⟩

theorem code_costs_spec (lit dist : Code) : code_costs lit dist ⦃ r => Prices r.1.val r.2.val ⦄ := by
  unfold code_costs
  have h0 := code0_loop lit (alloc.vec.Vec.with_capacity U32 545#usize) 0#usize (by simp)
    (by simp [alloc.vec.Vec.with_capacity]) (by simp [alloc.vec.Vec.with_capacity]; exact small_nil)
  step as ⟨lcost1, hl1, hl2⟩
  have hs1 : ∀ k < 286, (lcost1.val[k]!).val ≤ 15 := fun k hk => hl2 k (by rw [hl1]; exact hk)
  have hb1 : Big lcost1.val := by intro k hk1 hk2; rw [hl1] at hk2; omega
  -- the three unpriced lengths
  have hcap1 : lcost1.val.length < Usize.max := by rw [hl1]; scalar_tac
  step as ⟨lcost2, hlc2⟩
  have hl2' : lcost2.val.length = 287 := by
    rw [hlc2, List.length_append, List.length_singleton, hl1]
  have hs2 : ∀ k < 286, (lcost2.val[k]!).val ≤ 15 := by
    rw [hlc2]; exact small286_append hs1 (by omega) _
  have hb2 : Big lcost2.val := by rw [hlc2]; exact big_append hb1 _ (by simp)
  have hcap2 : lcost2.val.length < Usize.max := by rw [hl2']; scalar_tac
  step as ⟨lcost3, hlc3⟩
  have hl3' : lcost3.val.length = 288 := by
    rw [hlc3, List.length_append, List.length_singleton, hl2']
  have hs3 : ∀ k < 286, (lcost3.val[k]!).val ≤ 15 := by
    rw [hlc3]; exact small286_append hs2 (by omega) _
  have hb3 : Big lcost3.val := by rw [hlc3]; exact big_append hb2 _ (by simp)
  have hcap3 : lcost3.val.length < Usize.max := by rw [hl3']; scalar_tac
  step as ⟨lcost4, hlc4⟩
  have hl4' : lcost4.val.length = 289 := by
    rw [hlc4, List.length_append, List.length_singleton, hl3']
  have hs4 : ∀ k < 286, (lcost4.val[k]!).val ≤ 15 := by
    rw [hlc4]; exact small286_append hs3 (by omega) _
  have hb4 : Big lcost4.val := by rw [hlc4]; exact big_append hb3 _ (by simp)
  have hloop := code2_loop lcost4 3#usize (by simp) (by simp) (by simp [hl4']) hs4 hb4
  step as ⟨lcost5, hl5, hs5, hb5⟩
  have h1 := code1_loop dist (alloc.vec.Vec.with_capacity U32 30#usize) 0#usize (by simp)
    (by simp [alloc.vec.Vec.with_capacity]) (by simp [alloc.vec.Vec.with_capacity]; exact small_nil)
  step as ⟨dcost, hd1, hd2⟩
  try simp only [WP.spec_ok]
  refine ⟨hl5, hd1, hs5, ?_, ?_⟩
  · intro k hk; exact hd2 k (by rw [hd1]; exact hk)
  · intro k hk1 hk2; exact hb5 k hk1 (by rw [hl5]; exact hk2)

-- ================================================================ the codes of a plan

theorem plan_codes_spec (data : Aeneas.Std.Slice U8) (start : Usize) (plan : Plan) (stop : ℕ)
    (hr : Runs data.val stop start.val stop plan.lengths.val plan.distances.val)
    (hd : stop ≤ data.val.length) (hsize : plan.lengths.val.length ≤ 32768) :
    plan_codes data start plan ⦃ _ => True ⦄ := by
  unfold plan_codes
  have hsymb := PricingHistogram.correct data start plan.lengths plan.distances stop hr hd (by omega)
  step as ⟨lfreq, dfreq, hlf, hdf⟩
  have hm1 := Huff.code_lengths_spec lfreq 15#usize (by rw [hlf]; omega) (by simp)
  step as ⟨lit, _, _⟩
  have hm2 := Huff.code_lengths_spec dfreq 15#usize (by rw [hdf]; omega) (by simp)
  step as ⟨dist, _, _⟩
  all_goals step*

-- ================================================================ the passes

/-- The difference of two prices is counted as at most 64. -/
theorem price_diff_spec (a b : U32) : price_diff a b ⦃ r => r.val ≤ 64 ⦄ := by
  unfold price_diff
  have hsel : ((if a > b then a - b else b - a) : Result U32) ⦃ _ => True ⦄ := by
    split <;> step* <;> (try simp)
  step as ⟨d, _⟩
  split
  · simp
  · rename_i hle
    try simp only [WP.spec_ok]
    scalar_tac

/-- The literal/length prices are compared while the gap is within the limit: the sum stays
small, and each step advances. -/
theorem near_body0 (la lb : alloc.vec.Vec U32) (limit gap : U32) (i : Usize)
    (hl : limit.val ≤ 1000) :
    near_prices_loop0.body la lb limit gap i ⦃ r =>
      match r with
      | .done _ => True
      | .cont (_, i') => i'.val = i.val + 1 ∧ i.val < 286 ⦄ := by
  unfold near_prices_loop0.body
  dsimp only
  split
  · rename_i h1
    split
    · rename_i h2
      split
      · rename_i h3
        split
        · rename_i h4
          have hi : i.val < la.val.length := by scalar_tac
          have hi2 : i.val < lb.val.length := by scalar_tac
          step as ⟨i3, _⟩
          step as ⟨i4, _⟩
          have hpd := price_diff_spec i3 i4
          step as ⟨d, hd⟩
          have hg : gap.val ≤ limit.val := by scalar_tac
          step as ⟨gap1, _⟩
          step as ⟨i5, hi5⟩
          try simp only [WP.spec_ok]
          exact ⟨hi5, by scalar_tac⟩
        · simp
      · simp
    · simp
  · simp

theorem near_loop0 (la lb : alloc.vec.Vec U32) (limit gap : U32) (i : Usize)
    (hl : limit.val ≤ 1000) :
    near_prices_loop0 la lb limit gap i ⦃ _ => True ⦄ := by
  unfold near_prices_loop0
  apply loop.spec_decr_nat (fun (_, j) => 286 - j.val) (fun _ => True)
  · rintro ⟨g, j⟩ _
    refine WP.spec_mono (near_body0 la lb limit g j hl) ?_
    intro r hr
    cases r with
    | done _ => trivial
    | cont state =>
        obtain ⟨g', j'⟩ := state
        obtain ⟨h1, h2⟩ := hr
        exact ⟨trivial, by change 286 - j'.val < 286 - j.val; omega⟩
  · trivial

/-- The distance prices, likewise. -/
theorem near_body1 (da db : alloc.vec.Vec U32) (limit gap : U32) (i : Usize)
    (hl : limit.val ≤ 1000) :
    near_prices_loop1.body da db limit gap i ⦃ r =>
      match r with
      | .done _ => True
      | .cont (_, i') => i'.val = i.val + 1 ∧ i.val < 30 ⦄ := by
  unfold near_prices_loop1.body
  dsimp only
  split
  · rename_i h1
    split
    · rename_i h2
      split
      · rename_i h3
        split
        · rename_i h4
          have hi : i.val < da.val.length := by scalar_tac
          have hi2 : i.val < db.val.length := by scalar_tac
          step as ⟨i3, _⟩
          step as ⟨i4, _⟩
          have hpd := price_diff_spec i3 i4
          step as ⟨d, hd⟩
          have hg : gap.val ≤ limit.val := by scalar_tac
          step as ⟨gap1, _⟩
          step as ⟨i5, hi5⟩
          try simp only [WP.spec_ok]
          exact ⟨hi5, by scalar_tac⟩
        · simp
      · simp
    · simp
  · simp

theorem near_loop1 (da db : alloc.vec.Vec U32) (limit gap : U32) (i : Usize)
    (hl : limit.val ≤ 1000) :
    near_prices_loop1 da db limit gap i ⦃ _ => True ⦄ := by
  unfold near_prices_loop1
  apply loop.spec_decr_nat (fun (_, j) => 30 - j.val) (fun _ => True)
  · rintro ⟨g, j⟩ _
    refine WP.spec_mono (near_body1 da db limit g j hl) ?_
    intro r hr
    cases r with
    | done _ => trivial
    | cont state =>
        obtain ⟨g', j'⟩ := state
        obtain ⟨h1, h2⟩ := hr
        exact ⟨trivial, by change 30 - j'.val < 30 - j.val; omega⟩
  · trivial

/-- Comparing two price lists always terminates; what it says does not matter. -/
theorem near_prices_spec (la da lb db : alloc.vec.Vec U32) (limit : U32) (hl : limit.val ≤ 1000) :
    near_prices la da lb db limit ⦃ _ => True ⦄ := by
  unfold near_prices
  have h0 := near_loop0 la lb limit 0#u32 0#usize hl
  step as ⟨gap1, _⟩
  have h1 := near_loop1 da db limit gap1 0#usize hl
  step as ⟨gap2, _⟩
  try simp

theorem passes_body (data : Aeneas.Std.Slice U8) (start stop passes : Usize)
    (hints : alloc.vec.Vec U64) (plan : Plan) (lcost1 dcost1 : alloc.vec.Vec U32) (pass : Usize)
    (settled : Bool)
    (hrun : Runs data.val stop.val start.val stop.val plan.lengths.val plan.distances.val)
    (hprices : Prices lcost1.val dcost1.val)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length) (hsize : stop.val - start.val ≤ 32768)
    (hh : Gzip.Proofs.Edges.Edges data.val start.val stop.val hints.val) :
    optimal_passes_loop.body data start stop passes hints plan lcost1 dcost1 pass settled ⦃ r =>
      match r with
      | .done (p, l, d, _) => Runs data.val stop.val start.val stop.val p.lengths.val p.distances.val ∧
          Prices l.val d.val
      | .cont (p, l, d, pass', _) => Runs data.val stop.val start.val stop.val p.lengths.val p.distances.val ∧
          Prices l.val d.val ∧ pass'.val = pass.val + 1 ∧ pass.val < passes.val ⦄ := by
  unfold optimal_passes_loop.body
  split
  · split
    · simp only [WP.spec_ok]
      exact ⟨hrun, hprices⟩
    · have hpp : pass.val < passes.val := by scalar_tac
      have hpl := runs_lengths hrun
      have hpc := plan_codes_spec data start plan stop.val hrun hd (by omega)
      step as ⟨lit, dist, _⟩
      have hcc := code_costs_spec lit dist
      step as ⟨lcost2, dcost2, hprices2⟩
      step as ⟨i1, hi1⟩
      have hsel : (if alloc.vec.Vec.len hints <= i1 then ok (plan, true) else do
            let b ← near_prices lcost1 dcost1 lcost2 dcost2 12#u32
            if b then ok (plan, true) else do
              let plan2 ← optimal_hinted data start stop hints lcost2 dcost2
              ok (plan2, settled)) ⦃ r =>
          Runs data.val stop.val start.val stop.val r.1.lengths.val r.1.distances.val ⦄ := by
        split
        · simp only [WP.spec_ok]
          exact hrun
        · have hsp := near_prices_spec lcost1 dcost1 lcost2 dcost2 12#u32 (by scalar_tac)
          step as ⟨b, _⟩
          split
          · simp only [WP.spec_ok]
            exact hrun
          · have hoh := Dp.optimal_hinted_correct data start stop hints lcost2 dcost2 hs hd hsize
              hprices2 hh
            step as ⟨plan2, hplan2⟩
            try simp only [WP.spec_ok]
            exact hplan2
      step as ⟨plan1, settled1, hplan1⟩
      step as ⟨pass1, hpass1⟩
      try simp only [WP.spec_ok]
      exact ⟨hplan1, hprices2, hpass1, hpp⟩
  · simp only [WP.spec_ok]
    exact ⟨hrun, hprices⟩

theorem passes_loop (data : Aeneas.Std.Slice U8) (start stop passes : Usize)
    (hints : alloc.vec.Vec U64) (plan : Plan) (lcost1 dcost1 : alloc.vec.Vec U32) (pass : Usize)
    (settled : Bool)
    (hrun : Runs data.val stop.val start.val stop.val plan.lengths.val plan.distances.val)
    (hprices : Prices lcost1.val dcost1.val)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length) (hsize : stop.val - start.val ≤ 32768)
    (hh : Gzip.Proofs.Edges.Edges data.val start.val stop.val hints.val) :
    optimal_passes_loop data start stop passes hints plan lcost1 dcost1 pass settled ⦃ r =>
      Runs data.val stop.val start.val stop.val r.1.lengths.val r.1.distances.val ∧
      Prices r.2.1.val r.2.2.1.val ⦄ := by
  unfold optimal_passes_loop
  apply loop.spec_decr_nat (fun (_, _, _, j, _) => passes.val - j.val)
    (fun (p, l, d, _, _) => Runs data.val stop.val start.val stop.val p.lengths.val p.distances.val ∧
      Prices l.val d.val)
  · rintro ⟨p, l, d, j, s⟩ ⟨hp, hpr⟩
    refine WP.spec_mono (passes_body data start stop passes hints p l d j s hp hpr hs hd hsize hh) ?_
    intro r hr
    cases r with
    | done state =>
        obtain ⟨p', l', d', s'⟩ := state
        exact hr
    | cont state =>
        obtain ⟨p', l', d', j', s'⟩ := state
        obtain ⟨hp', hpr', he, hlt⟩ := hr
        exact ⟨⟨hp', hpr'⟩, by change passes.val - j'.val < passes.val - j.val; omega⟩
  · exact ⟨hrun, hprices⟩

theorem incompressible_loop_spec (data : Aeneas.Std.Slice U8) (start : Usize)
    (table : alloc.vec.Vec U32) (hits : I32) (p : Usize)
    (hlen : table.val.length = 4096) (hp : start.val ≤ p.val ∧ p.val ≤ start.val + 4096)
    (hd : start.val + 8192 ≤ data.val.length)
    (hh : 0 ≤ hits.val ∧ hits.val ≤ (p.val : Int) - start.val) :
    incompressible_loop data start table hits p ⦃ _ => True ⦄ := by
  unfold incompressible_loop
  apply loop.spec_decr_nat (fun (_, _, q) => start.val + 4096 - q.val)
    (fun (t, k, q) => t.val.length = 4096 ∧ start.val ≤ q.val ∧ q.val ≤ start.val + 4096 ∧
      0 ≤ k.val ∧ k.val ≤ (q.val : Int) - start.val)
  · rintro ⟨t, k, q⟩ ⟨htl, hq0, hq1, hk0, hk1⟩
    dsimp only
    unfold incompressible_loop.body
    step as ⟨i, hi⟩
    split
    · split
      · simp only [WP.spec_ok]
      · have hq4 : q.val + 4 ≤ data.val.length := by scalar_tac
        step as ⟨h, hh⟩
        have hhb : h.val < t.val.length := by rw [htl]; scalar_tac
        step as ⟨c0, hc0⟩
        step as ⟨c, hc⟩
        step as ⟨next, hnext⟩
        step
        step as ⟨n32, hn32⟩
        have htl1 : (index_mut_back n32).val.length = 4096 := by
          rw [index_mut_back_post]; simp only [alloc.vec.Vec.set_val_eq, List.length_set, htl]
        split
        · split
          · step as ⟨i3, hi3⟩
            step as ⟨i4, hi4⟩
            step as ⟨i5, hi5⟩
            split
            · step as ⟨hits2, hhits2⟩
              refine ⟨htl1, by omega, by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac⟩
            · step*
          · step*
        · step*
  
    · simp only [WP.spec_ok]
  · exact ⟨hlen, hp.1, hp.2, hh.1, hh.2⟩

/-- Whether a chunk looks incompressible: a choice, with no bearing on the invariants. -/
theorem incompressible_spec (data : Aeneas.Std.Slice U8) (start stop : Usize)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length) :
    incompressible data start stop ⦃ _ => True ⦄ := by
  unfold incompressible
  step as ⟨i, hi⟩
  split
  · simp only [WP.spec_ok]
  · have hz := Gzip.Proofs.Chains.zeros_u32_correct 4096#usize
    step as ⟨table, htable⟩
    have hl := incompressible_loop_spec data start table 0#i32 start
      (by rw [htable, List.length_replicate]) ⟨Nat.le_refl _, by omega⟩ (by scalar_tac) (by simp)
    step*

/-- The plan of `n` literals. -/
theorem literal_plan_spec (n : Usize) :
    literal_plan n ⦃ p => p.lengths.val = List.replicate n.val 1#u16 ∧
      p.distances.val = List.replicate n.val 0#u16 ⦄ := by
  unfold literal_plan
  have hr := alloc.vec.Vec.resize_spec core.clone.CloneU16 (alloc.vec.Vec.new U16) n 1#u16
    (by rfl)
  step as ⟨v, hv⟩
  have hr1 := alloc.vec.Vec.resize_spec core.clone.CloneU16 (alloc.vec.Vec.new U16) n 0#u16
    (by rfl)
  step as ⟨v1, hv1⟩
  try simp only [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · rw [hv]
    unfold List.resize
    simp [alloc.vec.Vec.new]
  · rw [hv1]
    unfold List.resize
    simp [alloc.vec.Vec.new]

/-- The prices of the first pass: the given ones, or the first block's greedy seed. -/
theorem first_prices_spec (data : Aeneas.Std.Slice U8) (start stop : Usize)
    (lcost dcost : alloc.vec.Vec U32) (five : Bool)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length)
    (hsize : stop.val - start.val ≤ 32768) (hprices : Prices lcost.val dcost.val) :
    first_prices data start stop lcost dcost five ⦃ r => Prices r.1.val r.2.val ⦄ := by
  unfold first_prices
  split
  · have hz := Gzip.Proofs.Chains.zeros_u32_correct 32768#usize
    step as ⟨seedhead, hh⟩
    have hz' := Gzip.Proofs.Chains.zeros_u32_correct 65536#usize
    step as ⟨seedchain, hc⟩
    have ht0 : Gzip.Proofs.Chains.Tables seedhead.val seedchain.val 0 := by
      simp only [hh, hc]
      change Gzip.Proofs.Chains.Tables (List.replicate 32768 0#u32) (List.replicate 65536 0#u32) 0
      exact Gzip.Proofs.Chains.initial_tables 32768 (by omega)
    have hts := Gzip.Proofs.Chains.tables_advance_to ht0 (Nat.zero_le start.val)
    have hg := Gzip.Proofs.Greedy.greedy_correct data start stop 11#u8 seedhead seedchain five
      (Gzip.Proofs.Chains.ltables_of_tables hts) hs hd hsize (by simp)
    step as ⟨seed, seedhead1, seedchain1, hseed, hfused, _⟩
    obtain ⟨_, hlf, hdf, _⟩ := hseed.2 hfused
    have hm1 := Huff.code_lengths_spec seed.lfreq 15#usize (by rw [hlf]; omega) (by simp)
    step as ⟨v, _, _⟩
    have hm2 := Huff.code_lengths_spec seed.dfreq 15#usize (by rw [hdf]; omega) (by simp)
    step as ⟨v1, _, _⟩
    exact code_costs_spec _ _
  · simp only [WP.spec_ok]
    exact hprices

@[step]
theorem optimal_passes_correct (data : Aeneas.Std.Slice U8) (start stop : Usize)
    (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32) (passes depth : Usize) (lcost dcost : alloc.vec.Vec U32)
    (five four : Bool)
    (ht : Gzip.Proofs.Chains.Tables head.val chain.val start.val)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length)
    (hsize : stop.val - start.val ≤ 32768) (hprices : Prices lcost.val dcost.val) :
    optimal_passes data start stop head chain passes depth lcost dcost five four ⦃ r =>
      Runs data.val stop.val start.val stop.val r.1.1.lengths.val r.1.1.distances.val ∧
      Prices r.1.2.1.val r.1.2.2.val ∧
      Gzip.Proofs.Chains.Tables r.2.1.val r.2.2.val stop.val ⦄ := by
  unfold optimal_passes
  have hinc := incompressible_spec data start stop hs hd
  step as ⟨b, _⟩
  split
  · step as ⟨n, hn⟩
    have hlp := literal_plan_spec n
    step as ⟨plan, hpl, hpd⟩
    have hrun : Runs data.val stop.val start.val stop.val plan.lengths.val plan.distances.val := by
      rw [hpl, hpd]
      have hr := Gzip.Proofs.FastGreedy.literal_runs data.val stop.val start.val n.val
      have he : start.val + n.val = stop.val := by omega
      rw [he] at hr
      exact hr
    have hpc := plan_codes_spec data start plan stop.val hrun hd (by
      have := runs_lengths hrun
      omega)
    step as ⟨lit, dist, _⟩
    have hcc := code_costs_spec lit dist
    step as ⟨lcost1, dcost1, hprices1⟩
    try simp only [WP.spec_ok]
    exact ⟨hrun, hprices1, Gzip.Proofs.Chains.tables_advance_to ht hs⟩
  have hseed : ((if five then ok (¬ four) else ok false) : Result Bool) ⦃ _ => True ⦄ := by
    split <;> step*
  step as ⟨seed_five, _⟩
  have hfp := first_prices_spec data start stop lcost dcost seed_five hs hd hsize hprices
  step as ⟨lcost0, dcost0, hprices0⟩
  have ho := Dp.optimal_correct data start stop head chain lcost0 dcost0 depth (passes > 1#usize) five
    four ht hs hd hsize hprices0
  step as ⟨fho, head1, chain1, hrun, ht1, hh⟩
  obtain ⟨first, hints⟩ := fho
  dsimp only at hrun hh ⊢
  have hl := passes_loop data start stop passes hints first lcost0 dcost0 1#usize false hrun hprices0
    hs hd hsize hh
  step as ⟨plan, lcost1, dcost1, settled, hplan, hprices1⟩
  split
  · try simp only [WP.spec_ok]
    exact ⟨hplan, hprices1, ht1⟩
  · have hpc := plan_codes_spec data start plan stop.val hplan hd (by
      have := runs_lengths hplan
      omega)
    step as ⟨lit, dist, _⟩
    have hcc := code_costs_spec lit dist
    step as ⟨lcost3, dcost3, hprices3⟩
    try simp only [WP.spec_ok]
    exact ⟨hplan, hprices3, ht1⟩

/-- The plan of a block at a level above 0, and the prices for the next block. -/
@[step]
theorem parse_correct (data : Aeneas.Std.Slice U8) (start stop : Usize) (level : U8)
    (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32) (lcost dcost : alloc.vec.Vec U32)
    (hlt : Gzip.Proofs.Chains.LTables level.val head.val chain.val start.val)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length)
    (hsize : stop.val - start.val ≤ 32768) (hprices : Prices lcost.val dcost.val) :
    parse data start stop level head chain lcost dcost ⦃ r =>
      Counting.ParsedOk data.val start.val stop.val r.1.1 ∧
      Prices r.1.2.1.val r.1.2.2.val ∧
      Gzip.Proofs.Chains.LTables level.val r.2.1.val r.2.2.val stop.val ⦄ := by
  unfold parse
  have hinc : ((if level = 1#u8 then incompressible data start stop else ok false) : Result Bool)
      ⦃ _ => True ⦄ := by
    split
    · exact incompressible_spec data start stop hs hd
    · simp only [WP.spec_ok]
  step as ⟨b, _⟩
  split
  · step as ⟨n, hn⟩
    have hlp := literal_plan_spec n
    step as ⟨plan, hpl, hpd⟩
    have hrun : Runs data.val stop.val start.val stop.val plan.lengths.val plan.distances.val := by
      rw [hpl, hpd]
      have hr := Gzip.Proofs.FastGreedy.literal_runs data.val stop.val start.val n.val
      have he : start.val + n.val = stop.val := by omega
      rw [he] at hr
      exact hr
    step as ⟨parsed, hpp, hpf⟩
    try simp only [WP.spec_ok]
    exact ⟨Counting.parsedOk_unfused hpp hpf hrun, hprices, hlt⟩
  ·
    split
    · rename_i h8
      have ht : Gzip.Proofs.Chains.Tables head.val chain.val start.val :=
        Gzip.Proofs.Chains.tables_of_ltables hlt (by scalar_tac)
      have hopt : ((if level >= 10#u8 then do
            let (t, head2, chain2) ← optimal_passes data start stop head chain 6#usize 40#usize lcost dcost true true
            ok (head2, chain2, t)
          else if level = 9#u8 then do
            let (t, head2, chain2) ← optimal_passes data start stop head chain 2#usize 32#usize lcost dcost true false
            ok (head2, chain2, t)
          else do
            let (t, head2, chain2) ← optimal_passes data start stop head chain 1#usize 32#usize lcost dcost true false
            ok (head2, chain2, t)) :
          Result (alloc.vec.Vec U32 × alloc.vec.Vec U32 × (Plan × alloc.vec.Vec U32 × alloc.vec.Vec U32))) ⦃ r =>
          Runs data.val stop.val start.val stop.val r.2.2.1.lengths.val r.2.2.1.distances.val ∧
          Prices r.2.2.2.1.val r.2.2.2.2.val ∧
          Gzip.Proofs.Chains.Tables r.1.val r.2.1.val stop.val ⦄ := by
        split
        · step as ⟨t, head2, chain2, hrun, hpr, ht2⟩
          try simp only [WP.spec_ok]
          exact ⟨hrun, hpr, ht2⟩
        · split
          · step as ⟨t, head2, chain2, hrun, hpr, ht2⟩
            try simp only [WP.spec_ok]
            exact ⟨hrun, hpr, ht2⟩
          · step as ⟨t, head2, chain2, hrun, hpr, ht2⟩
            try simp only [WP.spec_ok]
            exact ⟨hrun, hpr, ht2⟩
      step as ⟨head1, chain1, plan, lcost1, dcost1, hrun, hpr, ht1⟩
      step as ⟨p, hpp, hpf⟩
      try simp only [WP.spec_ok]
      exact ⟨Counting.parsedOk_unfused hpp hpf hrun, hpr, Gzip.Proofs.Chains.ltables_of_tables ht1⟩
    · have hg := Gzip.Proofs.Greedy.greedy_correct data start stop level head chain (level > 1#u8) hlt hs hd hsize
        (by scalar_tac)
      step as ⟨p, head1, chain1, hpr, _, ht1⟩
      try simp only [WP.spec_ok]
      exact ⟨hpr, hprices, ht1⟩
  
end Gzip.Proofs.Passes
