import Gzip.Proofs.Body
import Gzip.Proofs.Fused

open Aeneas Std Result
open Gzip.solution

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace Gzip.Proofs.CostHistogram

def Checked (freq : List Usize) (lens : List U8) (n : ℕ) : Prop :=
  ∀ s < n, 0 < (freq[s]!).val → s < lens.length ∧ 1 ≤ (lens[s]!).val

theorem usable (data : List U8) (start : ℕ) (ls ds : List U16) (lsym dsym : List U8) (lfreq dfreq : List Usize)
    (lit dist : List U8) (hsym : Symbolize.Symbolized ls ds lsym dsym)
    (hsupp : Fused.Support data start ls ds lsym dsym lfreq dfreq)
    (hl : Checked lfreq lit 286) (hd : Checked dfreq dist 30) :
    Body.Usable data start ls ds lsym dsym lit dist := by
  refine ⟨?_, hl 256 (by omega) hsupp.2⟩
  intro t ht
  have hu := hsupp.1 t ht
  unfold Fused.SupportAt at hu
  unfold Body.UsableAt
  by_cases hz : (ds[t]!).val = 0
  · simp only [hz, ite_true] at hu ⊢
    exact hl _ (by scalar_tac) hu
  · simp only [hz, ite_false] at hu ⊢
    have hb := hsym.2.2 t ht hz
    exact ⟨(hl _ (by omega) hu.1).1, (hl _ (by omega) hu.1).2,
      (hd _ (by omega) hu.2).1, (hd _ (by omega) hu.2).2⟩

theorem read_length_spec (lens : alloc.vec.Vec U8) (s : Usize) :
    (if s < alloc.vec.Vec.len lens then do
      let x ← alloc.vec.Vec.index_usize lens s
      ok (UScalar.cast .Usize x)
    else ok 0#usize) ⦃ x => x.val ≤ 255 ∧
      (x.val ≠ 0 → s.val < lens.val.length ∧ 1 ≤ (lens.val[s.val]!).val) ⦄ := by
  split
  · rename_i h
    have hs : s.val < lens.val.length := by
      simpa [alloc.vec.Vec.len_val, alloc.vec.Vec.length] using (UScalar.lt_equiv _ _).mp h
    step as ⟨x, hx⟩
    try simp only [WP.spec_ok]
    have hxv : (UScalar.cast .Usize x).val = (lens.val[s.val]!).val := by
      rw [UScalar.cast_val_eq, hx, getElem!_pos lens.val s.val hs]
      exact Nat.mod_eq_of_lt (by scalar_tac)
    refine ⟨by rw [hxv]; scalar_tac, fun hn => ⟨hs, ?_⟩⟩
    rw [hxv] at hn
    omega
  · simp only [WP.spec_ok]
    exact ⟨by simp, fun h => by simp at h⟩

theorem cap_frequency (count : Usize) :
    (if count > 1048576#usize then ok 1048576#usize else ok count)
      ⦃ f => f.val ≤ 1048576 ⦄ := by
  split <;> simp only [WP.spec_ok] <;> scalar_tac

theorem cap_cost (sum : Usize) :
    (if sum > 1073741824#usize then ok 1073741824#usize else ok sum)
      ⦃ f => f.val ≤ 1073741824 ⦄ := by
  split <;> simp only [WP.spec_ok] <;> scalar_tac

theorem keep_ok (flag : Bool) (condition : Prop) [Decidable condition] :
    (if condition then ok false else ok flag) ⦃ flag' => flag' = true → flag = true ∧ ¬condition ⦄ := by
  split <;> simp_all [WP.spec_ok]

def Inv (freq : List Usize) (lens : List U8) (n : ℕ) (ok0 : Bool)
    (cost fixed : Usize) (ok1 : Bool) (s : Usize) : Prop :=
  s.val ≤ n ∧ cost.val ≤ 1073741824 ∧ fixed.val ≤ 1073741824 ∧
    (ok1 = true → ok0 = true ∧ Checked freq lens s.val)

theorem extend_checked (freq : List Usize) (lens : List U8) (s : ℕ)
    (hs : Checked freq lens s)
    (hc : 0 < (freq[s]!).val → s < lens.length ∧ 1 ≤ (lens[s]!).val) :
    Checked freq lens (s + 1) := by
  intro k hk hp
  by_cases he : k = s
  · subst he; exact hc hp
  · exact hs k (by omega) hp

theorem body0 (lfreq : alloc.vec.Vec Usize) (lit : Code) (cost fixed : Usize) (ok0 ok1 : Bool) (s : Usize)
    (hlen : lfreq.val.length = 286) (hi : Inv lfreq.val lit.lens.val 286 ok0 cost fixed ok1 s) :
    cost_histograms_loop0.body lfreq lit cost fixed ok1 s ⦃ r =>
      match r with
      | .done r => r.1.val ≤ 1073741824 ∧ r.2.1.val ≤ 1073741824 ∧
          (r.2.2 = true → ok0 = true ∧ Checked lfreq.val lit.lens.val 286)
      | .cont r => r.1 = lit ∧ Inv lfreq.val lit.lens.val 286 ok0 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 ∧
          s.val < r.2.2.2.2.val ⦄ := by
  obtain ⟨hs, hc, hf, hok⟩ := hi
  unfold cost_histograms_loop0.body
  split
  · rename_i hloop
    have hsb : s.val < 286 := by scalar_tac
    have hsl : s < alloc.vec.Vec.len lfreq := by
      apply (UScalar.lt_equiv _ _).mpr
      simp [hlen]; omega
    simp only [hsl, ↓reduceIte]
    step as ⟨count, hcount⟩
    have hcv : count.val = (lfreq.val[s.val]!).val := by
      rw [hcount, getElem!_pos lfreq.val s.val (by omega)]
    have hb : (if count != 0#usize then do
      let f ← if count > 1048576#usize then ok 1048576#usize else ok count
      let ok2 ← if count > 1048576#usize then ok false else ok ok1
      let x ← if s < alloc.vec.Vec.len lit.lens then do
        let x ← alloc.vec.Vec.index_usize lit.lens s
        ok (UScalar.cast .Usize x)
        else ok 0#usize
      let ok3 ← if x = 0#usize then ok false else ok ok2
      let extra ← if s >= 257#usize then do
        let j ← s - 257#usize
        let e ← Array.index_usize LENGTH_EXTRA j
        ok (UScalar.cast .Usize e)
        else ok 0#usize
      let width ← if s < 144#usize then ok 8#usize else
        if s < 256#usize then ok 9#usize else if s < 280#usize then ok 7#usize else ok 8#usize
      let xe ← x + extra
      let product ← f * xe
      let sum ← cost + product
      let cost1 ← if sum > 1073741824#usize then ok 1073741824#usize else ok sum
      let we ← width + extra
      let product1 ← f * we
      let sum1 ← fixed + product1
      let fixed1 ← if sum1 > 1073741824#usize then ok 1073741824#usize else ok sum1
      ok (lit, cost1, fixed1, ok3)
      else ok (lit, cost, fixed, ok1)) ⦃ r => r.1 = lit ∧ r.2.1.val ≤ 1073741824 ∧
        r.2.2.1.val ≤ 1073741824 ∧ (r.2.2.2 = true → ok0 = true ∧ Checked lfreq.val lit.lens.val (s.val + 1)) ⦄ := by
      split
      · have hfreq := cap_frequency count
        step as ⟨f, hfb⟩
        have hkeep := keep_ok ok1 (count > 1048576#usize)
        step as ⟨ok2, hok2⟩
        have hread := read_length_spec lit.lens s
        step as ⟨x, hxb, hxvalid⟩
        have hkeepx := keep_ok ok2 (x = 0#usize)
        step as ⟨ok3, hok3⟩
        have hextra : (if s >= 257#usize then do
            let j ← s - 257#usize
            let e ← Array.index_usize LENGTH_EXTRA j
            ok (UScalar.cast .Usize e)
          else ok 0#usize) ⦃ e => e.val ≤ 5 ⦄ := by
          split
          · rename_i he
            have hes : 257 ≤ s.val := by scalar_tac
            step as ⟨j, hj⟩
            have hjb : j.val < 29 := by omega
            have hje : j.val < LENGTH_EXTRA.val.length := by simp [LENGTH_EXTRA, Array.make]; omega
            step as ⟨e, heq⟩
            try simp only [WP.spec_ok]
            rw [UScalar.cast_val_eq, heq]
            have he := Costs.length_extra_bound j.val hjb
            rw [getElem!_pos LENGTH_EXTRA.val j.val hje] at he
            exact (Nat.mod_le _ _).trans he
          · simp [WP.spec_ok]
        step as ⟨extra, heb⟩
        have hwidth : (if s < 144#usize then ok 8#usize else
            if s < 256#usize then ok 9#usize else if s < 280#usize then ok 7#usize else ok 8#usize)
            ⦃ w => w.val ≤ 9 ⦄ := by
          split
          · simp [WP.spec_ok]
          · split
            · simp [WP.spec_ok]
            · split <;> simp [WP.spec_ok]
        step as ⟨width, hwb⟩
        step as ⟨xe, hxe⟩
        have hxeb : xe.val ≤ 260 := by omega
        have hprod : f.val * xe.val ≤ 272629760 := by
          calc f.val * xe.val ≤ 1048576 * 260 := Nat.mul_le_mul hfb hxeb
               _ = 272629760 := by decide
        step as ⟨product, hproduct⟩
        step as ⟨sum, hsum⟩
        have hcap := cap_cost sum
        step as ⟨cost1, hcost1⟩
        step as ⟨we, hwe⟩
        have hweb : we.val ≤ 14 := by omega
        have hprod1 : f.val * we.val ≤ 14680064 := by
          calc f.val * we.val ≤ 1048576 * 14 := Nat.mul_le_mul hfb hweb
               _ = 14680064 := by decide
        step as ⟨product1, hproduct1⟩
        step as ⟨sum1, hsum1⟩
        have hcap1 := cap_cost sum1
        step as ⟨fixed1, hfixed1⟩
        try simp only [WP.spec_ok]
        refine ⟨hcost1, hfixed1, ?_⟩
        intro ho3
        have ho2 := (hok3 ho3).1
        have ho1 := (hok2 ho2).1
        obtain ⟨h0, hcheck⟩ := hok ho1
        refine ⟨h0, extend_checked _ _ _ hcheck (fun _ => hxvalid ?_)⟩
        have hn := (hok3 ho3).2
        intro hz
        apply hn
        apply (UScalar.eq_equiv _ _).mpr
        simpa using hz
      · rename_i hzero
        simp only [WP.spec_ok]
        refine ⟨by trivial, hc, hf, ?_⟩
        intro ho
        obtain ⟨h0, hcheck⟩ := hok ho
        refine ⟨h0, extend_checked _ _ _ hcheck ?_⟩
        intro hp
        have hz : count.val = 0 := by scalar_tac
        omega
    step as ⟨lit1, cost1, fixed1, ok2, hlit, hcost1, hfixed1, hok2⟩
    step as ⟨s1, hs1⟩
    try simp only [WP.spec_ok]
    exact ⟨hlit, by subst hlit; exact ⟨by omega, hcost1, hfixed1, by simpa [hs1] using hok2⟩, by omega⟩
  · rename_i hdone
    have he : s.val = 286 := by scalar_tac
    simp only [WP.spec_ok]
    exact ⟨hc, hf, by simpa [he] using hok⟩

theorem body1 (dfreq : alloc.vec.Vec Usize) (dist : Code) (cost fixed : Usize) (ok0 ok1 : Bool) (s : Usize)
    (hlen : dfreq.val.length = 30) (hi : Inv dfreq.val dist.lens.val 30 ok0 cost fixed ok1 s) :
    cost_histograms_loop1.body dfreq dist cost fixed ok1 s ⦃ r =>
      match r with
      | .done r => r.1.val ≤ 1073741824 ∧ r.2.1.val ≤ 1073741824 ∧
          (r.2.2 = true → ok0 = true ∧ Checked dfreq.val dist.lens.val 30)
      | .cont r => r.1 = dist ∧ Inv dfreq.val dist.lens.val 30 ok0 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 ∧
          s.val < r.2.2.2.2.val ⦄ := by
  obtain ⟨hs, hc, hf, hok⟩ := hi
  unfold cost_histograms_loop1.body
  split
  · rename_i hloop
    have hsb : s.val < 30 := by scalar_tac
    have hsl : s < alloc.vec.Vec.len dfreq := by
      apply (UScalar.lt_equiv _ _).mpr
      simp [hlen]; omega
    simp only [hsl, ↓reduceIte]
    step as ⟨count, hcount⟩
    have hcv : count.val = (dfreq.val[s.val]!).val := by
      rw [hcount, getElem!_pos dfreq.val s.val (by omega)]
    have hb : (if count != 0#usize then do
      let f ← if count > 1048576#usize then ok 1048576#usize else ok count
      let ok2 ← if count > 1048576#usize then ok false else ok ok1
      let x ← if s < alloc.vec.Vec.len dist.lens then do
        let x ← alloc.vec.Vec.index_usize dist.lens s
        ok (UScalar.cast .Usize x)
        else ok 0#usize
      let ok3 ← if x = 0#usize then ok false else ok ok2
      let e ← Array.index_usize DIST_EXTRA s
      let extra ← lift (UScalar.cast .Usize e)
      let xe ← x + extra
      let product ← f * xe
      let sum ← cost + product
      let cost1 ← if sum > 1073741824#usize then ok 1073741824#usize else ok sum
      let we ← 5#usize + extra
      let product1 ← f * we
      let sum1 ← fixed + product1
      let fixed1 ← if sum1 > 1073741824#usize then ok 1073741824#usize else ok sum1
      ok (dist, cost1, fixed1, ok3)
      else ok (dist, cost, fixed, ok1)) ⦃ r => r.1 = dist ∧ r.2.1.val ≤ 1073741824 ∧
        r.2.2.1.val ≤ 1073741824 ∧ (r.2.2.2 = true → ok0 = true ∧ Checked dfreq.val dist.lens.val (s.val + 1)) ⦄ := by
      split
      · have hfreq := cap_frequency count
        step as ⟨f, hfb⟩
        have hkeep := keep_ok ok1 (count > 1048576#usize)
        step as ⟨ok2, hok2⟩
        have hread := read_length_spec dist.lens s
        step as ⟨x, hxb, hxvalid⟩
        have hkeepx := keep_ok ok2 (x = 0#usize)
        step as ⟨ok3, hok3⟩
        have hse : s.val < DIST_EXTRA.val.length := by simp [DIST_EXTRA, Array.make]; omega
        have he := Costs.distance_extra_bound s.val hsb
        rw [getElem!_pos DIST_EXTRA.val s.val hse] at he
        step as ⟨e, heq⟩
        step as ⟨extra, hext⟩
        have heb : extra.val ≤ 13 := by
          rw [hext, UScalar.cast_val_eq, heq]
          exact (Nat.mod_le _ _).trans he
        step as ⟨xe, hxe⟩
        have hxeb : xe.val ≤ 268 := by omega
        have hprod : f.val * xe.val ≤ 281018368 := by
          calc f.val * xe.val ≤ 1048576 * 268 := Nat.mul_le_mul hfb hxeb
               _ = 281018368 := by decide
        step as ⟨product, hproduct⟩
        step as ⟨sum, hsum⟩
        have hcap := cap_cost sum
        step as ⟨cost1, hcost1⟩
        step as ⟨we, hwe⟩
        have hweb : we.val ≤ 18 := by omega
        have hprod1 : f.val * we.val ≤ 18874368 := by
          calc f.val * we.val ≤ 1048576 * 18 := Nat.mul_le_mul hfb hweb
               _ = 18874368 := by decide
        step as ⟨product1, hproduct1⟩
        step as ⟨sum1, hsum1⟩
        have hcap1 := cap_cost sum1
        step as ⟨fixed1, hfixed1⟩
        try simp only [WP.spec_ok]
        refine ⟨hcost1, hfixed1, ?_⟩
        intro ho3
        have ho2 := (hok3 ho3).1
        have ho1 := (hok2 ho2).1
        obtain ⟨h0, hcheck⟩ := hok ho1
        refine ⟨h0, extend_checked _ _ _ hcheck (fun _ => hxvalid ?_)⟩
        have hn := (hok3 ho3).2
        intro hz
        apply hn
        apply (UScalar.eq_equiv _ _).mpr
        simpa using hz
      · rename_i hzero
        simp only [WP.spec_ok]
        refine ⟨by trivial, hc, hf, ?_⟩
        intro ho
        obtain ⟨h0, hcheck⟩ := hok ho
        refine ⟨h0, extend_checked _ _ _ hcheck ?_⟩
        intro hp
        have hz : count.val = 0 := by scalar_tac
        omega
    step as ⟨dist1, cost1, fixed1, ok2, hdist, hcost1, hfixed1, hok2⟩
    step as ⟨s1, hs1⟩
    try simp only [WP.spec_ok]
    exact ⟨hdist, by subst hdist; exact ⟨by omega, hcost1, hfixed1, by simpa [hs1] using hok2⟩, by omega⟩
  · rename_i hdone
    have he : s.val = 30 := by scalar_tac
    simp only [WP.spec_ok]
    exact ⟨hc, hf, by simpa [he] using hok⟩

theorem loop0 (lfreq : alloc.vec.Vec Usize) (lit : Code) (cost fixed : Usize) (ok0 ok1 : Bool) (s : Usize)
    (hlen : lfreq.val.length = 286) (hi : Inv lfreq.val lit.lens.val 286 ok0 cost fixed ok1 s) :
    cost_histograms_loop0 lfreq lit cost fixed ok1 s ⦃ r =>
      r.1.val ≤ 1073741824 ∧ r.2.1.val ≤ 1073741824 ∧
        (r.2.2 = true → ok0 = true ∧ Checked lfreq.val lit.lens.val 286) ⦄ := by
  unfold cost_histograms_loop0
  apply loop.spec_decr_nat (fun r => 286 - r.2.2.2.2.val)
    (fun r => r.1 = lit ∧ Inv lfreq.val lit.lens.val 286 ok0 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2)
  · rintro ⟨lit1, cost1, fixed1, ok2, s1⟩ ⟨hlit, hinv⟩
    dsimp only at hlit hinv ⊢
    subst lit1
    refine WP.spec_mono (body0 lfreq lit cost1 fixed1 ok0 ok2 s1 hlen hinv) ?_
    intro r hr
    cases r with
    | done r => exact hr
    | cont r => exact ⟨⟨hr.1, hr.2.1⟩, by have := hr.2.1.1; omega⟩
  · exact ⟨rfl, hi⟩

theorem loop1 (dfreq : alloc.vec.Vec Usize) (dist : Code) (cost fixed : Usize) (ok0 ok1 : Bool) (s : Usize)
    (hlen : dfreq.val.length = 30) (hi : Inv dfreq.val dist.lens.val 30 ok0 cost fixed ok1 s) :
    cost_histograms_loop1 dfreq dist cost fixed ok1 s ⦃ r =>
      r.1.val ≤ 1073741824 ∧ r.2.1.val ≤ 1073741824 ∧
        (r.2.2 = true → ok0 = true ∧ Checked dfreq.val dist.lens.val 30) ⦄ := by
  unfold cost_histograms_loop1
  apply loop.spec_decr_nat (fun r => 30 - r.2.2.2.2.val)
    (fun r => r.1 = dist ∧ Inv dfreq.val dist.lens.val 30 ok0 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2)
  · rintro ⟨dist1, cost1, fixed1, ok2, s1⟩ ⟨hdist, hinv⟩
    dsimp only at hdist hinv ⊢
    subst dist1
    refine WP.spec_mono (body1 dfreq dist cost1 fixed1 ok0 ok2 s1 hlen hinv) ?_
    intro r hr
    cases r with
    | done r => exact hr
    | cont r => exact ⟨⟨hr.1, hr.2.1⟩, by have := hr.2.1.1; omega⟩
  · exact ⟨rfl, hi⟩

theorem cost_histograms_spec (lfreq dfreq : alloc.vec.Vec Usize) (lit dist : Code)
    (hlf : lfreq.val.length = 286) (hdf : dfreq.val.length = 30) :
    cost_histograms lfreq dfreq lit dist ⦃ r => r.1.val ≤ 1073741824 ∧
      (r.2.2 = true → Checked lfreq.val lit.lens.val 286 ∧ Checked dfreq.val dist.lens.val 30) ⦄ := by
  unfold cost_histograms
  have hl : alloc.vec.Vec.len lfreq = 286#usize := by
    apply (UScalar.eq_equiv _ _).mpr; simpa using hlf
  have hd : alloc.vec.Vec.len dfreq = 30#usize := by
    apply (UScalar.eq_equiv _ _).mpr; simpa using hdf
  simp only [hl, hd, ↓reduceIte, bind_ok]
  have h0 := loop0 lfreq lit 0#usize 0#usize true (decide True) 0#usize hlf
    ⟨by simp, by simp, by simp, fun _ => ⟨rfl, fun k hk => by simp at hk⟩⟩
  step as ⟨cost, fixed, ok1, hc, hf, hok⟩
  have h1 := loop1 dfreq dist cost fixed ok1 ok1 0#usize hdf
    ⟨by simp, hc, hf, fun h => ⟨h, fun k hk => by simp at hk⟩⟩
  step as ⟨r, hc1, hf1, hok1⟩
  exact ⟨hc1, fun h => ⟨hok (hok1 h).1, (hok1 h).2⟩⟩

end Gzip.Proofs.CostHistogram
