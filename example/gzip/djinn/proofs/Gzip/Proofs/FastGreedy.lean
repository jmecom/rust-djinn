import Gzip.Proofs.Plans
import Gzip.Proofs.Chains
import Gzip.Proofs.Counting

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Plans Gzip.Proofs.Matches Gzip.Proofs.Chains

set_option maxHeartbeats 2000000

namespace Gzip.Proofs.Greedy

@[step]
theorem first_match_correct (data : Aeneas.Std.Slice U8) (p stop h : Usize)
    (head : alloc.vec.Vec U32) (hp : p.val < stop.val) (hd : stop.val ≤ data.val.length) :
    first_match data p stop h head ⦃ r =>
      2 ≤ r.1.1.val ∧ r.1.1.val ≤ 258 ∧
      ValidMatch data.val p.val stop.val r.1.1.val r.1.2.val ∧
      r.2.val.length = head.val.length ⦄ := by
  unfold first_match
  step*
  · rw [index_mut_back_post]
    simp only [alloc.vec.Vec.set_val_eq, List.length_set, and_true]
    refine ⟨by scalar_tac, n_post, Or.inr ?_⟩
    refine ⟨by scalar_tac, n_post, by omega, by scalar_tac,
      by omega, by scalar_tac, ?_⟩
    have hdiff : p.val - i4.val = q.val := by omega
    rw [hdiff]
    exact n_post2
  all_goals first
    | simp [ValidMatch, index_mut_back_post, alloc.vec.Vec.set_val_eq]
    | simp [ValidMatch]

@[step]
theorem first_insert_correct (data : Aeneas.Std.Slice U8) (p : Usize)
    (head : alloc.vec.Vec U32) (hp : p.val < data.val.length) (hh : 0 < head.val.length) :
    first_insert data p head ⦃ r => r.val.length = head.val.length ⦄ := by
  have hp' : p.val ≤ data.val.length := by omega
  unfold first_insert
  step as ⟨h, _⟩
  split
  · step*
    rw [index_mut_back_post]
    simp only [alloc.vec.Vec.set_val_eq, List.length_set]
  · step*

@[step]
theorem next_misses_correct (misses : U32) :
    next_misses misses ⦃ _ => True ⦄ := by
  unfold next_misses
  step*

end Gzip.Proofs.Greedy

namespace Gzip.Proofs.FastGreedy

theorem literal_runs (data : List U8) (stop p n : ℕ) :
    Runs data stop p (p + n) (List.replicate n 1#u16) (List.replicate n 0#u16) := by
  induction n generalizing p with
  | zero => simpa using Runs.finish (data := data) (stop := stop) p
  | succ n ih =>
      simp only [List.replicate_succ]
      apply Runs.next p (p + (n + 1)) 1#u16 0#u16
      · exact Or.inl ⟨by scalar_tac, by scalar_tac⟩
      · simpa only [show (1#u16).val = 1 from rfl, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using ih (p + 1)

theorem append_literals {data : List U8} {stop start p : ℕ} {ls ds : List U16}
    (hr : Runs data stop start p ls ds) (n : ℕ) :
    Runs data stop start (p + n)
      (ls ++ List.replicate n 1#u16) (ds ++ List.replicate n 0#u16) :=
  runs_concat hr (literal_runs data stop p n)

theorem resize_append {α : Type} (xs : List α) (n : ℕ) (x : α) (hn : xs.length ≤ n) :
    xs.resize n x = xs ++ List.replicate (n - xs.length) x := by
  unfold List.resize
  rw [List.take_of_length_le hn]
  simp

/-- The loop invariant: the plan so far is a run of valid steps, the head table is nonempty,
and the symbol indices and counts are the plan's. Level 1 has no link table, and its miss
counter needs no invariant (the sampling bound comes from `sample_gap`). -/
def State (data : List U8) (start stop p : ℕ) (head : List U32)
    (ls ds : List U16) (lsym dsym : List U8) (lit dist : alloc.vec.Vec Usize) : Prop :=
  start ≤ p ∧ p ≤ stop ∧ 0 < head.length ∧ Runs data stop start p ls ds ∧
  Counting.Counted data start ls ds lsym dsym lit dist

def Final (data : List U8) (start stop : ℕ) (head : List U32)
    (ls ds : List U16) (lsym dsym : List U8) (lit dist : alloc.vec.Vec Usize) : Prop :=
  0 < head.length ∧ Runs data stop start stop ls ds ∧
  Counting.Counted data start ls ds lsym dsym lit dist

@[step]
theorem sample_gap_correct (misses : U32) :
    sample_gap misses ⦃ gap => gap.val ≤ 16 ∧ (0 < gap.val → misses.val < 128) ⦄ := by
  have hmask : (misses &&& 15#u32).val ≤ 15 := by
    rw [UScalar.val_and]
    exact Nat.and_le_right
  have hcast : (UScalar.cast .Usize (misses &&& 15#u32)).val ≤ 15 := by
    rw [UScalar.cast_val_eq]
    exact (Nat.mod_le _ _).trans hmask
  unfold sample_gap
  step*

@[step]
theorem advance_misses_correct (misses skip : U32) (hm : misses.val < 128) (hs : skip.val ≤ 16) :
    advance_misses misses skip ⦃ _ => True ⦄ := by
  unfold advance_misses
  step*


theorem position_body (data : Aeneas.Std.Slice U8) (start : ℕ) (stop : Usize)
    (head : alloc.vec.Vec U32) (ls ds : alloc.vec.Vec U16) (lsym dsym : alloc.vec.Vec U8)
    (lit dist : alloc.vec.Vec Usize) (p : Usize) (misses : U32)
    (h : State data.val start stop.val p.val head.val ls.val ds.val lsym.val dsym.val lit dist)
    (hd : stop.val ≤ data.val.length) (hs : stop.val - start ≤ 32768) :
    greedy_fast_loop.body data stop head ls ds lsym dsym lit dist p misses ⦃ r =>
      match r with
      | .done (hh, l, d, ls', ds', li, di) =>
          Final data.val start stop.val hh.val l.val d.val ls'.val ds'.val li di
      | .cont (hh, l, d, ls', ds', li, di, next, _) =>
          State data.val start stop.val next.val hh.val l.val d.val ls'.val ds'.val li di ∧
          p.val < next.val ⦄ := by
  obtain ⟨hp0, hp1, ht, hr, hcnt⟩ := h
  have hll := runs_lengths hr
  have hls : ls.val.length ≤ 32768 := by omega
  have hds : ds.val.length ≤ 32768 := by omega
  have hlsl := hcnt.symbolized.1
  have hdsl := hcnt.symbolized.2.1
  have hcounts := hcnt.counts
  have hppos := Counting.runs_pos hr
  unfold greedy_fast_loop.body
  split
  · have hplt : p.val < stop.val := by scalar_tac
    step as ⟨gap, hgap, hgapmiss⟩
    split
    · have hgap0 : 0 < gap.val := by scalar_tac
      have hmiss128 := hgapmiss hgap0
      step as ⟨remaining, hremaining⟩
      have hremaining0 : 0 < remaining.val := by omega
      have hskip :
          (if remaining < gap then ok remaining else ok gap) ⦃ skip =>
            0 < skip.val ∧ skip.val ≤ remaining.val ∧ skip.val ≤ 16 ⦄ := by
        split <;> simp only [WP.spec_ok] <;> scalar_tac
      step as ⟨skip, hskip0, hskiprem, hskip16⟩
      step as ⟨i1, hi1⟩
      have hr1 := alloc.vec.Vec.resize_spec core.clone.CloneU16 ls i1 1#u16 (by rfl)
      step as ⟨v2, hv2⟩
      step as ⟨i3, hi3⟩
      have hr3 := alloc.vec.Vec.resize_spec core.clone.CloneU16 ds i3 0#u16 (by rfl)
      step as ⟨v3, hv3⟩
      step as ⟨i5, hi5⟩
      have hr5 := alloc.vec.Vec.resize_spec core.clone.CloneU8 lsym i5 0#u8 (by rfl)
      step as ⟨lsym1, hlsym1⟩
      step as ⟨i7, hi7⟩
      have hr7 := alloc.vec.Vec.resize_spec core.clone.CloneU8 dsym i7 0#u8 (by rfl)
      step as ⟨dsym1, hdsym1⟩
      have hcl := Counting.count_literals_spec data p skip lit dist ls.val.length (by omega) (by omega) hcounts
      step as ⟨lit1, dist1, hc1, hl1, hd1, hcounted⟩
      step as ⟨skipped, hskipped⟩
      have hskipped16 : skipped.val ≤ 16 := by
        rw [hskipped, UScalar.cast_val_eq]
        exact (Nat.mod_le _ _).trans hskip16
      step as ⟨misses1⟩
      step as ⟨next, hnext⟩
      simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length] at hi1 hi3 hi5 hi7
      rw [resize_append ls.val i1.val 1#u16 (by omega)] at hv2
      rw [resize_append ds.val i3.val 0#u16 (by omega)] at hv3
      rw [resize_append lsym.val i5.val 0#u8 (by omega)] at hlsym1
      rw [resize_append dsym.val i7.val 0#u8 (by omega)] at hdsym1
      have hsize1 : i1.val - ls.val.length = skip.val := by omega
      have hsize3 : i3.val - ds.val.length = skip.val := by omega
      have hsize5 : i5.val - lsym.val.length = skip.val := by omega
      have hsize7 : i7.val - dsym.val.length = skip.val := by omega
      rw [hsize1] at hv2
      rw [hsize3] at hv3
      rw [hsize5] at hlsym1
      rw [hsize7] at hdsym1
      try simp only [WP.spec_ok]
      refine ⟨⟨by omega, by omega, ht, ?_, ?_⟩, by omega⟩
      · rw [hv2, hv3, hnext]
        exact append_literals hr skip.val
      · rw [hv2, hv3, hlsym1, hdsym1]
        exact Counting.counted_literals hcnt hll.1.symm p.val skip.val hppos hc1 hl1 hd1 hcounted
    · step as ⟨h, _⟩
      step as ⟨len, dist16, head1, hl0, hl1, hm, hhead⟩
      try dsimp only at hm hl0 hl1
      have hmiss : ((if dist16 != 0#usize then ok 0#u32 else next_misses misses) : Result U32)
          ⦃ _ => True ⦄ := by
        split
        · simp
        · exact Gzip.Proofs.Greedy.next_misses_correct misses
      step with hmiss as ⟨misses1⟩
      have ht1 : 0 < head1.val.length := by rw [hhead]; exact ht
      have hlit := runs_append hr 1#u16 0#u16 (Or.inl ⟨by scalar_tac, by scalar_tac⟩)
      step as ⟨b, hb⟩
      split
      · rename_i hbt
        have hdpos : 0 < dist16.val := hb hbt
        have hcopy := hm.resolve_left (by omega)
        have hstep : Step data.val p.val stop.val len dist16 := Or.inr ⟨hm, hdpos⟩
        have hrnew := runs_append hr (UScalar.cast .U16 len) (UScalar.cast .U16 dist16) (step_narrow hstep)
        rw [narrow_val len (by omega)] at hrnew
        have hlen3 : 3 ≤ len.val := hcopy.1
        have hlen258 : len.val ≤ 258 := hcopy.2.1
        have hpl : p.val + len.val ≤ data.val.length := by have := hcopy.2.2.1; omega
        have hd32 : dist16.val ≤ 32768 := hcopy.2.2.2.2.2.1
        step as ⟨i, hi⟩
        step as ⟨v2, hv2⟩
        step as ⟨i1, hi1⟩
        step as ⟨v3, hv3⟩
        step as ⟨l, hl0', hl1', hl2'⟩
        step as ⟨dc, hd0', hd1', hd2'⟩
        step as ⟨i2, hi2⟩
        step as ⟨lsym1, hlsym1⟩
        step as ⟨i3, hi3⟩
        step as ⟨dsym1, hdsym1⟩
        have hcs := Fused.count_supported data p dist16 l dc lit dist ls.val.length (by omega) (by omega) hcounts
        step as ⟨lit1, dist1, hc1, hlm1, hdm1, hcounted⟩
        have hkeep : (if dist16 < len then len - dist16 else len - 1#usize)
            ⦃ k => k.val < len.val ⦄ := by
          split <;> step* <;> omega
        step with hkeep as ⟨keep, hkeepLen⟩
        step as ⟨kept, hkept⟩
        have hkeptData : kept.val < data.val.length := by omega
        have hinsert := Gzip.Proofs.Greedy.first_insert_correct data kept head1 hkeptData ht1
        step as ⟨head2, hhead2⟩
        have ht2 : 0 < head2.val.length := by rw [hhead2]; exact ht1
        step as ⟨p1, hp1⟩
        have hi2v : i2.val = l.val := by rw [hi2]; exact Symbolize.narrow8_val l (by omega)
        have hi3v : i3.val = dc.val := by rw [hi3]; exact Symbolize.narrow8_val dc (by omega)
        have hiv : i.val = len.val := by rw [hi]; exact narrow_val len (by omega)
        have hi1v : i1.val = dist16.val := by rw [hi1]; exact narrow_val dist16 (by omega)
        have hsupp := hcounted.2 (by omega) (by omega) (by omega)
        try simp only [WP.spec_ok]
        refine ⟨⟨by scalar_tac, by scalar_tac, ht2, ?_, ?_⟩, by scalar_tac⟩
        · rw [hv2, hv3, hp1, hi, hi1]
          exact hrnew
        · rw [hv2, hv3, hlsym1, hdsym1]
          refine Counting.counted_copy hcnt hll.1.symm i i1 i2 i3 (by rw [hi1v]; omega) ?_ hc1 hlm1 hdm1 ?_
          · rw [hi2v, hi3v, hiv, hi1v]
            exact ⟨hl0', hd0', hl1', hl2', hd1', hd2'⟩
          · rw [hi2v, hi3v]
            exact hsupp
      · step as ⟨v2, hv2⟩
        step as ⟨v3, hv3⟩
        step as ⟨lsym1, hlsym1⟩
        step as ⟨dsym1, hdsym1⟩
        have hcs := Fused.count_supported data p 0#usize 0#usize 0#usize lit dist ls.val.length (by omega) (by omega) hcounts
        step as ⟨lit1, dist1, hc1, hlm1, hdm1, hcounted⟩
        step as ⟨p1, hp1⟩
        try simp only [WP.spec_ok]
        refine ⟨⟨by scalar_tac, by scalar_tac, ht1, ?_, ?_⟩, by scalar_tac⟩
        · rw [hv2, hv3, hp1]
          simpa using hlit
        · rw [hv2, hv3, hlsym1, hdsym1]
          exact Counting.counted_literal hcnt hll.1.symm p.val hppos hc1 hlm1 hdm1 (hcounted.1 (by scalar_tac))
  · have he : p = stop := by
      apply (UScalar.eq_equiv _ _).mpr
      scalar_tac
    subst he
    simp only [WP.spec_ok]
    exact ⟨ht, hr, hcnt⟩

@[step]
theorem position_loop (data : Aeneas.Std.Slice U8) (start : ℕ) (stop : Usize)
    (head : alloc.vec.Vec U32) (ls ds : alloc.vec.Vec U16) (lsym dsym : alloc.vec.Vec U8)
    (lit dist : alloc.vec.Vec Usize) (p : Usize) (misses : U32)
    (h : State data.val start stop.val p.val head.val ls.val ds.val lsym.val dsym.val lit dist)
    (hd : stop.val ≤ data.val.length) (hs : stop.val - start ≤ 32768) :
    greedy_fast_loop data stop head ls ds lsym dsym lit dist p misses ⦃ r =>
      Final data.val start stop.val r.1.val r.2.1.val r.2.2.1.val r.2.2.2.1.val
        r.2.2.2.2.1.val r.2.2.2.2.2.1 r.2.2.2.2.2.2 ⦄ := by
  unfold greedy_fast_loop
  apply loop.spec_decr_nat (fun (_, _, _, _, _, _, _, q, _) => stop.val - q.val)
    (fun (hh, l, d, ls', ds', li, di, q, _) =>
      State data.val start stop.val q.val hh.val l.val d.val ls'.val ds'.val li di)
  · rintro ⟨hh, l, d, ls', ds', li, di, q, m⟩ hq
    refine WP.spec_mono (position_body data start stop hh l d ls' ds' li di q m hq hd hs) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨hh', l', d', ls'', ds'', li', di', q', m'⟩ := state
        obtain ⟨h', hnext⟩ := hr
        exact ⟨h', by have hb := h'.2.1; change stop.val - q'.val < stop.val - q.val; omega⟩
  · exact h

@[step]
theorem greedy_fast_correct (data : Aeneas.Std.Slice U8) (start stop : Usize)
    (head : alloc.vec.Vec U32) (ht : 0 < head.val.length)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length)
    (hsize : stop.val - start.val ≤ 32768) :
    greedy_fast data start stop head ⦃ r =>
      Counting.ParsedOk data.val start.val stop.val r.1 ∧ r.1.fused = true ∧
      0 < r.2.val.length ⦄ := by
  unfold greedy_fast
  dsimp only
  step as ⟨i, hi⟩
  step as ⟨lit, hlit⟩
  step as ⟨dist, hdist⟩
  have hinitial : State data.val start.val stop.val start.val head.val
      (alloc.vec.Vec.with_capacity U16 i).val (alloc.vec.Vec.with_capacity U16 i).val
      (alloc.vec.Vec.with_capacity U8 i).val (alloc.vec.Vec.with_capacity U8 i).val lit dist := by
    refine ⟨Nat.le_refl _, hs, ht, ?_, ?_⟩
    · simp only [alloc.vec.Vec.with_capacity]
      exact Runs.finish start.val
    · simp only [alloc.vec.Vec.with_capacity]
      exact Counting.counted_nil data.val start.val lit dist (by rw [hlit]) (by rw [hdist])
  step as ⟨head1, v2, v3, lsym1, dsym1, lit1, dist1, hstate⟩
  obtain ⟨ht1, hr1, hc1⟩ := hstate
  have h256 : (256 : ℕ) < lit1.val.length := by rw [hc1.counts.litLen]; omega
  have hll := runs_lengths hr1
  step as ⟨i1, hi1⟩
  have hib : i1.val ≤ v2.val.length := by
    rw [hi1, ← getElem!_pos lit1.val 256 h256]
    exact hc1.counts.litBound 256 (by omega)
  step as ⟨c, hcc⟩
  step as ⟨x, back, hx, hback⟩
  have hfin := Counting.counted_finish hc1 c (by rw [hcc, hi1, ← getElem!_pos lit1.val 256 h256]; omega) h256
  have hpost : Counting.ParsedOk data.val start.val stop.val
      (Parsed.mk (Plan.mk v2 v3) lsym1 dsym1 (back c) dist1 true) ∧
      (Parsed.mk (Plan.mk v2 v3) lsym1 dsym1 (back c) dist1 true).fused = true ∧
      0 < head1.val.length := by
    refine ⟨⟨hr1, fun _ => ?_⟩, rfl, ht1⟩
    simp only [hback, alloc.vec.Vec.set_val_eq, UScalar.ofNatCore_val_eq]
    exact hfin
  simpa only [WP.spec_ok, true_and] using hpost

end Gzip.Proofs.FastGreedy
