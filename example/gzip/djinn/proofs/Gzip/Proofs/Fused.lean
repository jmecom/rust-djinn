import Gzip.Proofs.Symbolize
import Gzip.Proofs.Histogram
import Gzip.Proofs.Body

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Plans Gzip.Proofs.Matches

set_option maxHeartbeats 3000000

namespace Gzip.Proofs.Fused

structure Counts (lit dist : alloc.vec.Vec Usize) (n : ℕ) : Prop where
  litLen : lit.val.length = 286
  distLen : dist.val.length = 30
  litBound : ∀ i < 286, (lit.val[i]!).val ≤ n
  distBound : ∀ i < 30, (dist.val[i]!).val ≤ n

def Mono (before after : List Usize) : Prop :=
  ∀ i : Nat, (before[i]!).val ≤ (after[i]!).val

theorem mono_set (v : List Usize) (j : Nat) (x : Usize)
    (hx : (v[j]!).val ≤ x.val) : Mono v (v.set j x) := by
  intro i
  by_cases hi : i < v.length
  · rw [Djinn.Vocab.getElem!_set v j i x hi]
    split
    · rename_i h
      simpa [h] using hx
    · exact Nat.le_refl _
  · have hi' : ¬ i < (v.set j x).length := by simpa using hi
    rw [getElem!_neg v i hi, getElem!_neg (v.set j x) i hi']

def Counted (data : List U8) (p : Nat) (dd l d : Usize)
    (lit dist : List Usize) : Prop :=
  (dd.val = 0 → 0 < (lit[(data[p]!).val]!).val) ∧
  (dd.val ≠ 0 → l.val < 29 → d.val < 30 →
    0 < (lit[257 + l.val]!).val ∧ 0 < (dist[d.val]!).val)

theorem count_supported (data : Aeneas.Std.Slice U8) (p dd l d : Usize)
    (lit dist : alloc.vec.Vec Usize) (n : ℕ)
    (hp : p.val < data.val.length) (hn : n ≤ 1048576) (h : Counts lit dist n) :
    count_symbols data p dd l d lit dist ⦃ r => Counts r.1 r.2 (n + 1) ∧
      Mono lit.val r.1.val ∧ Mono dist.val r.2.val ∧
      Counted data.val p.val dd l d r.1.val r.2.val ⦄ := by
  obtain ⟨hlit, hdist, hlb, hdb⟩ := h
  have hlb' : ∀ i < lit.val.length, (lit.val[i]!).val ≤ n := by rw [hlit]; exact hlb
  have hdb' : ∀ i < dist.val.length, (dist.val[i]!).val ≤ n := by rw [hdist]; exact hdb
  unfold count_symbols
  split
  · rename_i hzero
    have hz : dd.val = 0 := by scalar_tac
    step as ⟨b, hb⟩
    step as ⟨s, hs⟩
    have hsv : s.val = (data.val[p.val]!).val := by
      rw [hs, UScalar.cast_val_eq, hb, getElem!_pos data.val p.val hp]
      apply Nat.mod_eq_of_lt
      scalar_tac
    have hsl : s.val < lit.val.length := by rw [hlit]; scalar_tac
    step as ⟨x, hx⟩
    have hxb : x.val ≤ n := by rw [hx, ← getElem!_pos lit.val s.val hsl]; exact hlb' s.val hsl
    step as ⟨c, hc⟩
    step as ⟨old, back, ho, hback⟩
    simp only [hback, alloc.vec.Vec.set_val_eq, WP.spec_ok]
    refine ⟨⟨by simpa, hdist, ?_, fun i hi => Nat.le_succ_of_le (hdb i hi)⟩,
      mono_set lit.val s.val c ?_, (fun i => Nat.le_refl _), ?_⟩
    · have hh := Histogram.bound_set hlb' s.val c (by omega)
      simpa only [alloc.vec.Vec.set_val_eq, List.length_set, hlit] using hh
    · rw [hc, hx, ← getElem!_pos lit.val s.val hsl]
      omega
    · refine ⟨?_, fun hdn => False.elim (hdn hz)⟩
      intro _
      rw [← hsv, Djinn.Vocab.getElem!_set lit.val s.val s.val c hsl, if_pos rfl]
      omega
  · rename_i hnonzero
    have hnz : dd.val ≠ 0 := by scalar_tac
    split
    · split
      · step as ⟨s, hs⟩
        have hsl : s.val < lit.val.length := by rw [hlit]; scalar_tac
        have hdl : d.val < dist.val.length := by rw [hdist]; scalar_tac
        step as ⟨x, hx⟩
        have hxb : x.val ≤ n := by rw [hx, ← getElem!_pos lit.val s.val hsl]; exact hlb' s.val hsl
        step as ⟨c, hc⟩
        step as ⟨old, back, ho, hback⟩
        step as ⟨y, hy⟩
        have hyb : y.val ≤ n := by rw [hy, ← getElem!_pos dist.val d.val hdl]; exact hdb' d.val hdl
        step as ⟨e, he⟩
        step as ⟨old1, back1, ho1, hback1⟩
        simp only [hback, hback1, alloc.vec.Vec.set_val_eq, WP.spec_ok]
        refine ⟨⟨by simpa, by simpa, ?_, ?_⟩, mono_set lit.val s.val c ?_,
          mono_set dist.val d.val e ?_, ?_⟩
        · have hh := Histogram.bound_set hlb' s.val c (by omega)
          simpa only [alloc.vec.Vec.set_val_eq, List.length_set, hlit] using hh
        · have hh := Histogram.bound_set hdb' d.val e (by omega)
          simpa only [alloc.vec.Vec.set_val_eq, List.length_set, hdist] using hh
        · rw [hc, hx, ← getElem!_pos lit.val s.val hsl]
          omega
        · rw [he, hy, ← getElem!_pos dist.val d.val hdl]
          omega
        · refine ⟨fun hz => False.elim (hnz hz), ?_⟩
          intro _ _ _
          have hsv : s.val = 257 + l.val := hs
          rw [← hsv, Djinn.Vocab.getElem!_set lit.val s.val s.val c hsl, if_pos rfl,
            Djinn.Vocab.getElem!_set dist.val d.val d.val e hdl, if_pos rfl]
          exact ⟨by omega, by omega⟩
      · rename_i hlarge
        simp only [WP.spec_ok]
        refine ⟨⟨hlit, hdist, fun i hi => Nat.le_succ_of_le (hlb i hi), fun i hi => Nat.le_succ_of_le (hdb i hi)⟩,
          (fun i => Nat.le_refl _), (fun i => Nat.le_refl _),
          ⟨fun hz => False.elim (hnz hz), ?_⟩⟩
        intro _ _ hdsmall
        scalar_tac
    · rename_i hlarge
      simp only [WP.spec_ok]
      refine ⟨⟨hlit, hdist, fun i hi => Nat.le_succ_of_le (hlb i hi), fun i hi => Nat.le_succ_of_le (hdb i hi)⟩,
        (fun i => Nat.le_refl _), (fun i => Nat.le_refl _),
        ⟨fun hz => False.elim (hnz hz), ?_⟩⟩
      intro _ hlsmall _
      scalar_tac

@[step]
theorem count_spec (data : Aeneas.Std.Slice U8) (p dd l d : Usize)
    (lit dist : alloc.vec.Vec Usize) (n : ℕ)
    (hp : p.val < data.val.length) (hn : n ≤ 1048576) (h : Counts lit dist n) :
    count_symbols data p dd l d lit dist ⦃ r => Counts r.1 r.2 (n + 1) ⦄ := by
  exact WP.spec_mono (count_supported data p dd l d lit dist n hp hn h) (fun _ h => h.1)

def SupportAt (data : List U8) (start : Nat) (ls ds : List U16) (lsym dsym : List U8) (lit dist : List Usize)
    (t : Nat) : Prop :=
  if (ds[t]!).val = 0 then 0 < (lit[(data[Body.pos ls start t]!).val]!).val
  else 0 < (lit[257 + (lsym[t]!).val]!).val ∧ 0 < (dist[(dsym[t]!).val]!).val

def Support (data : List U8) (start : Nat) (ls ds : List U16) (lsym dsym : List U8) (lit dist : List Usize) : Prop :=
  (∀ t < ls.length, SupportAt data start ls ds lsym dsym lit dist t) ∧ 0 < (lit[256]!).val

theorem supportAt_mono {data : List U8} {start t : Nat}
    {ls ds : List U16} {lsym dsym : List U8} {lit dist lit' dist' : List Usize}
    (hl : Mono lit lit') (hd : Mono dist dist')
    (h : SupportAt data start ls ds lsym dsym lit dist t) :
    SupportAt data start ls ds lsym dsym lit' dist' t := by
  unfold SupportAt at h ⊢
  split at h
  · rename_i hz
    rw [if_pos hz]
    exact Nat.lt_of_lt_of_le h (hl _)
  · rename_i hnz
    rw [if_neg hnz]
    exact ⟨Nat.lt_of_lt_of_le h.1 (hl _), Nat.lt_of_lt_of_le h.2 (hd _)⟩

structure State (data : List U8) (start stop : ℕ) (ls ds : List U16)
    (lsym dsym : alloc.vec.Vec U8) (lit dist : alloc.vec.Vec Usize) (p t : Usize) : Prop where
  position : p.val ≤ stop ∧ stop ≤ data.length
  location : p.val = Body.pos ls start t.val
  lengths : ls.length = ds.length
  index : t.val ≤ ls.length
  runs : Runs data stop p.val stop (ls.drop t.val) (ds.drop t.val)
  lsymLen : lsym.val.length = t.val
  dsymLen : dsym.val.length = t.val
  symbols : ∀ t' < t.val, (ds[t']!).val ≠ 0 →
    (lsym.val[t']!).val ≤ 28 ∧ (dsym.val[t']!).val ≤ 29 ∧
    Indices.lb (lsym.val[t']!).val ≤ (ls[t']!).val ∧
    (ls[t']!).val - Indices.lb (lsym.val[t']!).val < 2 ^ Indices.le (lsym.val[t']!).val ∧
    Indices.db (dsym.val[t']!).val ≤ (ds[t']!).val ∧
    (ds[t']!).val - Indices.db (dsym.val[t']!).val < 2 ^ Indices.de (dsym.val[t']!).val
  counts : Counts lit dist t.val
  support : ∀ j < t.val, SupportAt data start ls ds lsym.val dsym.val lit.val dist.val j

theorem body (data : Aeneas.Std.Slice U8) (start stop : ℕ) (ls ds : alloc.vec.Vec U16)
    (lsym dsym : alloc.vec.Vec U8) (lit dist : alloc.vec.Vec Usize) (p t : Usize)
    (hv : Symbolize.ValidPlan ls.val ds.val)
    (h : State data.val start stop ls.val ds.val lsym dsym lit dist p t)
    (hsize : ls.val.length ≤ 1048576) :
    symbols_histogram_loop.body data ls ds lsym dsym lit dist p t ⦃ r =>
      match r with
      | .done (lsym', dsym', lit', dist') =>
          Symbolize.Symbolized ls.val ds.val lsym'.val dsym'.val ∧ Counts lit' dist' ls.val.length ∧
          ∀ j < ls.val.length, SupportAt data.val start ls.val ds.val lsym'.val dsym'.val lit'.val dist'.val j
      | .cont (lsym', dsym', lit', dist', p', t') =>
          State data.val start stop ls.val ds.val lsym' dsym' lit' dist' p' t' ∧ t'.val = t.val + 1 ⦄ := by
  obtain ⟨hp, hlocal, hlen, ht, hr, hlsym, hdsym, hprev, hc, hsupp⟩ := h
  unfold symbols_histogram_loop.body
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
        ok (l, d)) ⦃ r => (ds.val[t.val]!).val ≠ 0 →
        r.1.val ≤ 28 ∧ r.2.val ≤ 29 ∧
        Indices.lb r.1.val ≤ (ls.val[t.val]!).val ∧
        (ls.val[t.val]!).val - Indices.lb r.1.val < 2 ^ Indices.le r.1.val ∧
        Indices.db r.2.val ≤ (ds.val[t.val]!).val ∧
        (ds.val[t.val]!).val - Indices.db r.2.val < 2 ^ Indices.de r.2.val ⦄ := by
      split
      · rename_i hz0
        try simp only [WP.spec_ok]
        intro hdn
        have hd0 : dd.val = 0 := by scalar_tac
        rw [hdget] at hd0
        exact absurd hd0 hdn
      · rename_i hdn0
        have hdn : dd.val ≠ 0 := by scalar_tac
        obtain ⟨h3, h258, h1, h32⟩ := hnz hdn
        step as ⟨l, hl0, hl1, hl2⟩
        step as ⟨d, hd0, hd1, hd2⟩
        try simp only [WP.spec_ok]
        intro _
        rw [← hlget, ← hdget]
        exact ⟨hl0, hd0, hl1, hl2, hd1, hd2⟩
    step as ⟨l, d, hnew⟩
    step as ⟨l8, hl8⟩
    step as ⟨lsym1, hlsym1⟩
    step as ⟨d8, hd8⟩
    step as ⟨dsym1, hdsym1⟩
    have hcast : (ds.val[t.val]!).val ≠ 0 → l8.val = l.val ∧ d8.val = d.val := by
      intro hn
      have hb := hnew hn
      constructor
      · rw [hl8]; exact Symbolize.narrow8_val l (by omega)
      · rw [hd8]; exact Symbolize.narrow8_val d (by omega)
    have hnew8 : (ds.val[t.val]!).val ≠ 0 →
        l8.val ≤ 28 ∧ d8.val ≤ 29 ∧
        Indices.lb l8.val ≤ (ls.val[t.val]!).val ∧
        (ls.val[t.val]!).val - Indices.lb l8.val < 2 ^ Indices.le l8.val ∧
        Indices.db d8.val ≤ (ds.val[t.val]!).val ∧
        (ds.val[t.val]!).val - Indices.db d8.val < 2 ^ Indices.de d8.val := by
      intro hn
      rw [(hcast hn).1, (hcast hn).2]
      exact hnew hn
    have hcs := count_supported data p dd l d lit dist t.val (by omega) (by omega) hc
    step as ⟨lit1, dist1, hc1, hlmono, hdmono, hcounted⟩
    step as ⟨p1, hp1⟩
    step as ⟨t1, ht1⟩
    try simp only [WP.spec_ok]
    refine ⟨⟨⟨by omega, hp.2⟩, ?_, hlen, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ht1⟩
    · rw [hp1, ht1, Body.pos_succ ls.val start t.val hlt', ← hlocal, ← hlget]
    · simpa only [hp1, ht1] using htail
    · simp only [hlsym1, List.length_append, List.length_singleton, hlsym, ht1]
    · simp only [hdsym1, List.length_append, List.length_singleton, hdsym, ht1]
    · rw [hlsym1, hdsym1, ht1]
      exact Symbolize.symbolized_extend l8 d8 hlsym hdsym hlt' hprev hnew8
    · rw [ht1]
      exact hc1
    · rw [ht1, hlsym1, hdsym1]
      intro j hj
      by_cases hjold : j < t.val
      · have hjls : j < lsym.val.length := by omega
        have hjds : j < dsym.val.length := by omega
        have hold := supportAt_mono hlmono hdmono (hsupp j hjold)
        unfold SupportAt at hold ⊢
        rw [List.getElem!_append_left lsym.val [l8] j hjls,
          List.getElem!_append_left dsym.val [d8] j hjds]
        exact hold
      · have hje : j = t.val := by omega
        subst j
        unfold SupportAt
        rw [← hdget, ← hlocal]
        by_cases hzero : dd.val = 0
        · rw [if_pos hzero]
          exact hcounted.1 hzero
        · rw [if_neg hzero, List.getElem!_append_right lsym.val [l8] t.val (by omega),
            List.getElem!_append_right dsym.val [d8] t.val (by omega)]
          simp only [hlsym, hdsym, Nat.sub_self, List.getElem!_cons_zero]
          have hdn : (ds.val[t.val]!).val ≠ 0 := by rw [← hdget]; exact hzero
          have hlimits := hnew hdn
          rw [(hcast hdn).1, (hcast hdn).2]
          exact hcounted.2 hzero (by omega) (by omega)
  · rename_i hge
    have he : t.val = ls.val.length := by scalar_tac
    simp only [WP.spec_ok]
    refine ⟨⟨by omega, by omega, fun t' ht' => hprev t' (by omega)⟩, ?_, ?_⟩
    · rw [← he]
      exact hc
    · intro j hj
      exact hsupp j (by omega)

@[step]
theorem loop (data : Aeneas.Std.Slice U8) (start stop : ℕ) (ls ds : alloc.vec.Vec U16)
    (lsym dsym : alloc.vec.Vec U8) (lit dist : alloc.vec.Vec Usize) (p t : Usize)
    (hv : Symbolize.ValidPlan ls.val ds.val)
    (h : State data.val start stop ls.val ds.val lsym dsym lit dist p t)
    (hsize : ls.val.length ≤ 1048576) :
    symbols_histogram_loop data ls ds lsym dsym lit dist p t ⦃ r =>
      Symbolize.Symbolized ls.val ds.val r.1.val r.2.1.val ∧ Counts r.2.2.1 r.2.2.2 ls.val.length ∧
      ∀ j < ls.val.length, SupportAt data.val start ls.val ds.val r.1.val r.2.1.val r.2.2.1.val r.2.2.2.val j ⦄ := by
  unfold symbols_histogram_loop
  apply loop.spec_decr_nat (fun (_, _, _, _, _, j) => ls.val.length - j.val)
    (fun (lsym', dsym', lit', dist', p', t') => State data.val start stop ls.val ds.val lsym' dsym' lit' dist' p' t')
  · rintro ⟨lsym', dsym', lit', dist', p', t'⟩ h'
    refine WP.spec_mono (body data start stop ls ds lsym' dsym' lit' dist' p' t' hv h' hsize) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨lsym'', dsym'', lit'', dist'', p'', t''⟩ := state
        exact ⟨hr.1, by change ls.val.length - t''.val < ls.val.length - t'.val; have := hr.1.index; have := hr.2; omega⟩
  · exact h

theorem correct (data : Aeneas.Std.Slice U8) (start : Usize) (ls ds : alloc.vec.Vec U16) (stop : ℕ)
    (hr : Runs data.val stop start.val stop ls.val ds.val) (hd : stop ≤ data.val.length)
    (hsize : ls.val.length ≤ 1048576) :
    symbols_histogram data start ls ds ⦃ r =>
      Symbolize.Symbolized ls.val ds.val r.1.val r.2.1.val ∧
        r.2.2.1.val.length = 286 ∧ r.2.2.2.val.length = 30 ∧
        Support data.val start.val ls.val ds.val r.1.val r.2.1.val r.2.2.1.val r.2.2.2.val ⦄ := by
  have hvalid := Symbolize.runs_valid hr
  unfold symbols_histogram
  step as ⟨lit, hlit⟩
  step as ⟨dist, hdist⟩
  have hlen := runs_lengths hr
  have hstate : State data.val start.val stop ls.val ds.val
      (alloc.vec.Vec.with_capacity U8 ls.len) (alloc.vec.Vec.with_capacity U8 ls.len)
      lit dist start 0#usize := by
    refine ⟨⟨runs_bound hr, hd⟩, by simp, hlen.1, by simp, by simpa using hr, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · intro t ht
      simp at ht
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hlit, List.length_replicate]
      · rw [hdist, List.length_replicate]
      · intro i hi
        rw [hlit, List.getElem!_replicate] <;> scalar_tac
      · intro i hi
        rw [hdist, List.getElem!_replicate] <;> scalar_tac
    · intro j hj
      simp at hj
  have hl := loop data start.val stop ls ds _ _ lit dist start 0#usize hvalid hstate hsize
  step as ⟨lsym, dsym, lit1, dist1, hsym, hc, hsupp⟩
  have h256 : (256 : ℕ) < lit1.val.length := by rw [hc.litLen]; omega
  step as ⟨i, hi⟩
  have hib : i.val ≤ ls.val.length := by rw [hi, ← getElem!_pos lit1.val 256 h256]; exact hc.litBound 256 (by omega)
  step as ⟨c, hcc⟩
  step as ⟨x, back, hx, hback⟩
  simp only [hback, alloc.vec.Vec.set_val_eq, List.length_set, WP.spec_ok]
  refine ⟨hsym, hc.litLen, hc.distLen, ?_, ?_⟩
  · intro j hj
    exact supportAt_mono (mono_set lit1.val 256 c (by rw [hcc, hi, ← getElem!_pos lit1.val 256 h256]; omega))
      (fun i => Nat.le_refl _) (hsupp j hj)
  · simp only [UScalar.ofNatCore_val_eq]
    rw [Djinn.Vocab.getElem!_set lit1.val 256 256 c h256, if_pos rfl]
    omega

end Gzip.Proofs.Fused
