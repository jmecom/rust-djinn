import Gzip.Proofs.Merge

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Plans Gzip.Proofs.Body

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

/-! Cutting the first block of a file in two: the cut's choice is a heuristic (termination and
bounds only), the plan's cut is exact (the two parts are runs of tokens). -/

namespace Gzip.Proofs.Split

/-! ### Cutting a run of tokens in two -/

theorem pos_cons (l : U16) (ls : List U16) (p k : ℕ) :
    pos (l :: ls) p (k + 1) = pos ls (p + l.val) k := by
  simp only [pos, List.take_succ_cons, List.map_cons, List.sum_cons]
  omega

theorem runs_pos_le {data : List U8} {stop p q : ℕ} {ls ds : List U16}
    (h : Runs data stop p q ls ds) (k : ℕ) (hk : k ≤ ls.length) : pos ls p k ≤ q := by
  induction h generalizing k with
  | finish p =>
      simp only [List.length_nil, Nat.le_zero] at hk
      subst hk
      simp
  | next p q l d ls ds hv ht ih =>
      cases k with
      | zero =>
          have := runs_bound ht
          have := step_positive hv
          simp only [pos_zero]
          omega
      | succ k =>
          rw [pos_cons]
          exact ih k (by simp at hk; omega)

/-- A run of tokens ending at `q` is a run under the match bound `q`. -/
theorem runs_tighten {data : List U8} {stop p q : ℕ} {ls ds : List U16}
    (h : Runs data stop p q ls ds) : Runs data q p q ls ds := by
  induction h with
  | finish p => exact Runs.finish p
  | next p q l d ls ds hv ht ih =>
      have hb := runs_bound ht
      refine Runs.next p q l d ls ds ?_ ih
      rcases hv with hl | ⟨hm, hd⟩
      · exact Or.inl hl
      · right
        refine ⟨?_, hd⟩
        rcases hm with hm | hm
        · exact Or.inl hm
        · exact Or.inr ⟨hm.1, hm.2.1, by omega, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1, hm.2.2.2.2.2.2⟩

/-- The first `k` tokens of a run and the rest are runs. -/
theorem runs_split {data : List U8} {stop p q : ℕ} {ls ds : List U16}
    (h : Runs data stop p q ls ds) (k : ℕ) (hk : k ≤ ls.length) :
    Runs data stop p (pos ls p k) (ls.take k) (ds.take k) ∧
    Runs data stop (pos ls p k) q (ls.drop k) (ds.drop k) := by
  induction h generalizing k with
  | finish p =>
      simp only [List.length_nil, Nat.le_zero] at hk
      subst hk
      simp only [pos_zero, List.take_nil, List.drop_nil]
      exact ⟨Runs.finish p, Runs.finish p⟩
  | next p q l d ls ds hv ht ih =>
      cases k with
      | zero =>
          simp only [pos_zero, List.take_zero, List.drop_zero]
          exact ⟨Runs.finish p, Runs.next p q l d ls ds hv ht⟩
      | succ k =>
          rw [pos_cons]
          obtain ⟨h1, h2⟩ := ih k (by simp at hk; omega)
          simp only [List.take_succ_cons, List.drop_succ_cons]
          exact ⟨Runs.next p _ l d _ _ hv h1, h2⟩

/-! ### The cut heuristic: termination and bounds only -/

@[step]
theorem count_up_spec (x : Usize) : count_up x ⦃ _ => True ⦄ := by
  unfold count_up
  split
  · rename_i hlt
    have : x.val < 1073741824 := by scalar_tac
    step*
  · simp

@[step]
theorem length_code_any (len : Usize) : length_code len ⦃ _ => True ⦄ := by
  unfold length_code
  split
  · rename_i hlt
    have : len.val < 259 := by scalar_tac
    step*
  · simp

@[step]
theorem distance_code_any (dist : Usize) : distance_code dist ⦃ _ => True ⦄ := by
  unfold distance_code
  split
  · rename_i hlt
    have : dist.val < 257 := by scalar_tac
    step*
  · split
    · rename_i hge hlt
      have h1 : 257 ≤ dist.val := by scalar_tac
      have h2 : dist.val < 32769 := by scalar_tac
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      case hy => rcases System.Platform.numBits_eq with h | h <;> simp [h]
      have hk : i1.val = (dist.val - 1) / 128 := by
        rw [hi1, Nat.shiftRight_eq_div_pow, hi]
      have hk2 : i1.val < 256 := by rw [hk]; omega
      step*
    · simp

@[step]
theorem count_token_spec (data : Aeneas.Std.Slice U8) (p len dd : Usize) (lit dist : alloc.vec.Vec Usize)
    (hlit : lit.val.length = 286) (hdist : dist.val.length = 30) :
    count_token data p len dd lit dist ⦃ r => r.1.val.length = 286 ∧ r.2.val.length = 30 ⦄ := by
  unfold count_token
  dsimp only
  split
  · split
    · rename_i hp
      have hp' : p.val < data.val.length := by scalar_tac
      step as ⟨b, hb⟩
      step as ⟨s, hs⟩
      have hs' : s.val < 256 := by
        rw [hs, DynBlock.cast_usize_u8_val]
        scalar_tac
      step as ⟨x, hx⟩
      step as ⟨c, _⟩
      step as ⟨y, back, hy, hback⟩
      simp only [hback, alloc.vec.Vec.set_val_eq, List.length_set, WP.spec_ok]
      exact ⟨hlit, hdist⟩
    · simp only [WP.spec_ok]
      exact ⟨hlit, hdist⟩
  · step as ⟨l, _⟩
    step as ⟨d, _⟩
    split
    · split
      · rename_i hl hd
        have hl' : l.val < 29 := by scalar_tac
        have hd' : d.val < 30 := by scalar_tac
        step as ⟨i2, hi2⟩
        step as ⟨x, hx⟩
        step as ⟨c, _⟩
        step as ⟨y, back, hy, hback⟩
        step as ⟨x1, hx1⟩
        step as ⟨e, _⟩
        step as ⟨y1, back1, hy1, hback1⟩
        simp only [hback, hback1, alloc.vec.Vec.set_val_eq, List.length_set, WP.spec_ok]
        exact ⟨hlit, hdist⟩
      · simp only [WP.spec_ok]
        exact ⟨hlit, hdist⟩
    · simp only [WP.spec_ok]
      exact ⟨hlit, hdist⟩

theorem snapshot0_body (lit out : alloc.vec.Vec Usize) (base s : Usize) (hb : base.val ≤ 10000) :
    snapshot_loop0.body lit base out s ⦃ r =>
      match r with
      | .done _ => True
      | .cont (_, s') => s'.val = s.val + 1 ∧ s.val < 286 ⦄ := by
  unfold snapshot_loop0.body
  dsimp only
  split
  · rename_i hs
    have hs' : s.val < 286 := by scalar_tac
    split
    · rename_i hsl
      have hsl' : s.val < lit.val.length := by scalar_tac
      step as ⟨i1, hi1⟩
      split
      · rename_i hio
        have hio' : i1.val < out.val.length := by scalar_tac
        step as ⟨x, hx⟩
        step as ⟨y, back, hy, hback⟩
        step as ⟨s1, hs1⟩
        try simp only [WP.spec_ok]
        exact ⟨hs1, hs'⟩
      · simp
    · simp
  · simp

theorem snapshot0_loop (lit out : alloc.vec.Vec Usize) (base s : Usize) (hb : base.val ≤ 10000) :
    snapshot_loop0 lit out base s ⦃ _ => True ⦄ := by
  unfold snapshot_loop0
  apply loop.spec_decr_nat (fun (_, s') => 286 - s'.val) (fun _ => True)
  · rintro ⟨out', s'⟩ _
    refine WP.spec_mono (snapshot0_body lit out' base s' hb) ?_
    intro r hr
    cases r with
    | done state => trivial
    | cont state =>
        obtain ⟨out'', s''⟩ := state
        obtain ⟨h1, h2⟩ := hr
        exact ⟨trivial, by change 286 - s''.val < 286 - s'.val; omega⟩
  · trivial

theorem snapshot1_body (dist out : alloc.vec.Vec Usize) (base s : Usize) (hb : base.val ≤ 10000) :
    snapshot_loop1.body dist base out s ⦃ r =>
      match r with
      | .done _ => True
      | .cont (_, s') => s'.val = s.val + 1 ∧ s.val < 30 ⦄ := by
  unfold snapshot_loop1.body
  dsimp only
  split
  · rename_i hs
    have hs' : s.val < 30 := by scalar_tac
    split
    · rename_i hsl
      have hsl' : s.val < dist.val.length := by scalar_tac
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      split
      · rename_i hio
        have hio' : i2.val < out.val.length := by scalar_tac
        step as ⟨x, hx⟩
        step as ⟨i5, hi5⟩
        have hi5' : i5.val < out.val.length := by omega
        step as ⟨y, back, hy, hback⟩
        step as ⟨s1, hs1⟩
        try simp only [WP.spec_ok]
        exact ⟨hs1, hs'⟩
      · simp
    · simp
  · simp

theorem snapshot1_loop (dist out : alloc.vec.Vec Usize) (base s : Usize) (hb : base.val ≤ 10000) :
    snapshot_loop1 dist out base s ⦃ _ => True ⦄ := by
  unfold snapshot_loop1
  apply loop.spec_decr_nat (fun (_, s') => 30 - s'.val) (fun _ => True)
  · rintro ⟨out', s'⟩ _
    refine WP.spec_mono (snapshot1_body dist out' base s' hb) ?_
    intro r hr
    cases r with
    | done state => trivial
    | cont state =>
        obtain ⟨out'', s''⟩ := state
        obtain ⟨h1, h2⟩ := hr
        exact ⟨trivial, by change 30 - s''.val < 30 - s'.val; omega⟩
  · trivial

theorem snapshot_spec (snap lit dist : alloc.vec.Vec Usize) (j : Usize) (hj : j.val < 31) :
    snapshot snap j lit dist ⦃ _ => True ⦄ := by
  unfold snapshot
  step as ⟨base, hbase⟩
  have hb : base.val ≤ 10000 := by rw [hbase]; omega
  have h0 := snapshot0_loop lit snap base 0#usize hb
  step as ⟨out, _⟩
  exact snapshot1_loop dist out base 0#usize hb

/-- The inner loop over the thresholds a token position has passed. -/
theorem thresholds_body (start p t j : Usize) (lit dist snap cut : alloc.vec.Vec Usize)
    (hstart : start.val ≤ 1073741824) (hcut : cut.val.length = 31) :
    prefix_histograms_loop0_loop0.body start lit dist p t snap cut j ⦃ r =>
      match r with
      | .done (_, cut', _) => cut'.val.length = 31
      | .cont (_, cut', j') => cut'.val.length = 31 ∧ j'.val = j.val + 1 ∧ j.val < 31 ⦄ := by
  unfold prefix_histograms_loop0_loop0.body
  split
  · rename_i hj
    have hj' : j.val < 31 := by scalar_tac
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    split
    · have hsn := snapshot_spec snap lit dist j hj'
      step as ⟨snap1, _⟩
      step as ⟨x, back, hx, hback⟩
      simp only [hback, alloc.vec.Vec.set_val_eq, List.length_set, WP.spec_ok]
      exact ⟨hcut, hi, hj'⟩
    · simp only [WP.spec_ok]
      exact hcut
  · simp only [WP.spec_ok]
    exact hcut

theorem thresholds_loop (start p t j : Usize) (lit dist snap cut : alloc.vec.Vec Usize)
    (hstart : start.val ≤ 1073741824) (hcut : cut.val.length = 31) :
    prefix_histograms_loop0_loop0 start lit dist snap cut j p t ⦃ r => r.2.1.val.length = 31 ⦄ := by
  unfold prefix_histograms_loop0_loop0
  apply loop.spec_decr_nat (fun (_, _, j') => 31 - j'.val) (fun (_, cut', _) => cut'.val.length = 31)
  · rintro ⟨snap', cut', j'⟩ hc
    refine WP.spec_mono (thresholds_body start p t j' lit dist snap' cut' hstart hc) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨snap'', cut'', j''⟩ := state
        obtain ⟨h1, h2, h3⟩ := hr
        exact ⟨h1, by change 31 - j''.val < 31 - j'.val; omega⟩
  · exact hcut

theorem tokens_body (data : Aeneas.Std.Slice U8) (start p t j : Usize)
    (lengths distances : alloc.vec.Vec U16) (lit dist snap cut : alloc.vec.Vec Usize)
    (hstart : start.val ≤ 1073741824) (hlit : lit.val.length = 286) (hdist : dist.val.length = 30)
    (hcut : cut.val.length = 31) (ht : t.val ≤ lengths.val.length) :
    prefix_histograms_loop0.body data start lengths distances lit dist snap cut j p t ⦃ r =>
      match r with
      | .done (lit', dist', _, cut', _, _) => lit'.val.length = 286 ∧ dist'.val.length = 30 ∧ cut'.val.length = 31
      | .cont (lit', dist', _, cut', _, _, t') => lit'.val.length = 286 ∧ dist'.val.length = 30 ∧
          cut'.val.length = 31 ∧ t'.val = t.val + 1 ∧ t.val < lengths.val.length ⦄ := by
  unfold prefix_histograms_loop0.body
  dsimp only
  split
  · rename_i htl
    have htl' : t.val < lengths.val.length := by scalar_tac
    split
    · rename_i htd
      have htd' : t.val < distances.val.length := by scalar_tac
      have hth := thresholds_loop start p t j lit dist snap cut hstart hcut
      step as ⟨snap1, cut1, j1, hcut1⟩
      step as ⟨len16, hlen16⟩
      step as ⟨len, hlen⟩
      step as ⟨dd16, hdd16⟩
      step as ⟨dd, hdd⟩
      step as ⟨lit1, dist1, hlit1, hdist1⟩
      have hp1 : (if len <= 1073741824#usize then if p <= 1073741824#usize then p + len else ok p
          else ok p) ⦃ _ => True ⦄ := by
        split
        · split
          · rename_i h1 h2
            have : len.val ≤ 1073741824 := by scalar_tac
            have : p.val ≤ 1073741824 := by scalar_tac
            step*
          · simp
        · simp
      step as ⟨p1, _⟩
      step as ⟨t1, ht1⟩
      try simp only [WP.spec_ok]
      exact ⟨hlit1, hdist1, hcut1, ht1, htl'⟩
    · simp only [WP.spec_ok]
      exact ⟨hlit, hdist, hcut⟩
  · simp only [WP.spec_ok]
    exact ⟨hlit, hdist, hcut⟩

theorem tokens_loop (data : Aeneas.Std.Slice U8) (start p t j : Usize)
    (lengths distances : alloc.vec.Vec U16) (lit dist snap cut : alloc.vec.Vec Usize)
    (hstart : start.val ≤ 1073741824) (hlit : lit.val.length = 286) (hdist : dist.val.length = 30)
    (hcut : cut.val.length = 31) (ht : t.val ≤ lengths.val.length) :
    prefix_histograms_loop0 data start lengths distances lit dist snap cut j p t ⦃ r =>
      r.1.val.length = 286 ∧ r.2.1.val.length = 30 ∧ r.2.2.2.1.val.length = 31 ⦄ := by
  unfold prefix_histograms_loop0
  apply loop.spec_decr_nat (fun (_, _, _, _, _, _, t') => lengths.val.length - t'.val)
    (fun (lit', dist', _, cut', _, _, t') => lit'.val.length = 286 ∧ dist'.val.length = 30 ∧
      cut'.val.length = 31 ∧ t'.val ≤ lengths.val.length)
  · rintro ⟨lit', dist', snap', cut', j', p', t'⟩ ⟨h1, h2, h3, h4⟩
    refine WP.spec_mono (tokens_body data start p' t' j' lengths distances lit' dist' snap' cut'
      hstart h1 h2 h3 h4) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨lit'', dist'', snap'', cut'', j'', p'', t''⟩ := state
        obtain ⟨g1, g2, g3, g4, g5⟩ := hr
        exact ⟨⟨g1, g2, g3, by omega⟩, by change lengths.val.length - t''.val < lengths.val.length - t'.val; omega⟩
  · exact ⟨hlit, hdist, hcut, ht⟩

theorem trailing_body (t j : Usize) (lit dist snap cut : alloc.vec.Vec Usize) (hcut : cut.val.length = 31) :
    prefix_histograms_loop1.body lit dist t snap cut j ⦃ r =>
      match r with
      | .done (_, cut') => cut'.val.length = 31
      | .cont (_, cut', j') => cut'.val.length = 31 ∧ j'.val = j.val + 1 ∧ j.val < 31 ⦄ := by
  unfold prefix_histograms_loop1.body
  split
  · rename_i hj
    have hj' : j.val < 31 := by scalar_tac
    have hsn := snapshot_spec snap lit dist j hj'
    step as ⟨snap1, _⟩
    step as ⟨x, back, hx, hback⟩
    step as ⟨j1, hj1⟩
    simp only [hback, alloc.vec.Vec.set_val_eq, List.length_set, WP.spec_ok]
    exact ⟨hcut, hj1, hj'⟩
  · simp only [WP.spec_ok]
    exact hcut

theorem trailing_loop (t j : Usize) (lit dist snap cut : alloc.vec.Vec Usize) (hcut : cut.val.length = 31) :
    prefix_histograms_loop1 lit dist snap cut j t ⦃ r => r.2.val.length = 31 ⦄ := by
  unfold prefix_histograms_loop1
  apply loop.spec_decr_nat (fun (_, _, j') => 31 - j'.val) (fun (_, cut', _) => cut'.val.length = 31)
  · rintro ⟨snap', cut', j'⟩ hc
    refine WP.spec_mono (trailing_body t j' lit dist snap' cut' hc) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨snap'', cut'', j''⟩ := state
        obtain ⟨h1, h2, h3⟩ := hr
        exact ⟨h1, by change 31 - j''.val < 31 - j'.val; omega⟩
  · exact hcut

theorem prefix_histograms_spec (data : Aeneas.Std.Slice U8) (start : Usize)
    (lengths distances : alloc.vec.Vec U16) (hstart : start.val ≤ 1073741824) :
    prefix_histograms data start lengths distances ⦃ r => r.2.1.val.length = 31 ⦄ := by
  unfold prefix_histograms
  step as ⟨lit, hlit⟩
  step as ⟨dist, hdist⟩
  step as ⟨i, hi⟩
  step as ⟨snap, hsnap⟩
  step as ⟨cut, hcut⟩
  have hl := tokens_loop data start start 0#usize 0#usize lengths distances lit dist snap cut hstart
    (by rw [hlit, List.length_replicate]) (by rw [hdist, List.length_replicate])
    (by rw [hcut, List.length_replicate]) (by simp)
  step as ⟨lit1, dist1, snap1, cut1, j, t, hlit1, hdist1, hcut1⟩
  have ht := trailing_loop t j lit1 dist1 snap1 cut1 hcut1
  step as ⟨snap2, cut2, hcut2⟩
  have h256 : (256 : ℕ) < lit1.val.length := by omega
  step as ⟨x, hx⟩
  step as ⟨c, _⟩
  step as ⟨y, back, hy, hback⟩
  try simp only [WP.spec_ok]
  exact hcut2

theorem cut0_body (snap lfreq la lb : alloc.vec.Vec Usize) (base s : Usize) (hb : base.val ≤ 10000)
    (hla : la.val.length = s.val) (hlb : lb.val.length = s.val) :
    cut_cost_loop0.body snap lfreq base la lb s ⦃ r =>
      match r with
      | .done _ => True
      | .cont (la', lb', s') => s'.val = s.val + 1 ∧ s.val < 286 ∧
          la'.val.length = s'.val ∧ lb'.val.length = s'.val ⦄ := by
  unfold cut_cost_loop0.body
  dsimp only
  split
  · rename_i hs
    have hs' : s.val < 286 := by scalar_tac
    step as ⟨i, hi⟩
    have hx : (if i < alloc.vec.Vec.len snap then alloc.vec.Vec.index_usize snap i else ok 0#usize)
        ⦃ _ => True ⦄ := by
      split
      · rename_i hlt
        have : i.val < snap.val.length := by scalar_tac
        step*
      · simp
    step as ⟨x, _⟩
    have hy : (if s < alloc.vec.Vec.len lfreq then alloc.vec.Vec.index_usize lfreq s else ok 0#usize)
        ⦃ _ => True ⦄ := by
      split
      · rename_i hlt
        have : s.val < lfreq.val.length := by scalar_tac
        step*
      · simp
    step as ⟨y, _⟩
    have hla' : la.val.length < Usize.max := by scalar_tac
    have hlb' : lb.val.length < Usize.max := by scalar_tac
    split
    · step as ⟨x1, _⟩
      step as ⟨la1, hla1⟩
      split
      · step as ⟨i3, hi3⟩
        step as ⟨lb1, hlb1⟩
        step as ⟨s1, hs1⟩
        try simp only [WP.spec_ok]
        refine ⟨hs1, hs', ?_, ?_⟩ <;> simp [hla1, hlb1, hla, hlb, hs1]
      · step as ⟨lb1, hlb1⟩
        step as ⟨s1, hs1⟩
        try simp only [WP.spec_ok]
        refine ⟨hs1, hs', ?_, ?_⟩ <;> simp [hla1, hlb1, hla, hlb, hs1]
    · step as ⟨la1, hla1⟩
      split
      · step as ⟨i3, hi3⟩
        step as ⟨lb1, hlb1⟩
        step as ⟨s1, hs1⟩
        try simp only [WP.spec_ok]
        refine ⟨hs1, hs', ?_, ?_⟩ <;> simp [hla1, hlb1, hla, hlb, hs1]
      · step as ⟨lb1, hlb1⟩
        step as ⟨s1, hs1⟩
        try simp only [WP.spec_ok]
        refine ⟨hs1, hs', ?_, ?_⟩ <;> simp [hla1, hlb1, hla, hlb, hs1]
  · simp

theorem cut0_loop (snap lfreq la lb : alloc.vec.Vec Usize) (base s : Usize) (hb : base.val ≤ 10000)
    (hla : la.val.length = s.val) (hlb : lb.val.length = s.val) :
    cut_cost_loop0 snap lfreq base la lb s ⦃ _ => True ⦄ := by
  unfold cut_cost_loop0
  apply loop.spec_decr_nat (fun (_, _, s') => 286 - s'.val)
    (fun (la', lb', s') => la'.val.length = s'.val ∧ lb'.val.length = s'.val)
  · rintro ⟨la', lb', s'⟩ ⟨g1, g2⟩
    refine WP.spec_mono (cut0_body snap lfreq la' lb' base s' hb g1 g2) ?_
    intro r hr
    cases r with
    | done state => trivial
    | cont state =>
        obtain ⟨la'', lb'', s''⟩ := state
        obtain ⟨h1, h2, h3, h4⟩ := hr
        exact ⟨⟨h3, h4⟩, by change 286 - s''.val < 286 - s'.val; omega⟩
  · exact ⟨hla, hlb⟩

theorem cut1_body (snap dfreq da db : alloc.vec.Vec Usize) (base s : Usize) (hb : base.val ≤ 10000)
    (hda : da.val.length = s.val) (hdb : db.val.length = s.val) :
    cut_cost_loop1.body snap dfreq base s da db ⦃ r =>
      match r with
      | .done _ => True
      | .cont (s', da', db') => s'.val = s.val + 1 ∧ s.val < 30 ∧
          da'.val.length = s'.val ∧ db'.val.length = s'.val ⦄ := by
  unfold cut_cost_loop1.body
  dsimp only
  split
  · rename_i hs
    have hs' : s.val < 30 := by scalar_tac
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    have hx : (if i1 < alloc.vec.Vec.len snap then do
          let i3 ← i + s
          alloc.vec.Vec.index_usize snap i3
        else ok 0#usize) ⦃ _ => True ⦄ := by
      split
      · rename_i hlt
        have : i1.val < snap.val.length := by scalar_tac
        step as ⟨i3, hi3⟩
        have : i3.val < snap.val.length := by omega
        step*
      · simp
    step as ⟨x, _⟩
    have hy : (if s < alloc.vec.Vec.len dfreq then alloc.vec.Vec.index_usize dfreq s else ok 0#usize)
        ⦃ _ => True ⦄ := by
      split
      · rename_i hlt
        have : s.val < dfreq.val.length := by scalar_tac
        step*
      · simp
    step as ⟨y, _⟩
    have hda' : da.val.length < Usize.max := by scalar_tac
    have hdb' : db.val.length < Usize.max := by scalar_tac
    step as ⟨da1, hda1⟩
    split
    · step as ⟨i4, hi4⟩
      step as ⟨db1, hdb1⟩
      step as ⟨s1, hs1⟩
      try simp only [WP.spec_ok]
      refine ⟨hs1, hs', ?_, ?_⟩ <;> simp [hda1, hdb1, hda, hdb, hs1]
    · step as ⟨db1, hdb1⟩
      step as ⟨s1, hs1⟩
      try simp only [WP.spec_ok]
      refine ⟨hs1, hs', ?_, ?_⟩ <;> simp [hda1, hdb1, hda, hdb, hs1]
  · simp

theorem cut1_loop (snap dfreq da db : alloc.vec.Vec Usize) (base s : Usize) (hb : base.val ≤ 10000)
    (hda : da.val.length = s.val) (hdb : db.val.length = s.val) :
    cut_cost_loop1 snap dfreq base s da db ⦃ _ => True ⦄ := by
  unfold cut_cost_loop1
  apply loop.spec_decr_nat (fun (s', _, _) => 30 - s'.val)
    (fun (s', da', db') => da'.val.length = s'.val ∧ db'.val.length = s'.val)
  · rintro ⟨s', da', db'⟩ ⟨g1, g2⟩
    refine WP.spec_mono (cut1_body snap dfreq da' db' base s' hb g1 g2) ?_
    intro r hr
    cases r with
    | done state => trivial
    | cont state =>
        obtain ⟨s'', da'', db''⟩ := state
        obtain ⟨h1, h2, h3, h4⟩ := hr
        exact ⟨⟨h3, h4⟩, by change 30 - s''.val < 30 - s'.val; omega⟩
  · exact ⟨hda, hdb⟩

theorem cut_cost_spec (snap lfreq dfreq : alloc.vec.Vec Usize) (j : Usize) (hj : j.val < 31) :
    cut_cost snap j lfreq dfreq ⦃ _ => True ⦄ := by
  unfold cut_cost
  step as ⟨base, hbase⟩
  have hb : base.val ≤ 10000 := by rw [hbase]; omega
  have h0 := cut0_loop snap lfreq (alloc.vec.Vec.with_capacity Usize 286#usize)
    (alloc.vec.Vec.with_capacity Usize 286#usize) base 0#usize hb (by simp [alloc.vec.Vec.with_capacity])
    (by simp [alloc.vec.Vec.with_capacity])
  step as ⟨la1, lb1, _⟩
  have h1 := cut1_loop snap dfreq (alloc.vec.Vec.with_capacity Usize 30#usize)
    (alloc.vec.Vec.with_capacity Usize 30#usize) base 0#usize hb (by simp [alloc.vec.Vec.with_capacity])
    (by simp [alloc.vec.Vec.with_capacity])
  step as ⟨da1, db1, _⟩
  have hc1 := Merge.hist_cost_spec la1 da1
  step as ⟨i, hi⟩
  have hc2 := Merge.hist_cost_spec lb1 db1
  step as ⟨i1, hi1⟩
  step*

theorem coarse_body (snap lfreq dfreq : alloc.vec.Vec Usize) (best bestj j : Usize) :
    split_point_loop0.body snap lfreq dfreq best bestj j ⦃ r =>
      match r with
      | .done _ => True
      | .cont (_, _, j') => j'.val = j.val + 4 ∧ j.val < 31 ⦄ := by
  unfold split_point_loop0.body
  split
  · rename_i hj
    have hj' : j.val < 31 := by scalar_tac
    have hc := cut_cost_spec snap lfreq dfreq j hj'
    step as ⟨c, _⟩
    have hsel : (if c < best then ok (c, j) else ok (best, bestj)) ⦃ _ => True ⦄ := by
      split <;> simp
    step as ⟨best1, bestj1, _⟩
    step as ⟨j1, hj1⟩
    try simp only [WP.spec_ok]
    exact ⟨hj1, hj'⟩
  · simp

theorem coarse_loop (snap lfreq dfreq : alloc.vec.Vec Usize) (best bestj j : Usize) :
    split_point_loop0 snap lfreq dfreq best bestj j ⦃ _ => True ⦄ := by
  unfold split_point_loop0
  apply loop.spec_decr_nat (fun (_, _, j') => 31 - j'.val) (fun _ => True)
  · rintro ⟨best', bestj', j'⟩ _
    refine WP.spec_mono (coarse_body snap lfreq dfreq best' bestj' j') ?_
    intro r hr
    cases r with
    | done state => trivial
    | cont state =>
        obtain ⟨best'', bestj'', j''⟩ := state
        obtain ⟨h1, h2⟩ := hr
        exact ⟨trivial, by change 31 - j''.val < 31 - j'.val; omega⟩
  · trivial

theorem fine_body (snap lfreq dfreq : alloc.vec.Vec Usize) (center best bestj j : Usize)
    (hc : center.val ≤ 31) :
    split_point_loop1.body snap lfreq dfreq center best bestj j ⦃ r =>
      match r with
      | .done _ => True
      | .cont (_, _, j') => j'.val = j.val + 1 ∧ j.val ≤ center.val + 1 ⦄ := by
  unfold split_point_loop1.body
  step as ⟨i, hi⟩
  split
  · rename_i hji
    have hji' : j.val ≤ center.val + 1 := by scalar_tac
    split
    · rename_i hj
      have hj' : j.val < 31 := by scalar_tac
      have hsel : (if j != center then do
            let c ← cut_cost snap j lfreq dfreq
            if c < best then ok (c, j) else ok (best, bestj)
          else ok (best, bestj)) ⦃ _ => True ⦄ := by
        split
        · have hcc := cut_cost_spec snap lfreq dfreq j hj'
          step as ⟨c, _⟩
          split <;> simp
        · simp
      step as ⟨best1, bestj1, _⟩
      step as ⟨j1, hj1⟩
      try simp only [WP.spec_ok]
      exact ⟨hj1, hji'⟩
    · simp
  · simp

theorem fine_loop (snap lfreq dfreq : alloc.vec.Vec Usize) (best bestj j center : Usize)
    (hc : center.val ≤ 31) :
    split_point_loop1 snap lfreq dfreq best bestj j center ⦃ _ => True ⦄ := by
  unfold split_point_loop1
  apply loop.spec_decr_nat (fun (_, _, j') => center.val + 2 - j'.val) (fun _ => True)
  · rintro ⟨best', bestj', j'⟩ _
    refine WP.spec_mono (fine_body snap lfreq dfreq center best' bestj' j' hc) ?_
    intro r hr
    cases r with
    | done state => trivial
    | cont state =>
        obtain ⟨best'', bestj'', j''⟩ := state
        obtain ⟨h1, h2⟩ := hr
        exact ⟨trivial, by change center.val + 2 - j''.val < center.val + 2 - j'.val; omega⟩
  · trivial

theorem split_point_spec (data : Aeneas.Std.Slice U8) (start : Usize)
    (lengths distances : alloc.vec.Vec U16) (hstart : start.val ≤ 1073741824) :
    split_point data start lengths distances ⦃ _ => True ⦄ := by
  unfold split_point
  have hph := prefix_histograms_spec data start lengths distances hstart
  step as ⟨snap, cut, lfreq, dfreq, hcut⟩
  have hw := Merge.hist_cost_spec lfreq dfreq
  step as ⟨whole, _⟩
  have hb : (if whole > 64#usize then whole - 64#usize else ok 0#usize) ⦃ _ => True ⦄ := by
    split
    · rename_i h
      have : 64 ≤ whole.val := by scalar_tac
      step*
    · simp
  step as ⟨best, _⟩
  have hcl := coarse_loop snap lfreq dfreq best 31#usize 3#usize
  step as ⟨best1, bestj, _⟩
  split
  · rename_i hbj
    have hbj' : bestj.val < 31 := by scalar_tac
    have hjs : (if bestj >= 1#usize then bestj - 1#usize else ok 0#usize) ⦃ _ => True ⦄ := by
      split
      · rename_i h
        have : 1 ≤ bestj.val := by scalar_tac
        step*
      · simp
    step as ⟨j, _⟩
    have hfl := fine_loop snap lfreq dfreq best1 bestj j bestj (by omega)
    step as ⟨bestj1, _⟩
    split
    · rename_i hb1
      have : bestj1.val < cut.val.length := by rw [hcut]; scalar_tac
      step*
    · simp
  · simp

@[step]
theorem cut_candidate_spec (start : Usize) (level : U8) : cut_candidate start level ⦃ _ => True ⦄ := by
  unfold cut_candidate
  split <;> simp

@[step]
theorem split_choice_spec (data : Aeneas.Std.Slice U8) (start span : Usize) (plan : Plan) (level : U8)
    (hstart : start.val ≤ 1073741824) :
    split_choice data start span plan level ⦃ _ => True ⦄ := by
  unfold split_choice
  dsimp only
  split
  · step as ⟨b, _⟩
    split
    · split
      · step as ⟨i1, hi1⟩
        have : i1.val ≤ span.val := by rw [hi1]; exact Nat.div_le_self _ _
        step as ⟨i2, hi2⟩
        split
        · exact split_point_spec data start plan.lengths plan.distances hstart
        · simp
      · simp
    · simp
  · simp

/-! ### The exact cut of a plan -/

theorem first_body (plan : Plan) (k t mid : Usize) (v v1 : alloc.vec.Vec U16)
    (data : List U8) (stop start q : ℕ)
    (hr : Runs data stop start q plan.lengths.val plan.distances.val)
    (hk : k.val ≤ plan.lengths.val.length) (ht : t.val ≤ k.val)
    (hv : v.val = plan.lengths.val.take t.val) (hv1 : v1.val = plan.distances.val.take t.val)
    (hmid : mid.val = pos plan.lengths.val start t.val) (hq : q ≤ Usize.max) :
    split_plan_loop0.body plan k v v1 mid t ⦃ r =>
      match r with
      | .done (pl, v', v1', mid', t') => pl = plan ∧ t'.val = k.val ∧ v'.val = plan.lengths.val.take k.val ∧
          v1'.val = plan.distances.val.take k.val ∧ mid'.val = pos plan.lengths.val start k.val
      | .cont (v', v1', mid', t') => t'.val = t.val + 1 ∧ t'.val ≤ k.val ∧
          v'.val = plan.lengths.val.take t'.val ∧ v1'.val = plan.distances.val.take t'.val ∧
          mid'.val = pos plan.lengths.val start t'.val ⦄ := by
  have hll := runs_lengths hr
  unfold split_plan_loop0.body
  dsimp only
  split
  · rename_i htk
    have htk' : t.val < k.val := by scalar_tac
    split
    · rename_i htl
      have htl' : t.val < plan.lengths.val.length := by scalar_tac
      split
      · rename_i htd
        have htd' : t.val < plan.distances.val.length := by scalar_tac
        step as ⟨len, hlen⟩
        have hvlen : v.val.length < Usize.max := by
          rw [hv, List.length_take]; have := plan.lengths.property; omega
        step as ⟨v2, hv2⟩
        step as ⟨d, hd⟩
        have hv1len : v1.val.length < Usize.max := by
          rw [hv1, List.length_take]; have := plan.distances.property; omega
        step as ⟨v3, hv3⟩
        have hposle := runs_pos_le hr (t.val + 1) (by omega)
        have hpos1 := pos_succ plan.lengths.val start t.val htl'
        have hlget : len = plan.lengths.val[t.val]! := by rw [hlen, getElem!_pos plan.lengths.val t.val htl']
        have hmid1 : mid.val + len.val = pos plan.lengths.val start (t.val + 1) := by
          rw [hpos1, hmid, hlget]
        have hmidle : mid.val + len.val ≤ Usize.max := by omega
        step as ⟨wide, hwide⟩
        have hwideval : wide.val = len.val := by
          rw [hwide]
          exact widen_val len
        step as ⟨mid1, hmid1'⟩
        step as ⟨t1, ht1⟩
        try simp only [WP.spec_ok]
        refine ⟨ht1, by omega, ?_, ?_, ?_⟩
        · rw [hv2, hv, ht1, List.take_succ_eq_append_getElem htl', hlen]
        · rw [hv3, hv1, ht1, List.take_succ_eq_append_getElem htd', hd]
        · rw [hmid1', ht1, hwideval, ← hmid1]
      · exfalso
        have : t.val < plan.distances.val.length := by omega
        scalar_tac
    · exfalso
      have : t.val < plan.lengths.val.length := by omega
      scalar_tac
  · rename_i htk
    have hte : t.val = k.val := by scalar_tac
    try simp only [WP.spec_ok]
    rw [hte] at hv hv1 hmid
    exact ⟨by first | trivial | rfl, hte, hv, hv1, hmid⟩

theorem first_loop (plan : Plan) (k t mid : Usize) (v v1 : alloc.vec.Vec U16)
    (data : List U8) (stop start q : ℕ)
    (hr : Runs data stop start q plan.lengths.val plan.distances.val)
    (hk : k.val ≤ plan.lengths.val.length) (ht : t.val ≤ k.val)
    (hv : v.val = plan.lengths.val.take t.val) (hv1 : v1.val = plan.distances.val.take t.val)
    (hmid : mid.val = pos plan.lengths.val start t.val) (hq : q ≤ Usize.max) :
    split_plan_loop0 plan k v v1 mid t ⦃ r =>
      r.1 = plan ∧ r.2.2.2.2.val = k.val ∧ r.2.1.val = plan.lengths.val.take k.val ∧
      r.2.2.1.val = plan.distances.val.take k.val ∧ r.2.2.2.1.val = pos plan.lengths.val start k.val ⦄ := by
  unfold split_plan_loop0
  apply loop.spec_decr_nat (fun (_, _, _, t') => k.val - t'.val)
    (fun (v', v1', mid', t') => t'.val ≤ k.val ∧ v'.val = plan.lengths.val.take t'.val ∧
      v1'.val = plan.distances.val.take t'.val ∧ mid'.val = pos plan.lengths.val start t'.val)
  · rintro ⟨v', v1', mid', t'⟩ ⟨h1, h2, h3, h4⟩
    refine WP.spec_mono (first_body plan k t' mid' v' v1' data stop start q hr hk h1 h2 h3 h4 hq) ?_
    intro r hr'
    cases r with
    | done state =>
        obtain ⟨pl, v'', v1'', mid'', t''⟩ := state
        exact hr'
    | cont state =>
        obtain ⟨v'', v1'', mid'', t''⟩ := state
        obtain ⟨g1, g2, g3, g4, g5⟩ := hr'
        exact ⟨⟨g2, g3, g4, g5⟩, by change k.val - t''.val < k.val - t'.val; omega⟩
  · exact ⟨ht, hv, hv1, hmid⟩

theorem rest_body (plan : Plan) (k t : Usize) (v v1 : alloc.vec.Vec U16)
    (hl : plan.lengths.val.length = plan.distances.val.length)
    (hk : k.val ≤ t.val) (ht : t.val ≤ plan.lengths.val.length)
    (hv : v.val ++ plan.lengths.val.drop t.val = plan.lengths.val.drop k.val)
    (hv1 : v1.val ++ plan.distances.val.drop t.val = plan.distances.val.drop k.val) :
    split_plan_loop1.body plan v v1 t ⦃ r =>
      match r with
      | .done (v', v1') => v'.val = plan.lengths.val.drop k.val ∧ v1'.val = plan.distances.val.drop k.val
      | .cont (v', v1', t') => t'.val = t.val + 1 ∧ t'.val ≤ plan.lengths.val.length ∧
          v'.val ++ plan.lengths.val.drop t'.val = plan.lengths.val.drop k.val ∧
          v1'.val ++ plan.distances.val.drop t'.val = plan.distances.val.drop k.val ⦄ := by
  unfold split_plan_loop1.body
  dsimp only
  split
  · rename_i htl
    have htl' : t.val < plan.lengths.val.length := by scalar_tac
    split
    · rename_i htd
      have htd' : t.val < plan.distances.val.length := by scalar_tac
      step as ⟨len, hlen⟩
      have hvlen : v.val.length < Usize.max := by
        have := congrArg List.length hv
        simp only [List.length_append, List.length_drop] at this
        have := plan.lengths.property; omega
      step as ⟨v2, hv2⟩
      step as ⟨d, hd⟩
      have hv1len : v1.val.length < Usize.max := by
        have := congrArg List.length hv1
        simp only [List.length_append, List.length_drop] at this
        have := plan.distances.property; omega
      step as ⟨v3, hv3⟩
      step as ⟨t1, ht1⟩
      try simp only [WP.spec_ok]
      refine ⟨ht1, by omega, ?_, ?_⟩
      · rw [hv2, ht1, ← hv, List.drop_eq_getElem_cons htl', hlen]
        simp
      · rw [hv3, ht1, ← hv1, List.drop_eq_getElem_cons htd', hd]
        simp
    · exfalso
      have : t.val < plan.distances.val.length := by omega
      scalar_tac
  · rename_i htl
    have hte : t.val = plan.lengths.val.length := by scalar_tac
    try simp only [WP.spec_ok]
    rw [hte, List.drop_length, List.append_nil] at hv
    rw [hte, hl, List.drop_length, List.append_nil] at hv1
    exact ⟨hv, hv1⟩

theorem rest_loop (plan : Plan) (k t : Usize) (v v1 : alloc.vec.Vec U16)
    (hl : plan.lengths.val.length = plan.distances.val.length)
    (hk : k.val ≤ t.val) (ht : t.val ≤ plan.lengths.val.length)
    (hv : v.val ++ plan.lengths.val.drop t.val = plan.lengths.val.drop k.val)
    (hv1 : v1.val ++ plan.distances.val.drop t.val = plan.distances.val.drop k.val) :
    split_plan_loop1 plan v v1 t ⦃ r =>
      r.1.val = plan.lengths.val.drop k.val ∧ r.2.val = plan.distances.val.drop k.val ⦄ := by
  unfold split_plan_loop1
  apply loop.spec_decr_nat (fun (_, _, t') => plan.lengths.val.length - t'.val)
    (fun (v', v1', t') => k.val ≤ t'.val ∧ t'.val ≤ plan.lengths.val.length ∧
      v'.val ++ plan.lengths.val.drop t'.val = plan.lengths.val.drop k.val ∧
      v1'.val ++ plan.distances.val.drop t'.val = plan.distances.val.drop k.val)
  · rintro ⟨v', v1', t'⟩ ⟨h1, h2, h3, h4⟩
    refine WP.spec_mono (rest_body plan k t' v' v1' hl h1 h2 h3 h4) ?_
    intro r hr'
    cases r with
    | done state => exact hr'
    | cont state =>
        obtain ⟨v'', v1'', t''⟩ := state
        obtain ⟨g1, g2, g3, g4⟩ := hr'
        exact ⟨⟨by omega, g2, g3, g4⟩, by change plan.lengths.val.length - t''.val < plan.lengths.val.length - t'.val; omega⟩
  · exact ⟨hk, ht, hv, hv1⟩

/-- The cut plan: the two parts are runs of tokens meeting at `mid`. -/
theorem split_plan_spec (plan : Plan) (k start : Usize) (data : List U8) (stop q : ℕ)
    (hr : Runs data stop start.val q plan.lengths.val plan.distances.val)
    (hk : k.val ≤ plan.lengths.val.length) (hq : q ≤ Usize.max) :
    split_plan plan k start ⦃ r =>
      Runs data stop start.val r.2.2.val r.1.lengths.val r.1.distances.val ∧
      Runs data stop r.2.2.val q r.2.1.lengths.val r.2.1.distances.val ∧
      start.val ≤ r.2.2.val ∧ r.2.2.val ≤ q ⦄ := by
  have hll := runs_lengths hr
  unfold split_plan
  have h0 := first_loop plan k 0#usize start (alloc.vec.Vec.new U16) (alloc.vec.Vec.new U16)
    data stop start.val q hr hk (by simp) (by simp [alloc.vec.Vec.new]) (by simp [alloc.vec.Vec.new])
    (by simp) hq
  step as ⟨pl, v, v1, mid, t, hpl, hte, hv, hv1, hmid⟩
  try dsimp only at hpl hte hv hv1 hmid
  subst pl
  have h1 := rest_loop plan k t (alloc.vec.Vec.new U16) (alloc.vec.Vec.new U16) hll.1 (by omega)
    (by omega) (by simp [alloc.vec.Vec.new, hte]) (by simp [alloc.vec.Vec.new, hte])
  step as ⟨v2, v3, hv2, hv3⟩
  try simp only [WP.spec_ok]
  obtain ⟨hfirst, hrest⟩ := runs_split hr k.val hk
  rw [← hmid] at hfirst hrest
  refine ⟨?_, ?_, runs_bound hfirst, runs_bound hrest⟩
  · simpa only [hv, hv1] using hfirst
  · simpa only [hv2, hv3] using hrest

end Gzip.Proofs.Split
