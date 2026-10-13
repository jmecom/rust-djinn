import Gzip.Proofs.Plans
import Gzip.Proofs.FastGreedy
import Gzip.Proofs.Costs
import Gzip.Proofs.Chains

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Plans Gzip.Proofs.Matches Gzip.Proofs.Chains

namespace Gzip.Proofs.Greedy

@[step]
theorem choose_correct (data : Aeneas.Std.Slice U8) (p stop : Usize) (level : U8)
    (depth : Usize) (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32) (four : Bool)
    (ht : Tables head.val chain.val p.val)
    (hp : p.val < stop.val) (hd : stop.val ≤ data.val.length) :
    choose_match data p stop level depth head chain four ⦃ r =>
      1 ≤ r.1.1.val ∧ r.1.1.val ≤ 258 ∧
      ValidMatch data.val p.val stop.val r.1.1.val r.1.2.val ∧
      Tables r.2.1.val r.2.2.val (p.val + 1) ⦄ := by
  have hhead := ht.1
  have hchain := ht.2
  have hchain' : (alloc.vec.Vec.deref chain).val.length = 65536 := by
    simpa only [alloc.vec.Vec.deref, Slice.from_val] using hchain
  have hpd : p.val < data.val.length := by omega
  unfold choose_match
  step as ⟨h, _⟩
  split
  · step as ⟨pair, head1, hl0, hl1, hmatch, hlen⟩
    rcases pair with ⟨len, dist⟩
    dsimp only at *
    try simp only [WP.spec_ok]
    refine ⟨by omega, hl1, hmatch, ?_⟩
    exact ⟨by rw [hlen]; exact hhead, hchain⟩
  · step as ⟨len, dist, hl0, hl1, hmatch⟩
    step as ⟨head1, chain1, ht1⟩
    try simp only [WP.spec_ok]
    exact ⟨by omega, hl1, hmatch, ht1⟩

@[step]
theorem lazy_depth_spec (level : U8) (depth : Usize) :
    lazy_depth level depth ⦃ _ => True ⦄ := by
  unfold lazy_depth
  repeat' split
  all_goals step*

@[step]
theorem lazy_limit_spec (level : U8) :
    lazy_limit level ⦃ _ => True ⦄ := by
  unfold lazy_limit
  repeat' split
  all_goals step*

/-- `distance_code` of any distance: in range of the tables it reads. -/
theorem distance_code_free (dist : Usize) : distance_code dist ⦃ _ => True ⦄ := by
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
theorem extra_bits_spec (dist : Usize) : extra_bits dist ⦃ r => r.val ≤ 13 ⦄ := by
  unfold extra_bits
  step with distance_code_free dist as ⟨d, _⟩
  split
  · rename_i hlt
    have hd : d.val < 30 := by scalar_tac
    step as ⟨e, he⟩
    have hb := Gzip.Proofs.Costs.distance_extra_bound d.val hd
    have hdd : d.val < DIST_EXTRA.val.length := by simp [DIST_EXTRA, Array.make]; omega
    rw [getElem!_pos DIST_EXTRA.val d.val hdd, ← he] at hb
    have hc : (UScalar.cast UScalarTy.Usize e).val = e.val := by scalar_tac
    rw [hc]
    exact hb
  · simp

@[step]
theorem defers_spec (level : U8) (len dist next ndist : Usize)
    (hl : len.val ≤ 258) (hn : next.val ≤ 258) :
    defers level len dist next ndist ⦃ _ => True ⦄ := by
  unfold defers
  split
  · step as ⟨e1, he1⟩
    step as ⟨e2, he2⟩
    split
    · step*
    · simp
  · step*

@[step]
theorem chain_depth_spec (level : U8) : chain_depth level ⦃ _ => True ⦄ := by
  unfold chain_depth
  repeat' split
  all_goals step*

/-- The match carried from a position's lookahead to the next position: none (`cl` is 0), or a
valid match at `p` of a chain's shape. -/
def Carried (data : List U8) (stop p : ℕ) (cl cd : Usize) : Prop :=
  cl.val = 0 ∨ ((2 ≤ cl.val ∧ cl.val ≤ 258) ∧ ValidMatch data p stop cl.val cd.val)

theorem carried_none (data : List U8) (stop p : ℕ) : Carried data stop p 0#usize 0#usize :=
  Or.inl (by simp)

@[step]
theorem carried_or_found_correct (data : Aeneas.Std.Slice U8) (p stop h : Usize)
    (head : Aeneas.Std.Slice U32) (chain : Aeneas.Std.Slice U32) (depth cl cd : Usize)
    (hp : p.val ≤ stop.val) (hend : stop.val ≤ data.val.length)
    (hchain : chain.val.length = 65536) (hc : Carried data.val stop.val p.val cl cd) :
    carried_or_found data p stop h head chain depth cl cd ⦃ r =>
      (2 ≤ r.1.val ∧ r.1.val ≤ 258) ∧ ValidMatch data.val p.val stop.val r.1.val r.2.val ⦄ := by
  unfold carried_or_found
  by_cases h0 : cl = 0#usize
  · subst h0
    step*
  · have hne : (cl != 0#usize) = true := by
      simp only [bne_iff_ne, ne_eq]
      exact h0
    rw [hne]
    simp only [ite_true]
    try simp only [WP.spec_ok]
    rcases hc with hz | hm
    · exfalso
      apply h0
      apply (UScalar.eq_equiv _ _).mpr
      simpa using hz
    · exact hm

@[step]
theorem lazy_correct (data : Aeneas.Std.Slice U8) (p stop : Usize) (level : U8)
    (depth : Usize) (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32) (four : Bool) (cl cd : Usize)
    (ht : Tables head.val chain.val p.val)
    (hp : p.val < stop.val) (hd : stop.val ≤ data.val.length)
    (hc : Carried data.val stop.val p.val cl cd) :
    lazy_match data p stop level depth head chain four cl cd ⦃ r =>
      1 ≤ r.1.1.val ∧ r.1.1.val ≤ 258 ∧
      ValidMatch data.val p.val stop.val r.1.1.val r.1.2.1.val ∧
      Tables r.2.1.val r.2.2.val (p.val + 1) ∧
      Carried data.val stop.val (p.val + 1) r.1.2.2.1 r.1.2.2.2 ∧
      (r.1.2.2.1.val = 0 ∨ r.1.1.val = 1) ⦄ := by
  have hhead := ht.1
  have hchain := ht.2
  have hchain' : (alloc.vec.Vec.deref chain).val.length = 65536 := by
    simpa only [alloc.vec.Vec.deref, Slice.from_val] using hchain
  have hpd : p.val < data.val.length := by omega
  have hp' : p.val ≤ stop.val := by omega
  unfold lazy_match
  step as ⟨h, _⟩
  step as ⟨len, dist, hl0, hl1, hmatch⟩
  step as ⟨head1, chain1, ht1⟩
  have hhead1 : 0 < head1.deref.val.length := by
    simpa only [alloc.vec.Vec.deref, Slice.from_val] using ht1.1
  have hchain1 : chain1.deref.val.length = 65536 := by
    simpa only [alloc.vec.Vec.deref, Slice.from_val] using ht1.2
  step as ⟨lim, _⟩
  split
  · split
    · step as ⟨i1, hi1⟩
      split
      · step as ⟨h1, _⟩
        step as ⟨ld, _⟩
        step as ⟨next, ndist, hn0, hn1, hnm⟩
        step as ⟨b, _⟩
        split
        · try simp only [WP.spec_ok]
          refine ⟨by scalar_tac, by scalar_tac, Or.inl (by scalar_tac), ht1, Or.inr ⟨⟨hn0, hn1⟩, ?_⟩, Or.inr (by scalar_tac)⟩
          rw [hi1] at hnm
          exact hnm
        · try simp only [WP.spec_ok]
          exact ⟨by scalar_tac, hl1, hmatch, ht1, carried_none _ _ _, Or.inl (by scalar_tac)⟩
      · try simp only [WP.spec_ok]
        exact ⟨by scalar_tac, hl1, hmatch, ht1, carried_none _ _ _, Or.inl (by scalar_tac)⟩
    · try simp only [WP.spec_ok]
      exact ⟨by scalar_tac, hl1, hmatch, ht1, carried_none _ _ _, Or.inl (by scalar_tac)⟩
  · try simp only [WP.spec_ok]
    exact ⟨by scalar_tac, hl1, hmatch, ht1, carried_none _ _ _, Or.inl (by scalar_tac)⟩

@[step]
theorem step_correct (data : Aeneas.Std.Slice U8) (p stop : Usize) (level : U8)
    (depth : Usize) (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32) (four : Bool) (cl cd : Usize)
    (ht : Tables head.val chain.val p.val)
    (hp : p.val < stop.val) (hd : stop.val ≤ data.val.length)
    (hc : Carried data.val stop.val p.val cl cd) :
    step_match data p stop level depth head chain four cl cd ⦃ r =>
      1 ≤ r.1.1.val ∧ r.1.1.val ≤ 258 ∧
      ValidMatch data.val p.val stop.val r.1.1.val r.1.2.1.val ∧
      Tables r.2.1.val r.2.2.val (p.val + 1) ∧
      Carried data.val stop.val (p.val + 1) r.1.2.2.1 r.1.2.2.2 ∧
      (r.1.2.2.1.val = 0 ∨ r.1.1.val = 1) ⦄ := by
  unfold step_match
  split
  · exact lazy_correct data p stop level depth head chain four cl cd ht hp hd hc
  · step as ⟨pair, head1, chain1, hl0, hl1, hmatch, ht1⟩
    rcases pair with ⟨len, dist⟩
    dsimp only at *
    try simp only [WP.spec_ok]
    exact ⟨hl0, hl1, hmatch, ht1, carried_none _ _ _, Or.inl (by scalar_tac)⟩

@[step]
theorem insertion_start_spec (len dist : Usize) (level : U8) (hlen : 1 ≤ len.val) :
    insertion_start len dist level ⦃ k => k.val ≤ len.val ⦄ := by
  unfold insertion_start
  step*
  all_goals scalar_tac

theorem interior_body (data : Aeneas.Std.Slice U8) (level : U8) (four : Bool) (p len : Usize)
    (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32) (k : Usize)
    (ht : Tables head.val chain.val (p.val + k.val))
    (hk : k.val ≤ len.val) (hd : p.val + len.val ≤ data.val.length) :
    greedy_loop0_loop0.body data level four p len head chain k ⦃ r =>
      match r with
      | .done (hh, ch) => Tables hh.val ch.val (p.val + len.val)
      | .cont (hh, ch, next) => Tables hh.val ch.val (p.val + next.val) ∧
          next.val = k.val + 1 ∧ next.val ≤ len.val ⦄ := by
  unfold greedy_loop0_loop0.body
  step*

@[step]
theorem interior_loop (data : Aeneas.Std.Slice U8) (level : U8) (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32)
    (four : Bool) (p len k : Usize) (ht : Tables head.val chain.val (p.val + k.val))
    (hk : k.val ≤ len.val) (hd : p.val + len.val ≤ data.val.length) :
    greedy_loop0_loop0 data level head chain four p len k ⦃ r => Tables r.1.val r.2.val (p.val + len.val) ⦄ := by
  unfold greedy_loop0_loop0
  apply loop.spec_decr_nat (fun (_, _, j) => len.val - j.val)
    (fun (hh, ch, j) => Tables hh.val ch.val (p.val + j.val) ∧ j.val ≤ len.val)
  · rintro ⟨hh, ch, j⟩ ⟨htj, hj⟩
    refine WP.spec_mono (interior_body data level four p len hh ch j htj hj hd) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨hh', ch', j'⟩ := state
        obtain ⟨ht', he, hj'⟩ := hr
        exact ⟨⟨ht', hj'⟩, by change len.val - j'.val < len.val - j.val; omega⟩
  · exact ⟨ht, hk⟩


/-- The loop invariant of the greedy parse: the plan so far is a run of valid steps, the tables
have their sizes, the carried match (if any) is valid at the current position, and the symbol
indices and counts are the plan's. -/
def State (data : List U8) (start stop p : ℕ) (head : List U32) (chain : List U32) (ls ds : List U16)
    (lsym dsym : List U8) (lit dist : alloc.vec.Vec Usize) (cl cd : Usize) : Prop :=
  start ≤ p ∧ p ≤ stop ∧ Tables head chain p ∧ Runs data stop start p ls ds ∧ Carried data stop p cl cd ∧
  Counting.Counted data start ls ds lsym dsym lit dist

/-- What the loop leaves: the plan of the whole block, its counts, and the tables. -/
def Final (data : List U8) (start stop : ℕ) (head : List U32) (chain : List U32) (ls ds : List U16)
    (lsym dsym : List U8) (lit dist : alloc.vec.Vec Usize) : Prop :=
  Tables head chain stop ∧ Runs data stop start stop ls ds ∧ Counting.Counted data start ls ds lsym dsym lit dist

@[step]
theorem literal_tail_total (level : U8) (start p tokens : Usize) (hp : start.val ≤ p.val) :
    literal_tail level start p tokens ⦃ _ => True ⦄ := by
  unfold literal_tail
  step*

theorem position_body (data : Aeneas.Std.Slice U8) (start : ℕ) (startn stop : Usize)
    (level : U8) (four : Bool) (depth : Usize) (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32)
    (ls ds : alloc.vec.Vec U16) (lsym dsym : alloc.vec.Vec U8) (lit dist : alloc.vec.Vec Usize) (p cl cd : Usize)
    (hbegin : startn.val = start)
    (h : State data.val start stop.val p.val head.val chain.val ls.val ds.val lsym.val dsym.val lit dist cl cd)
    (hd : stop.val ≤ data.val.length) (hs : stop.val - start ≤ 32768) :
    greedy_loop0.body data startn stop level four depth head chain ls ds lsym dsym lit dist p cl cd ⦃ r =>
      match r with
      | .done (hh, ch, l, d, ls', ds', li, di) =>
          Final data.val start stop.val hh.val ch.val l.val d.val ls'.val ds'.val li di
      | .cont (hh, ch, l, d, ls', ds', li, di, next, cl', cd') =>
          State data.val start stop.val next.val hh.val ch.val l.val d.val ls'.val ds'.val li di cl' cd' ∧
          p.val < next.val ⦄ := by
  obtain ⟨hp0, hp1, ht, hr, hc, hcnt⟩ := h
  have hll := runs_lengths hr
  have hls : ls.val.length ≤ 32768 := by omega
  have hds : ds.val.length ≤ 32768 := by omega
  have hlsl := hcnt.symbolized.1
  have hdsl := hcnt.symbolized.2.1
  have hcounts := hcnt.counts
  have hppos := Counting.runs_pos hr
  unfold greedy_loop0.body
  split
  · have hplt : p.val < stop.val := by scalar_tac
    have htcheck := literal_tail_total level startn p (alloc.vec.Vec.len ls) (by omega)
    step as ⟨tail⟩
    split
    · step as ⟨remaining, hremaining⟩
      step as ⟨lcount, hlcount⟩
      have hresize1 := alloc.vec.Vec.resize_spec core.clone.CloneU16 ls lcount 1#u16 (by rfl)
      step as ⟨ls1, hls1⟩
      step as ⟨dcount, hdcount⟩
      have hresize2 := alloc.vec.Vec.resize_spec core.clone.CloneU16 ds dcount 0#u16 (by rfl)
      step as ⟨ds1, hds1⟩
      step as ⟨lscount, hlscount⟩
      have hresize3 := alloc.vec.Vec.resize_spec core.clone.CloneU8 lsym lscount 0#u8 (by rfl)
      step as ⟨lsym1, hlsym1⟩
      step as ⟨dscount, hdscount⟩
      have hresize4 := alloc.vec.Vec.resize_spec core.clone.CloneU8 dsym dscount 0#u8 (by rfl)
      step as ⟨dsym1, hdsym1⟩
      have hcl := Counting.count_literals_spec data p remaining lit dist ls.val.length (by omega) (by omega) hcounts
      step as ⟨lit1, dist1, hc1, hl1, hd1, hcounted⟩
      simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length] at hlcount hdcount hlscount hdscount
      have hlge : ls.val.length ≤ lcount.val := by omega
      have hdge : ds.val.length ≤ dcount.val := by omega
      have hlsge : lsym.val.length ≤ lscount.val := by omega
      have hdsge : dsym.val.length ≤ dscount.val := by omega
      rw [Gzip.Proofs.FastGreedy.resize_append ls.val lcount.val 1#u16 hlge] at hls1
      rw [Gzip.Proofs.FastGreedy.resize_append ds.val dcount.val 0#u16 hdge] at hds1
      rw [Gzip.Proofs.FastGreedy.resize_append lsym.val lscount.val 0#u8 hlsge] at hlsym1
      rw [Gzip.Proofs.FastGreedy.resize_append dsym.val dscount.val 0#u8 hdsge] at hdsym1
      have hln : lcount.val - ls.val.length = remaining.val := by omega
      have hdn : dcount.val - ds.val.length = remaining.val := by omega
      have hlsn : lscount.val - lsym.val.length = remaining.val := by omega
      have hdsn : dscount.val - dsym.val.length = remaining.val := by omega
      rw [hln] at hls1
      rw [hdn] at hds1
      rw [hlsn] at hlsym1
      rw [hdsn] at hdsym1
      have htail := Gzip.Proofs.FastGreedy.append_literals hr remaining.val
      have hfinish : p.val + remaining.val = stop.val := by omega
      rw [hfinish] at htail
      try simp only [WP.spec_ok]
      unfold State
      refine ⟨⟨by omega, Nat.le_refl _, tables_advance_to ht hp1, ?_, carried_none _ _ _, ?_⟩, hplt⟩
      · simpa only [hls1, hds1] using htail
      · rw [hls1, hds1, hlsym1, hdsym1]
        exact Counting.counted_literals hcnt hll.1.symm p.val remaining.val hppos hc1 hl1 hd1 hcounted
    · step as ⟨quad, head1, chain1, hl0, hl1, hm, ht1, hcar, hnl⟩
      rcases quad with ⟨len, dist16, nl, nd⟩
      dsimp only at *
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
        have hnl0 : nl.val = 0 := by
          rcases hnl with h0 | h1
          · exact h0
          · omega
        have hcar0 : ∀ q, Carried data.val stop.val q nl nd := fun _ => Or.inl hnl0
        step as ⟨i1, hi1⟩
        step as ⟨v2, hv2⟩
        step as ⟨i2, hi2⟩
        step as ⟨v3, hv3⟩
        step as ⟨l, hl0', hl1', hl2'⟩
        step as ⟨dc, hd0', hd1', hd2'⟩
        step as ⟨i3, hi3⟩
        step as ⟨lsym1, hlsym1⟩
        step as ⟨i4, hi4⟩
        step as ⟨dsym1, hdsym1⟩
        have hcs := Fused.count_supported data p dist16 l dc lit dist ls.val.length (by omega) (by omega) hcounts
        step as ⟨lit1, dist1, hc1, hlm1, hdm1, hcounted⟩
        have hi3v : i3.val = l.val := by rw [hi3]; exact Symbolize.narrow8_val l (by omega)
        have hi4v : i4.val = dc.val := by rw [hi4]; exact Symbolize.narrow8_val dc (by omega)
        have hi1v : i1.val = len.val := by rw [hi1]; exact narrow_val len (by omega)
        have hi2v : i2.val = dist16.val := by rw [hi2]; exact narrow_val dist16 (by omega)
        have hsupp := hcounted.2 (by omega) (by omega) (by omega)
        have hcnt1 : Counting.Counted data.val start v2.val v3.val lsym1.val dsym1.val lit1 dist1 := by
          rw [hv2, hv3, hlsym1, hdsym1]
          refine Counting.counted_copy hcnt hll.1.symm i1 i2 i3 i4 (by rw [hi2v]; omega) ?_ hc1 hlm1 hdm1 ?_
          · rw [hi3v, hi4v, hi1v, hi2v]
            exact ⟨hl0', hd0', hl1', hl2', hd1', hd2'⟩
          · rw [hi3v, hi4v]
            exact hsupp
        have hrun1 : Runs data.val stop.val start (p.val + len.val) v2.val v3.val := by
          rw [hv2, hv3, hi1, hi2]
          exact hrnew
        step as ⟨k, hk⟩
        split
        · step as ⟨head2, chain2, ht2⟩
          step as ⟨p1, hp1⟩
          try simp only [WP.spec_ok]
          refine ⟨⟨by scalar_tac, by scalar_tac, ?_, ?_, hcar0 _, hcnt1⟩, by scalar_tac⟩
          · rw [hp1]
            exact ht2
          · rw [hp1]
            exact hrun1
        · step as ⟨p1, hp1⟩
          try simp only [WP.spec_ok]
          refine ⟨⟨by scalar_tac, by scalar_tac, tables_advance_to ht1 (by omega), ?_, hcar0 _, hcnt1⟩, by scalar_tac⟩
          rw [hp1]
          exact hrun1
      · step as ⟨v2, hv2⟩
        step as ⟨v3, hv3⟩
        step as ⟨lsym1, hlsym1⟩
        step as ⟨dsym1, hdsym1⟩
        have hcs := Fused.count_supported data p 0#usize 0#usize 0#usize lit dist ls.val.length (by omega) (by omega) hcounts
        step as ⟨lit1, dist1, hc1, hlm1, hdm1, hcounted⟩
        step as ⟨p1, hp1⟩
        try simp only [WP.spec_ok]
        refine ⟨⟨by scalar_tac, by scalar_tac, tables_advance_to ht1 (by omega), ?_, ?_, ?_⟩, by scalar_tac⟩
        · rw [hv2, hv3, hp1]
          simpa using hlit
        · rw [hp1]
          exact hcar
        · rw [hv2, hv3, hlsym1, hdsym1]
          exact Counting.counted_literal hcnt hll.1.symm p.val hppos hc1 hlm1 hdm1 (hcounted.1 (by scalar_tac))
  · rename_i hge
    have he : p = stop := by
      apply (UScalar.eq_equiv _ _).mpr
      scalar_tac
    subst he
    try simp only [WP.spec_ok]
    exact ⟨ht, hr, hcnt⟩

@[step]
theorem position_loop (data : Aeneas.Std.Slice U8) (start : ℕ) (startn stop : Usize)
    (level : U8) (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32) (four : Bool)
    (ls ds : alloc.vec.Vec U16) (lsym dsym : alloc.vec.Vec U8) (lit dist : alloc.vec.Vec Usize)
    (depth p cl cd : Usize)
    (hbegin : startn.val = start)
    (h : State data.val start stop.val p.val head.val chain.val ls.val ds.val lsym.val dsym.val lit dist cl cd)
    (hd : stop.val ≤ data.val.length) (hs : stop.val - start ≤ 32768) :
    greedy_loop0 data startn stop level head chain four ls ds lsym dsym lit dist depth p cl cd ⦃ r =>
      Final data.val start stop.val r.1.val r.2.1.val r.2.2.1.val r.2.2.2.1.val
        r.2.2.2.2.1.val r.2.2.2.2.2.1.val r.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2 ⦄ := by
  unfold greedy_loop0
  apply loop.spec_decr_nat (fun (_, _, _, _, _, _, _, _, q, _, _) => stop.val - q.val)
    (fun (hh, ch, l, d, ls', ds', li, di, q, cl', cd') =>
      State data.val start stop.val q.val hh.val ch.val l.val d.val ls'.val ds'.val li di cl' cd')
  · rintro ⟨hh, ch, l, d, ls', ds', li, di, q, cl', cd'⟩ hq
    refine WP.spec_mono (position_body data start startn stop level four depth hh ch l d ls' ds' li di q cl' cd' hbegin hq hd hs) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨hh', ch', l', d', ls'', ds'', li', di', q', cl'', cd''⟩ := state
        obtain ⟨h', hnext⟩ := hr
        exact ⟨h', by have hb := h'.2.1; change stop.val - q'.val < stop.val - q.val; omega⟩
  · exact h

/-- The counted parse of a block: the plan is a run of tokens over the block and its arrays are
the plan's. -/
theorem finish_correct (data : Aeneas.Std.Slice U8) (start stop : Usize) (head1 chain1 : alloc.vec.Vec U32)
    (v2 v3 : alloc.vec.Vec U16) (lsym1 dsym1 : alloc.vec.Vec U8) (lit1 dist1 : alloc.vec.Vec Usize)
    (hsize : stop.val - start.val ≤ 32768)
    (hstate : Final data.val start.val stop.val head1.val chain1.val v2.val v3.val lsym1.val dsym1.val lit1 dist1) :
    ((do
      let i1 ← lit1.index_usize 256#usize
      let c ← i1 + 1#usize
      let (_, index_mut_back) ← lit1.index_mut_usize 256#usize
      ok ((Parsed.mk (Plan.mk v2 v3) lsym1 dsym1 (index_mut_back c) dist1 true), head1, chain1)) :
      Result (Parsed × alloc.vec.Vec U32 × alloc.vec.Vec U32)) ⦃ r =>
      Counting.ParsedOk data.val start.val stop.val r.1 ∧ r.1.fused = true ∧
      Tables r.2.1.val r.2.2.val stop.val ⦄ := by
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
      Tables head1.val chain1.val stop.val := by
    refine ⟨⟨hr1, fun _ => ?_⟩, rfl, ht1⟩
    simp only [hback, alloc.vec.Vec.set_val_eq, UScalar.ofNatCore_val_eq]
    exact hfin
  simpa only [WP.spec_ok, true_and] using hpost

@[step]
theorem greedy_correct (data : Aeneas.Std.Slice U8) (start stop : Usize) (level : U8)
    (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32) (four : Bool)
    (hlt : LTables level.val head.val chain.val start.val)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length)
    (hsize : stop.val - start.val ≤ 32768) (hl : level.val < 16) :
    greedy data start stop level head chain four ⦃ r =>
      Counting.ParsedOk data.val start.val stop.val r.1 ∧ r.1.fused = true ∧
      LTables level.val r.2.1.val r.2.2.val stop.val ⦄ := by
  have hwidth := System.Platform.sixteen_le_numBits
  unfold greedy
  split
  · rename_i hl1
    have hg := Gzip.Proofs.FastGreedy.greedy_fast_correct data start stop head hlt.1 hs hd hsize
    step as ⟨p, head1, hpo, hfu, hh⟩
    try simp only [WP.spec_ok]
    refine ⟨hpo, hfu, hh, Or.inl ?_⟩
    rw [hl1]
    rfl
  · rename_i hl1
    have hne : level.val ≠ 1 := by
      intro h
      apply hl1
      apply (UScalar.eq_equiv _ _).mpr
      simpa using h
    have ht : Tables head.val chain.val start.val := tables_of_ltables hlt hne
    refine WP.spec_mono (P₀ := fun r => Counting.ParsedOk data.val start.val stop.val r.1 ∧ r.1.fused = true ∧
      Tables r.2.1.val r.2.2.val stop.val) ?_ (fun r h => ⟨h.1, h.2.1, ltables_of_tables h.2.2⟩)
    dsimp only
    step as ⟨i, hi⟩
    step as ⟨lit, hlit⟩
    step as ⟨dist, hdist⟩
    have hinitial : State data.val start.val stop.val start.val head.val chain.val
        (alloc.vec.Vec.with_capacity U16 i).val (alloc.vec.Vec.with_capacity U16 i).val
        (alloc.vec.Vec.with_capacity U8 i).val (alloc.vec.Vec.with_capacity U8 i).val lit dist 0#usize 0#usize := by
      refine ⟨Nat.le_refl _, hs, ht, ?_, carried_none _ _ _, ?_⟩
      · simp only [alloc.vec.Vec.with_capacity]
        exact Runs.finish start.val
      · simp only [alloc.vec.Vec.with_capacity]
        exact Counting.counted_nil data.val start.val lit dist (by rw [hlit]) (by rw [hdist])
    step as ⟨depth, _⟩
    step as ⟨head1, chain1, v2, v3, lsym1, dsym1, lit1, dist1, hstate⟩
    exact finish_correct data start stop head1 chain1 v2 v3 lsym1 dsym1 lit1 dist1 hsize hstate

end Gzip.Proofs.Greedy
