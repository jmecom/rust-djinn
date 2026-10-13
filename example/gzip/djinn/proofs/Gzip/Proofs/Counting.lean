import Gzip.Proofs.Fused

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Plans Gzip.Proofs.Matches Gzip.Proofs.Fused Gzip.Proofs.Symbolize

set_option maxHeartbeats 2000000

/-! The greedy parsers count the symbol indices and frequencies of their plans as they go
(what `symbols_histogram` would count afterwards). `Counted` is the invariant they keep over
the plan so far, with its extension by one copy, one literal, or a run of literals. -/

namespace Gzip.Proofs.Counting

/-- The symbol indices and frequencies of a plan prefix. -/
structure Counted (data : List U8) (start : ℕ) (ls ds : List U16) (lsym dsym : List U8)
    (lit dist : alloc.vec.Vec Usize) : Prop where
  symbolized : Symbolized ls ds lsym dsym
  counts : Counts lit dist ls.length
  support : ∀ j < ls.length, SupportAt data start ls ds lsym dsym lit.val dist.val j

theorem mono_refl (v : List Usize) : Mono v v := fun _ => Nat.le_refl _

theorem mono_trans {a b c : List Usize} (h1 : Mono a b) (h2 : Mono b c) : Mono a c :=
  fun i => Nat.le_trans (h1 i) (h2 i)

theorem counted_nil (data : List U8) (start : ℕ) (lit dist : alloc.vec.Vec Usize)
    (hl : lit.val = List.replicate 286 0#usize) (hd : dist.val = List.replicate 30 0#usize) :
    Counted data start [] [] [] [] lit dist := by
  refine ⟨⟨rfl, rfl, fun t ht => by simp at ht⟩, ⟨?_, ?_, ?_, ?_⟩, fun j hj => by simp at hj⟩
  · rw [hl, List.length_replicate]
  · rw [hd, List.length_replicate]
  · intro i hi
    rw [hl, List.getElem!_replicate] <;> scalar_tac
  · intro i hi
    rw [hd, List.getElem!_replicate] <;> scalar_tac

/-! ### Positions -/

theorem runs_sum {data : List U8} {stop p q : ℕ} {ls ds : List U16} (h : Runs data stop p q ls ds) :
    q = p + (ls.map (fun x => x.val)).sum := by
  induction h with
  | finish => simp
  | next p q l d ls ds hv ht ih =>
      simp only [List.map_cons, List.sum_cons]
      omega

theorem pos_end (ls : List U16) (start : ℕ) :
    Body.pos ls start ls.length = start + (ls.map (fun x => x.val)).sum := by
  simp [Body.pos, List.take_length]

/-- The end of a run of tokens is the position after its last token. -/
theorem runs_pos {data : List U8} {stop start p : ℕ} {ls ds : List U16}
    (h : Runs data stop start p ls ds) : p = Body.pos ls start ls.length := by
  rw [pos_end]
  exact runs_sum h

theorem pos_append_left (ls more : List U16) (start t : ℕ) (ht : t ≤ ls.length) :
    Body.pos (ls ++ more) start t = Body.pos ls start t := by
  simp only [Body.pos, List.take_append_of_le_length ht]

theorem sum_ones (k : ℕ) : ((List.replicate k 1#u16).map (fun x => x.val)).sum = k := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [List.replicate_succ, List.map_cons, List.sum_cons, ih]
      rw [show (1#u16).val = 1 by scalar_tac]
      omega

theorem pos_append_replicate (ls : List U16) (start n k : ℕ) (hk : k ≤ n) :
    Body.pos (ls ++ List.replicate n 1#u16) start (ls.length + k) = Body.pos ls start ls.length + k := by
  unfold Body.pos
  rw [List.take_append, List.take_of_length_le (by omega : ls.length ≤ ls.length + k),
    Nat.add_sub_cancel_left, List.take_replicate, Nat.min_eq_left hk, List.map_append, List.sum_append,
    sum_ones, List.take_length]
  omega

/-! ### Extending the symbol indices -/

theorem symbolized_append {ls ds : List U16} {lsym dsym : List U8} (h : Symbolized ls ds lsym dsym)
    (hlen : ds.length = ls.length) (len dist : U16) (l d : U8)
    (hnew : dist.val ≠ 0 →
      l.val ≤ 28 ∧ d.val ≤ 29 ∧ Indices.lb l.val ≤ len.val ∧ len.val - Indices.lb l.val < 2 ^ Indices.le l.val ∧
      Indices.db d.val ≤ dist.val ∧ dist.val - Indices.db d.val < 2 ^ Indices.de d.val) :
    Symbolized (ls ++ [len]) (ds ++ [dist]) (lsym ++ [l]) (dsym ++ [d]) := by
  obtain ⟨hl, hd, hprev⟩ := h
  refine ⟨by simp [hl], by simp [hd], ?_⟩
  intro t ht hnz
  simp only [List.length_append, List.length_singleton] at ht
  by_cases hlt : t < ls.length
  · rw [List.getElem!_append_left ds [dist] t (by omega)] at hnz
    rw [List.getElem!_append_left ls [len] t hlt, List.getElem!_append_left ds [dist] t (by omega),
      List.getElem!_append_left lsym [l] t (by omega), List.getElem!_append_left dsym [d] t (by omega)]
    exact hprev t hlt hnz
  · have he : t = ls.length := by omega
    subst he
    rw [List.getElem!_append_right ds [dist] _ (by omega)] at hnz
    rw [List.getElem!_append_right ls [len] _ (by omega), List.getElem!_append_right ds [dist] _ (by omega),
      List.getElem!_append_right lsym [l] _ (by omega), List.getElem!_append_right dsym [d] _ (by omega)]
    simp only [hl, hd, hlen, Nat.sub_self, List.getElem!_cons_zero] at hnz ⊢
    exact hnew hnz

theorem symbolized_append_literals {ls ds : List U16} {lsym dsym : List U8} (h : Symbolized ls ds lsym dsym)
    (hlen : ds.length = ls.length) (n : ℕ) :
    Symbolized (ls ++ List.replicate n 1#u16) (ds ++ List.replicate n 0#u16)
      (lsym ++ List.replicate n 0#u8) (dsym ++ List.replicate n 0#u8) := by
  obtain ⟨hl, hd, hprev⟩ := h
  refine ⟨by simp [hl], by simp [hd], ?_⟩
  intro t ht hnz
  simp only [List.length_append, List.length_replicate] at ht
  by_cases hlt : t < ls.length
  · rw [List.getElem!_append_left ds _ t (by omega)] at hnz
    rw [List.getElem!_append_left ls _ t hlt, List.getElem!_append_left ds _ t (by omega),
      List.getElem!_append_left lsym _ t (by omega), List.getElem!_append_left dsym _ t (by omega)]
    exact hprev t hlt hnz
  · exfalso
    rw [List.getElem!_append_right ds _ t (by omega),
      List.getElem!_replicate (0#u16) (n := n) (i := t - ds.length) (by omega)] at hnz
    exact hnz (by scalar_tac)

/-! ### Extending the support -/

/-- The old tokens stay supported when the lists grow and the counts do not drop. -/
theorem support_append {data : List U8} {start : ℕ} {ls ds more mored : List U16} {lsym dsym morel moredd : List U8}
    {lit dist lit' dist' : List Usize}
    (hl : Mono lit lit') (hd : Mono dist dist') (hlen : ds.length = ls.length)
    (hls : lsym.length = ls.length) (hds : dsym.length = ls.length)
    (hsupp : ∀ j < ls.length, SupportAt data start ls ds lsym dsym lit dist j) :
    ∀ j < ls.length, SupportAt data start (ls ++ more) (ds ++ mored) (lsym ++ morel) (dsym ++ moredd) lit' dist' j := by
  intro j hj
  have hold := supportAt_mono hl hd (hsupp j hj)
  unfold SupportAt at hold ⊢
  rw [List.getElem!_append_left ds mored j (by omega), List.getElem!_append_left lsym morel j (by omega),
    List.getElem!_append_left dsym moredd j (by omega), pos_append_left ls more start j (by omega)]
  exact hold

/-- The plan so far, extended by a copy whose symbols were counted. -/
theorem counted_copy {data : List U8} {start : ℕ} {ls ds : List U16} {lsym dsym : List U8}
    {lit dist lit' dist' : alloc.vec.Vec Usize} (h : Counted data start ls ds lsym dsym lit dist)
    (hlen : ds.length = ls.length) (len dist16 : U16) (l d : U8)
    (hdn : dist16.val ≠ 0)
    (hidx : l.val ≤ 28 ∧ d.val ≤ 29 ∧ Indices.lb l.val ≤ len.val ∧ len.val - Indices.lb l.val < 2 ^ Indices.le l.val ∧
      Indices.db d.val ≤ dist16.val ∧ dist16.val - Indices.db d.val < 2 ^ Indices.de d.val)
    (hc : Counts lit' dist' (ls.length + 1)) (hlm : Mono lit.val lit'.val) (hdm : Mono dist.val dist'.val)
    (hcounted : 0 < (lit'.val[257 + l.val]!).val ∧ 0 < (dist'.val[d.val]!).val) :
    Counted data start (ls ++ [len]) (ds ++ [dist16]) (lsym ++ [l]) (dsym ++ [d]) lit' dist' := by
  obtain ⟨hsym, hcounts, hsupp⟩ := h
  refine ⟨symbolized_append hsym hlen len dist16 l d (fun _ => hidx), ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]
    exact hc
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < ls.length
    · exact support_append hlm hdm hlen hsym.1 hsym.2.1 hsupp j hlt
    · have he : j = ls.length := by omega
      subst he
      have hls := hsym.1
      have hds := hsym.2.1
      unfold SupportAt
      rw [List.getElem!_append_right ds [dist16] _ (by omega), List.getElem!_append_right lsym [l] _ (by omega),
        List.getElem!_append_right dsym [d] _ (by omega)]
      simp only [hlen, hsym.1, hsym.2.1, Nat.sub_self, List.getElem!_cons_zero]
      rw [if_neg hdn]
      exact hcounted

/-- The plan so far, extended by a literal whose byte was counted (`p` is its position). -/
theorem counted_literal {data : List U8} {start : ℕ} {ls ds : List U16} {lsym dsym : List U8}
    {lit dist lit' dist' : alloc.vec.Vec Usize} (h : Counted data start ls ds lsym dsym lit dist)
    (hlen : ds.length = ls.length) (p : ℕ) (hp : p = Body.pos ls start ls.length)
    (hc : Counts lit' dist' (ls.length + 1)) (hlm : Mono lit.val lit'.val) (hdm : Mono dist.val dist'.val)
    (hcounted : 0 < (lit'.val[(data[p]!).val]!).val) :
    Counted data start (ls ++ [1#u16]) (ds ++ [0#u16]) (lsym ++ [0#u8]) (dsym ++ [0#u8]) lit' dist' := by
  obtain ⟨hsym, hcounts, hsupp⟩ := h
  have h0 : (0#u16).val = 0 := by scalar_tac
  refine ⟨symbolized_append hsym hlen 1#u16 0#u16 0#u8 0#u8 (fun hz => absurd h0 hz), ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]
    exact hc
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < ls.length
    · exact support_append hlm hdm hlen hsym.1 hsym.2.1 hsupp j hlt
    · have he : j = ls.length := by omega
      subst he
      unfold SupportAt
      rw [List.getElem!_append_right ds [0#u16] _ (by omega), pos_append_left ls [1#u16] start _ (Nat.le_refl _)]
      simp only [hlen, Nat.sub_self, List.getElem!_cons_zero]
      rw [if_pos h0, ← hp]
      exact hcounted

/-- The plan so far, extended by `n` literals from position `p` on, all counted. -/
theorem counted_literals {data : List U8} {start : ℕ} {ls ds : List U16} {lsym dsym : List U8}
    {lit dist lit' dist' : alloc.vec.Vec Usize} (h : Counted data start ls ds lsym dsym lit dist)
    (hlen : ds.length = ls.length) (p n : ℕ) (hp : p = Body.pos ls start ls.length)
    (hc : Counts lit' dist' (ls.length + n)) (hlm : Mono lit.val lit'.val) (hdm : Mono dist.val dist'.val)
    (hcounted : ∀ k < n, 0 < (lit'.val[(data[p + k]!).val]!).val) :
    Counted data start (ls ++ List.replicate n 1#u16) (ds ++ List.replicate n 0#u16)
      (lsym ++ List.replicate n 0#u8) (dsym ++ List.replicate n 0#u8) lit' dist' := by
  obtain ⟨hsym, hcounts, hsupp⟩ := h
  refine ⟨symbolized_append_literals hsym hlen n, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]
    exact hc
  · intro j hj
    simp only [List.length_append, List.length_replicate] at hj
    by_cases hlt : j < ls.length
    · exact support_append hlm hdm hlen hsym.1 hsym.2.1 hsupp j hlt
    · have hk : j = ls.length + (j - ls.length) := by omega
      have h0 : (0#u16).val = 0 := by scalar_tac
      have hpos : Body.pos (ls ++ List.replicate n 1#u16) start j = p + (j - ls.length) := by
        have hr := pos_append_replicate ls start n (j - ls.length) (by omega)
        rw [← hk] at hr
        rw [hr, hp]
      unfold SupportAt
      rw [List.getElem!_append_right ds _ j (by omega),
        List.getElem!_replicate (0#u16) (n := n) (i := j - ds.length) (by omega), if_pos h0, hpos]
      exact hcounted (j - ls.length) (by omega)

/-- Counting the end-of-block symbol (the block writer's last) completes the frequencies:
every token's symbols and the end of block have a count. -/
theorem counted_finish {data : List U8} {start : ℕ} {ls ds : List U16} {lsym dsym : List U8}
    {lit dist : alloc.vec.Vec Usize} (h : Counted data start ls ds lsym dsym lit dist)
    (c : Usize) (hc : (lit.val[256]!).val < c.val) (h256 : 256 < lit.val.length) :
    Symbolized ls ds lsym dsym ∧ (lit.val.set 256 c).length = 286 ∧ dist.val.length = 30 ∧
      Support data start ls ds lsym dsym (lit.val.set 256 c) dist.val := by
  refine ⟨h.symbolized, by rw [List.length_set]; exact h.counts.litLen, h.counts.distLen, ?_, ?_⟩
  · intro j hj
    exact supportAt_mono (mono_set lit.val 256 c (Nat.le_of_lt hc)) (mono_refl _) (h.support j hj)
  · rw [Djinn.Vocab.getElem!_set lit.val 256 256 c h256, if_pos rfl]
    omega

/-! ### The helpers of the parse loops -/

/-- Whether a match is taken: only a real copy is. -/
@[step]
theorem taken_spec (len dist : Usize) : taken len dist ⦃ r => r = true → 0 < dist.val ⦄ := by
  unfold taken
  split
  · rename_i hnz
    split
    · simp only [WP.spec_ok]
      intro _
      scalar_tac
    · simp only [WP.spec_ok]
      intro _
      scalar_tac
  · simp

theorem count_literals_body (data : Aeneas.Std.Slice U8) (p n : Usize)
    (lit0 dist0 lit dist : alloc.vec.Vec Usize) (k : Usize) (t : ℕ)
    (hp : p.val + n.val ≤ data.val.length) (hn : t + n.val ≤ 1048576)
    (hk : k.val ≤ n.val) (hc : Counts lit dist (t + k.val))
    (hlm : Mono lit0.val lit.val) (hdm : Mono dist0.val dist.val)
    (hsupp : ∀ j < k.val, 0 < (lit.val[(data.val[p.val + j]!).val]!).val) :
    count_literals_loop.body data p n lit dist k ⦃ r =>
      match r with
      | .done (lit', dist') => Counts lit' dist' (t + n.val) ∧ Mono lit0.val lit'.val ∧ Mono dist0.val dist'.val ∧
          ∀ j < n.val, 0 < (lit'.val[(data.val[p.val + j]!).val]!).val
      | .cont (lit', dist', k') => k'.val = k.val + 1 ∧ k'.val ≤ n.val ∧ Counts lit' dist' (t + k'.val) ∧
          Mono lit0.val lit'.val ∧ Mono dist0.val dist'.val ∧
          ∀ j < k'.val, 0 < (lit'.val[(data.val[p.val + j]!).val]!).val ⦄ := by
  unfold count_literals_loop.body
  split
  · rename_i hlt
    have hlt' : k.val < n.val := by scalar_tac
    step as ⟨i, hi⟩
    have hcs := count_supported data i 0#usize 0#usize 0#usize lit dist (t + k.val) (by omega) (by omega) hc
    step as ⟨lit1, dist1, hc1, hl1, hd1, hcounted⟩
    step as ⟨k1, hk1⟩
    try simp only [WP.spec_ok]
    refine ⟨hk1, by omega, by rw [hk1, ← Nat.add_assoc]; exact hc1, mono_trans hlm hl1, mono_trans hdm hd1, ?_⟩
    intro j hj
    by_cases hjk : j < k.val
    · exact Nat.lt_of_lt_of_le (hsupp j hjk) (hl1 _)
    · have he : j = k.val := by omega
      subst he
      have h0 := hcounted.1 (by scalar_tac)
      rw [hi] at h0
      exact h0
  · rename_i hge
    have he : k.val = n.val := by scalar_tac
    simp only [WP.spec_ok]
    refine ⟨by rw [← he]; exact hc, hlm, hdm, ?_⟩
    intro j hj
    exact hsupp j (by omega)

theorem count_literals_loop_spec (data : Aeneas.Std.Slice U8) (p n : Usize)
    (lit0 dist0 lit dist : alloc.vec.Vec Usize) (k : Usize) (t : ℕ)
    (hp : p.val + n.val ≤ data.val.length) (hn : t + n.val ≤ 1048576)
    (hk : k.val ≤ n.val) (hc : Counts lit dist (t + k.val))
    (hlm : Mono lit0.val lit.val) (hdm : Mono dist0.val dist.val)
    (hsupp : ∀ j < k.val, 0 < (lit.val[(data.val[p.val + j]!).val]!).val) :
    count_literals_loop data p n lit dist k ⦃ r =>
      Counts r.1 r.2 (t + n.val) ∧ Mono lit0.val r.1.val ∧ Mono dist0.val r.2.val ∧
      ∀ j < n.val, 0 < (r.1.val[(data.val[p.val + j]!).val]!).val ⦄ := by
  unfold count_literals_loop
  apply loop.spec_decr_nat (fun (_, _, k') => n.val - k'.val)
    (fun (lit', dist', k') => k'.val ≤ n.val ∧ Counts lit' dist' (t + k'.val) ∧
      Mono lit0.val lit'.val ∧ Mono dist0.val dist'.val ∧
      ∀ j < k'.val, 0 < (lit'.val[(data.val[p.val + j]!).val]!).val)
  · rintro ⟨lit', dist', k'⟩ ⟨hk', hc', hl', hd', hs'⟩
    refine WP.spec_mono (count_literals_body data p n lit0 dist0 lit' dist' k' t hp hn hk' hc' hl' hd' hs') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨lit'', dist'', k''⟩ := state
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
        exact ⟨⟨h2, h3, h4, h5, h6⟩, by change n.val - k''.val < n.val - k'.val; omega⟩
  · exact ⟨hk, hc, hlm, hdm, hsupp⟩

/-- `n` literals from `p` on, counted: the counts grow by `n`, never drop, and every one of the
bytes has a count. -/
theorem count_literals_spec (data : Aeneas.Std.Slice U8) (p n : Usize)
    (lit dist : alloc.vec.Vec Usize) (t : ℕ)
    (hp : p.val + n.val ≤ data.val.length) (hn : t + n.val ≤ 1048576) (hc : Counts lit dist t) :
    count_literals data p n lit dist ⦃ r =>
      Counts r.1 r.2 (t + n.val) ∧ Mono lit.val r.1.val ∧ Mono dist.val r.2.val ∧
      ∀ j < n.val, 0 < (r.1.val[(data.val[p.val + j]!).val]!).val ⦄ := by
  unfold count_literals
  have h0 : (0#usize).val = 0 := by scalar_tac
  exact count_literals_loop_spec data p n lit dist lit dist 0#usize t hp hn (by rw [h0]; exact Nat.zero_le _)
    (by rw [h0, Nat.add_zero]; exact hc) (mono_refl _) (mono_refl _) (fun j hj => by rw [h0] at hj; omega)

/-! ### A parse as the block writer takes it -/

/-- The plan is a run of tokens over the span, and when its arrays were counted during the
parse (`fused`), they are the plan's symbol indices and the frequencies of its symbols. -/
def ParsedOk (data : List U8) (start stop : ℕ) (pr : Parsed) : Prop :=
  Runs data stop start stop pr.plan.lengths.val pr.plan.distances.val ∧
  (pr.fused = true →
    Symbolized pr.plan.lengths.val pr.plan.distances.val pr.lsym.val pr.dsym.val ∧
    pr.lfreq.val.length = 286 ∧ pr.dfreq.val.length = 30 ∧
    Support data start pr.plan.lengths.val pr.plan.distances.val pr.lsym.val pr.dsym.val pr.lfreq.val pr.dfreq.val)

@[step]
theorem unfused_spec (plan : Plan) : unfused plan ⦃ r => r.plan = plan ∧ r.fused = false ⦄ := by
  unfold unfused
  simp

theorem parsedOk_unfused {data : List U8} {start stop : ℕ} {pr : Parsed} {plan : Plan}
    (h : pr.plan = plan) (hf : pr.fused = false)
    (hr : Runs data stop start stop plan.lengths.val plan.distances.val) : ParsedOk data start stop pr := by
  refine ⟨by rw [h]; exact hr, ?_⟩
  intro hf'
  rw [hf] at hf'
  cases hf'

end Gzip.Proofs.Counting
