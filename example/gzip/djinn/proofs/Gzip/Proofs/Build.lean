import Gzip.Proofs.Body
import Gzip.Proofs.Histogram
import Gzip.Proofs.Symbolize
import Gzip.Proofs.CostHistogram
import Gzip.Proofs.Smooth

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Plans Gzip.Proofs.Codes Gzip.Proofs.Header

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Gzip.Proofs.Build

/-- Everything `build_tables` guarantees when it reports success. -/
structure TablesOk (data : List U8) (start : ℕ) (ls ds : List U16) (lsym dsym : List U8) (tb : Tables) : Prop where
  litLen : 257 ≤ tb.lit.lens.val.length ∧ tb.lit.lens.val.length ≤ 286
  distLen : 1 ≤ tb.dist.lens.val.length ∧ tb.dist.lens.val.length ≤ 30
  clLen : tb.cl.lens.val.length = 19
  lit : Canon.CodeOk tb.lit 15
  dist : Canon.CodeOk tb.dist 15
  cl : Canon.CodeOk tb.cl 7
  usable : Body.Usable data start ls ds lsym dsym tb.lit.lens.val tb.dist.lens.val
  covers : Covers (tb.lit.lens.val ++ tb.dist.lens.val) 0 tb.syms.val tb.extras.val
  items : Usable tb.cl.lens.val tb.syms.val
  hclen : 4 ≤ tb.hclen.val ∧ tb.hclen.val ≤ 19
  trailing : ∀ k, tb.hclen.val ≤ k → k < 19 → (tb.cl.lens.val[clOrder[k]!]!).val = 0
  itemsLen : tb.syms.val.length ≤ 316

unseal CL_ORDER in
theorem cl_order_table : ∀ k : Fin 19, (CL_ORDER.val[k.val]!).val = clOrder[k.val]! := by
  decide

theorem cl_order_len : CL_ORDER.val.length = 19 := by
  simp [CL_ORDER, Array.make]

/-! ### Concatenating the two codes' lengths -/

theorem concat0_body (c : Code) (pre : List U8) (all : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ c.lens.val.length) (hall : all.val = pre ++ c.lens.val.take i.val)
    (hsmall : c.lens.val.length ≤ 1024) (hpre : pre.length ≤ 1024) :
    build_tables_loop0.body c all i ⦃ r =>
      match r with
      | .done (l, w, rv, all') => l = c.lens ∧ w = c.words ∧ rv = c.rev ∧ all'.val = pre ++ c.lens.val
      | .cont (all', i') => i'.val = i.val + 1 ∧ i'.val ≤ c.lens.val.length ∧
          all'.val = pre ++ c.lens.val.take i'.val ⦄ := by
  unfold build_tables_loop0.body
  dsimp only
  split
  · rename_i hlt
    have hlt' : i.val < c.lens.val.length := by
      have := (UScalar.lt_equiv _ _).mp hlt
      simpa [alloc.vec.Vec.len_val, alloc.vec.Vec.length] using this
    step as ⟨i2, hi2⟩
    have hspace : all.val.length < Usize.max := by
      rw [hall, List.length_append, List.length_take]; scalar_tac
    step as ⟨all1, hall1⟩
    step as ⟨i3, hi3⟩
    try simp only [WP.spec_ok]
    refine ⟨hi3, by scalar_tac, ?_⟩
    rw [hall1, hall, hi3, List.take_succ_eq_append_getElem hlt', hi2, List.append_assoc]
  · rename_i hge
    have he : i.val = c.lens.val.length := by
      have := (UScalar.lt_equiv _ _).not.mp hge
      simp [alloc.vec.Vec.len_val, alloc.vec.Vec.length] at this
      omega
    try simp only [WP.spec_ok]
    refine ⟨by first | trivial | rfl, by first | trivial | rfl, by first | trivial | rfl, ?_⟩
    rw [hall, he, List.take_length]

@[step]
theorem concat0_loop (c : Code) (pre : List U8) (all : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ c.lens.val.length) (hall : all.val = pre ++ c.lens.val.take i.val)
    (hsmall : c.lens.val.length ≤ 1024) (hpre : pre.length ≤ 1024) :
    build_tables_loop0 c all i ⦃ r =>
      r.1 = c.lens ∧ r.2.1 = c.words ∧ r.2.2.1 = c.rev ∧ r.2.2.2.val = pre ++ c.lens.val ⦄ := by
  unfold build_tables_loop0
  apply loop.spec_decr_nat (fun (_, i') => c.lens.val.length - i'.val)
    (fun (all', i') => i'.val ≤ c.lens.val.length ∧ all'.val = pre ++ c.lens.val.take i'.val)
  · rintro ⟨all', i'⟩ ⟨hi', hall'⟩
    refine WP.spec_mono (concat0_body c pre all' i' hi' hall' hsmall hpre) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨a, j⟩ := state
        exact ⟨⟨hr.2.1, hr.2.2⟩, by change c.lens.val.length - j.val < c.lens.val.length - i'.val; omega⟩
  · exact ⟨hi, hall⟩

theorem concat1_body (c : Code) (pre : List U8) (all : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ c.lens.val.length) (hall : all.val = pre ++ c.lens.val.take i.val)
    (hsmall : c.lens.val.length ≤ 1024) (hpre : pre.length ≤ 1024) :
    build_tables_loop1.body c all i ⦃ r =>
      match r with
      | .done (l, w, rv, all') => l = c.lens ∧ w = c.words ∧ rv = c.rev ∧ all'.val = pre ++ c.lens.val
      | .cont (all', i') => i'.val = i.val + 1 ∧ i'.val ≤ c.lens.val.length ∧
          all'.val = pre ++ c.lens.val.take i'.val ⦄ := by
  unfold build_tables_loop1.body
  dsimp only
  split
  · rename_i hlt
    have hlt' : i.val < c.lens.val.length := by
      have := (UScalar.lt_equiv _ _).mp hlt
      simpa [alloc.vec.Vec.len_val, alloc.vec.Vec.length] using this
    step as ⟨i2, hi2⟩
    have hspace : all.val.length < Usize.max := by
      rw [hall, List.length_append, List.length_take]; scalar_tac
    step as ⟨all1, hall1⟩
    step as ⟨i3, hi3⟩
    try simp only [WP.spec_ok]
    refine ⟨hi3, by scalar_tac, ?_⟩
    rw [hall1, hall, hi3, List.take_succ_eq_append_getElem hlt', hi2, List.append_assoc]
  · rename_i hge
    have he : i.val = c.lens.val.length := by
      have := (UScalar.lt_equiv _ _).not.mp hge
      simp [alloc.vec.Vec.len_val, alloc.vec.Vec.length] at this
      omega
    try simp only [WP.spec_ok]
    refine ⟨by first | trivial | rfl, by first | trivial | rfl, by first | trivial | rfl, ?_⟩
    rw [hall, he, List.take_length]

@[step]
theorem concat1_loop (c : Code) (pre : List U8) (all : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ c.lens.val.length) (hall : all.val = pre ++ c.lens.val.take i.val)
    (hsmall : c.lens.val.length ≤ 1024) (hpre : pre.length ≤ 1024) :
    build_tables_loop1 c all i ⦃ r =>
      r.1 = c.lens ∧ r.2.1 = c.words ∧ r.2.2.1 = c.rev ∧ r.2.2.2.val = pre ++ c.lens.val ⦄ := by
  unfold build_tables_loop1
  apply loop.spec_decr_nat (fun (_, i') => c.lens.val.length - i'.val)
    (fun (all', i') => i'.val ≤ c.lens.val.length ∧ all'.val = pre ++ c.lens.val.take i'.val)
  · rintro ⟨all', i'⟩ ⟨hi', hall'⟩
    refine WP.spec_mono (concat1_body c pre all' i' hi' hall' hsmall hpre) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨a, j⟩ := state
        exact ⟨⟨hr.2.1, hr.2.2⟩, by change c.lens.val.length - j.val < c.lens.val.length - i'.val; omega⟩
  · exact ⟨hi, hall⟩

/-! ### The code-length code's frequencies -/

theorem count_body (syms : alloc.vec.Vec Usize) (i : Usize) (cfreq : alloc.vec.Vec Usize)
    (hsmall : syms.val.length ≤ 1024) (hi : i.val ≤ syms.val.length) (hc : cfreq.val.length = 19)
    (hb : ∀ k < 19, (cfreq.val[k]!).val ≤ i.val) :
    build_tables_loop2.body syms i cfreq ⦃ r =>
      match r with
      | .done cfreq' => cfreq'.val.length = 19
      | .cont (i', cfreq') => i'.val = i.val + 1 ∧ i'.val ≤ syms.val.length ∧ cfreq'.val.length = 19 ∧
          ∀ k < 19, (cfreq'.val[k]!).val ≤ i'.val ⦄ := by
  unfold build_tables_loop2.body
  dsimp only
  split
  · rename_i hlt
    have hlt' : i.val < syms.val.length := by scalar_tac
    step as ⟨s, hs⟩
    have hcSpec : (if s < 19#usize then do
          let i2 ← alloc.vec.Vec.index_usize cfreq s
          let c ← i2 + 1#usize
          let (_, index_mut_back) ← alloc.vec.Vec.index_mut_usize cfreq s
          ok (index_mut_back c)
        else ok cfreq) ⦃ r => r.val.length = 19 ∧ ∀ k < 19, (r.val[k]!).val ≤ i.val + 1 ⦄ := by
      split
      · rename_i hs19
        have hs19' : s.val < cfreq.val.length := by rw [hc]; scalar_tac
        step as ⟨i2, hi2⟩
        have hi2b : i2.val ≤ i.val := by rw [hi2, ← getElem!_pos cfreq.val s.val hs19']; exact hb s.val (by omega)
        step as ⟨c, hcv⟩
        step as ⟨x, back, hx, hback⟩
        simp only [hback, alloc.vec.Vec.set_val_eq, WP.spec_ok]
        refine ⟨by simp only [List.length_set]; exact hc, ?_⟩
        intro k hk
        rw [Djinn.Vocab.getElem!_set cfreq.val s.val k c (by rw [hc]; exact hk)]
        split
        · omega
        · exact Nat.le_succ_of_le (hb k hk)
      · try simp only [WP.spec_ok]
        exact ⟨hc, fun k hk => Nat.le_succ_of_le (hb k hk)⟩
    step as ⟨cfreq1, hc1, hb1⟩
    step as ⟨i2, hi2⟩
    try simp only [WP.spec_ok]
    refine ⟨hi2, by scalar_tac, hc1, ?_⟩
    rw [hi2]
    exact hb1
  · try simp only [WP.spec_ok]
    exact hc

@[step]
theorem count_loop (syms : alloc.vec.Vec Usize) (i : Usize) (cfreq : alloc.vec.Vec Usize)
    (hsmall : syms.val.length ≤ 1024) (hi : i.val ≤ syms.val.length) (hc : cfreq.val.length = 19)
    (hb : ∀ k < 19, (cfreq.val[k]!).val ≤ i.val) :
    build_tables_loop2 i syms cfreq ⦃ r => r.val.length = 19 ⦄ := by
  unfold build_tables_loop2
  apply loop.spec_decr_nat (fun (i', _) => syms.val.length - i'.val)
    (fun (i', cfreq') => i'.val ≤ syms.val.length ∧ cfreq'.val.length = 19 ∧
      ∀ k < 19, (cfreq'.val[k]!).val ≤ i'.val)
  · rintro ⟨i', cfreq'⟩ ⟨hi', hc', hb'⟩
    refine WP.spec_mono (count_body syms i' cfreq' hsmall hi' hc' hb') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨j, cf⟩ := state
        exact ⟨⟨hr.2.1, hr.2.2.1, hr.2.2.2⟩, by change syms.val.length - j.val < syms.val.length - i'.val; omega⟩
  · exact ⟨hi, hc, hb⟩

/-! ### Trimming the code-length lengths -/

theorem trim_body (cl : Code) (hclen : Usize) (hcl : cl.lens.val.length = 19)
    (hh : 4 ≤ hclen.val ∧ hclen.val ≤ 19)
    (hz : ∀ k, hclen.val ≤ k → k < 19 → (cl.lens.val[clOrder[k]!]!).val = 0) :
    build_tables_loop3.body cl hclen ⦃ r =>
      match r with
      | .done (cl', h') => cl' = cl ∧ 4 ≤ h'.val ∧ h'.val ≤ 19 ∧
          ∀ k, h'.val ≤ k → k < 19 → (cl.lens.val[clOrder[k]!]!).val = 0
      | .cont h' => h'.val < hclen.val ∧ 4 ≤ h'.val ∧ h'.val ≤ 19 ∧
          ∀ k, h'.val ≤ k → k < 19 → (cl.lens.val[clOrder[k]!]!).val = 0 ⦄ := by
  unfold build_tables_loop3.body
  split
  · rename_i hgt
    have hgt' : 4 < hclen.val := by scalar_tac
    step as ⟨i, hi⟩
    have hi19 : i.val < 19 := by omega
    have hilen : i.val < CL_ORDER.val.length := by rw [cl_order_len]; exact hi19
    step as ⟨i1, hi1⟩
    have hi1v : i1.val = clOrder[i.val]! := by
      rw [hi1, ← getElem!_pos CL_ORDER.val i.val hilen]
      have := cl_order_table ⟨i.val, hi19⟩
      simpa using this
    have hi1l : i1.val < cl.lens.val.length := by rw [hcl, hi1v]; exact clOrder_lt i.val hi19
    step as ⟨i2, hi2⟩
    have hi2v : i2 = cl.lens.val[clOrder[i.val]!]! := by
      rw [hi2, ← getElem!_pos cl.lens.val i1.val hi1l, hi1v]
    split
    · rename_i hzero
      try simp only [WP.spec_ok]
      refine ⟨by omega, by omega, by omega, ?_⟩
      intro k hk1 hk2
      by_cases hki : k = i.val
      · rw [hki, ← hi2v, hzero]; rfl
      · exact hz k (by omega) hk2
    · try simp only [WP.spec_ok]
      exact ⟨by first | trivial | rfl, hh.1, hh.2, hz⟩
  · try simp only [WP.spec_ok]
    exact ⟨by first | trivial | rfl, hh.1, hh.2, hz⟩

@[step]
theorem trim_loop (cl : Code) (hclen : Usize) (hcl : cl.lens.val.length = 19)
    (hh : 4 ≤ hclen.val ∧ hclen.val ≤ 19)
    (hz : ∀ k, hclen.val ≤ k → k < 19 → (cl.lens.val[clOrder[k]!]!).val = 0) :
    build_tables_loop3 cl hclen ⦃ r => r.1 = cl ∧ 4 ≤ r.2.val ∧ r.2.val ≤ 19 ∧
      ∀ k, r.2.val ≤ k → k < 19 → (cl.lens.val[clOrder[k]!]!).val = 0 ⦄ := by
  unfold build_tables_loop3
  apply loop.spec_decr_nat (fun h' => h'.val)
    (fun h' => (4 ≤ h'.val ∧ h'.val ≤ 19) ∧ ∀ k, h'.val ≤ k → k < 19 → (cl.lens.val[clOrder[k]!]!).val = 0)
  · intro h' ⟨hh', hz'⟩
    refine WP.spec_mono (trim_body cl h' hcl hh' hz') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont h'' => exact ⟨⟨⟨hr.2.1, hr.2.2.1⟩, hr.2.2.2⟩, hr.1⟩
  · exact ⟨hh, hz⟩

theorem checks_spec (ok1 ok2 ok3 ok4 ok5 : Bool) (nlit ndist ncl : Usize) :
    checks ok1 ok2 ok3 ok4 ok5 nlit ndist ncl ⦃ r => r = true →
      ok1 = true ∧ ok2 = true ∧ ok3 = true ∧ ok4 = true ∧ ok5 = true ∧
      nlit.val ≤ 286 ∧ ndist.val ≤ 30 ∧ ncl.val = 19 ⦄ := by
  unfold checks
  split
  · split
    · split
      · split
        · split
          · split
            · split
              · rename_i h1 h2 h3 h4 h5 h6 h7
                simp only [WP.spec_ok]
                intro h
                have h8 : ncl = 19#usize := by simpa using h
                refine ⟨h1, h2, h3, h4, h5, by scalar_tac, by scalar_tac, ?_⟩
                rw [h8]
                rfl
              · simp
            · simp
          · simp
        · simp
      · simp
    · simp
  · simp

/-! ### Putting it together -/

theorem build_tables_spec (data : Aeneas.Std.Slice U8) (start : Usize) (ls ds : alloc.vec.Vec U16) (lsym dsym : alloc.vec.Vec U8) (lfreq dfreq lcode dcode : alloc.vec.Vec Usize)
    (stop : ℕ) (hr : Runs data.val stop start.val stop ls.val ds.val) (hd : stop ≤ data.val.length)
    (hsyms : Symbolize.Symbolized ls.val ds.val lsym.val dsym.val)
    (hsize : ls.val.length ≤ 1048576) (hlf : lfreq.val.length = 286) (hdf : dfreq.val.length = 30)
    (hlc : lcode.val.length = 286) (hdc : dcode.val.length = 30)
    (hsupp : Fused.Support data.val start.val ls.val ds.val lsym.val dsym.val lfreq.val dfreq.val) :
    build_tables data start ls ds lsym dsym lfreq dfreq lcode dcode ⦃ r =>
      r.2.2.2 = true → TablesOk data.val start.val ls.val ds.val lsym.val dsym.val r.1 ⦄ := by
  unfold build_tables
  dsimp only
  have hm1 := Canon.make_code_spec lcode 15#usize 257#usize (by rw [hlc]; omega) (by simp)
  step as ⟨lit, ok1, hl1, hl2, hl3, hl4, hl5, hl6⟩
  have hm2 := Canon.make_code_spec dcode 15#usize 1#usize (by rw [hdc]; omega) (by simp)
  step as ⟨dist, ok2, hd1, hd2, hd3, hd4, hd5, hd6⟩
  have hb := CostHistogram.cost_histograms_spec lfreq dfreq lit dist hlf hdf
  step as ⟨body, fixed, ok3, hbb, hchecked⟩
  have hbody (hgood : ok3 = true) :
      Body.Usable data.val start.val ls.val ds.val lsym.val dsym.val lit.lens.val dist.lens.val := by
    exact CostHistogram.usable data.val start.val ls.val ds.val lsym.val dsym.val lfreq.val dfreq.val
      lit.lens.val dist.lens.val hsyms hsupp (hchecked hgood).1 (hchecked hgood).2
  have hc0 := concat0_loop lit [] (alloc.vec.Vec.with_capacity U8 316#usize) 0#usize (by simp)
    (by simp [alloc.vec.Vec.with_capacity]) (by rw [hlc] at hl1; omega) (by simp)
  step with hc0 as ⟨v, v1, v2, all, hv, hv1, hv2, hall⟩
  have hall' : all.val = lit.lens.val := by simpa using hall
  have hc1 := concat1_loop dist lit.lens.val all 0#usize (by simp) (by simpa using hall')
    (by rw [hdc] at hd1; omega) (by rw [hlc] at hl1; omega)
  step as ⟨v3, v4, v5, all1, hv3, hv4, hv5, hall1⟩
  have hall1len : all1.val.length ≤ 316 := by
    rw [hall1, List.length_append]
    rw [hlc] at hl1
    rw [hdc] at hd1
    omega
  have hall1sym : ∀ k < all1.val.length, (all1.val[k]!).val ≤ 15 := by
    intro k hk
    rw [hall1] at hk ⊢
    rw [List.length_append] at hk
    by_cases hkl : k < lit.lens.val.length
    · rw [List.getElem!_append_left _ _ k hkl]
      exact hl5 k hkl
    · rw [List.getElem!_append_right _ _ k (by omega)]
      exact hd5 (k - lit.lens.val.length) (by omega)
  have hrle := Rle.rle_spec all1 (by omega) hall1sym
  step as ⟨syms, extras, hcov, hsl⟩
  step as ⟨cfreq, hcfreq⟩
  have hcl := count_loop syms 0#usize cfreq (by omega) (by simp) (by rw [hcfreq, List.length_replicate])
    (by
      intro k hk
      rw [hcfreq, List.getElem!_replicate] <;> scalar_tac)
  step as ⟨cfreq1, hcfreq1⟩
  have hm3 := Canon.make_code_spec cfreq1 7#usize 19#usize (by rw [hcfreq1]; omega) (by simp)
  step as ⟨cl, ok4, hc1', hc2, hc3, hc4, hc5, hc6⟩
  have hcl19 : cl.lens.val.length = 19 := by
    rw [hcfreq1] at hc1' hc2
    have := hc2 (by simp)
    try simp at this
    omega
  have ht := trim_loop cl 19#usize hcl19 (by simp) (fun k hk1 hk2 => by simp at hk1; omega)
  step as ⟨cl1, hclen, hcl1, hh4, hh19, hz⟩
  subst hcl1
  have hhc := Rle.header_cost_spec syms cl1 (by omega)
  step as ⟨header, ok5, hheader, hitems⟩
  have hchk := checks_spec ok1 ok2 ok3 ok4 ok5 (alloc.vec.Vec.len v) (alloc.vec.Vec.len v3) (alloc.vec.Vec.len cl1.lens)
  step as ⟨ok6, hok6⟩
  step as ⟨i3, hi3⟩
  step as ⟨i4, hi4⟩
  step as ⟨i5, hi5⟩
  have hcb : i5.val + body.val ≤ Usize.max := by
    have hu : 4294967295 ≤ Usize.max := by scalar_tac
    have hhc : hclen.val ≤ 19 := by scalar_tac
    omega
  step as ⟨cost, hcost⟩
  try simp only [WP.spec_ok]
  try dsimp only
  intro h6
  obtain ⟨h1, h2, h3, h4, h5, hn286, hn30, hn19⟩ := hok6 h6
  have hlitok := hl6 h1
  have hdistok := hd6 h2
  have hclok := hc6 h4
  have hlitEq : ({ lens := v, words := v1, rev := v2 } : Code) = lit := by rw [hv, hv1, hv2]
  have hdistEq : ({ lens := v3, words := v4, rev := v5 } : Code) = dist := by rw [hv3, hv4, hv5]
  rw [hlitEq, hdistEq]
  refine ⟨⟨by rw [hlc] at hl1; exact hl2 (by omega), by rw [hlc] at hl1; exact hl1⟩,
    ⟨by rw [hdc] at hd1; exact hd2 (by omega), by rw [hdc] at hd1; exact hd1⟩, hcl19,
    hlitok, hdistok, hclok, hbody h3, ?_, hitems h5, ⟨hh4, hh19⟩, hz, by show syms.val.length ≤ 316; omega⟩
  rw [← hall1]
  exact hcov

/-- The tables fitted to the frequencies, or when `smooth` to the smoothed ones if they price
the block lower: either way tables `build_tables` vouches for. -/
theorem fit_tables_spec (data : Aeneas.Std.Slice U8) (start : Usize) (ls ds : alloc.vec.Vec U16) (lsym dsym : alloc.vec.Vec U8) (lfreq dfreq : alloc.vec.Vec Usize) (smooth : Bool)
    (stop : ℕ) (hr : Runs data.val stop start.val stop ls.val ds.val) (hd : stop ≤ data.val.length)
    (hsyms : Symbolize.Symbolized ls.val ds.val lsym.val dsym.val)
    (hsize : ls.val.length ≤ 1048576) (hlf : lfreq.val.length = 286) (hdf : dfreq.val.length = 30)
    (hsupp : Fused.Support data.val start.val ls.val ds.val lsym.val dsym.val lfreq.val dfreq.val) :
    fit_tables data start ls ds lsym dsym lfreq dfreq smooth ⦃ r =>
      r.2.2.2 = true → TablesOk data.val start.val ls.val ds.val lsym.val dsym.val r.1 ⦄ := by
  unfold fit_tables
  have h0 := build_tables_spec data start ls ds lsym dsym lfreq dfreq lfreq dfreq stop hr hd hsyms
    hsize hlf hdf hlf hdf hsupp
  step as ⟨t0, c0, f0, ok0, h0'⟩
  split
  · step as ⟨lcode, hlc⟩
    step as ⟨dcode, hdc⟩
    have h1 := build_tables_spec data start ls ds lsym dsym lfreq dfreq lcode dcode stop hr hd hsyms
      hsize hlf hdf (by rw [hlc, hlf]) (by rw [hdc, hdf]) hsupp
    step as ⟨t1, c1, f1, ok1, h1'⟩
    split
    · split
      · split
        · try simp only [WP.spec_ok]
          exact h1'
        · try simp only [WP.spec_ok]
          exact h0'
      · try simp only [WP.spec_ok]
        exact h1'
    · try simp only [WP.spec_ok]
      exact h0'
  · try simp only [WP.spec_ok]
    exact h0'

end Gzip.Proofs.Build
