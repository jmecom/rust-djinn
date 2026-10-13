import Gzip.Proofs.DynBlock
import Gzip.Proofs.Passes

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Plans Gzip.Proofs.Runtime

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

/-! The block-merging helpers of the dense levels: the merge decision is a heuristic, so all
that is proved about the cost estimates is that they terminate and stay in range; the plan
concatenation and the decision's side conditions are what the outer loop needs. -/

namespace Gzip.Proofs.Merge

/-! ### Frequency sums -/

theorem add_hist_body (a b v : alloc.vec.Vec Usize) (i : Usize)
    (hi : i.val ≤ a.val.length) (hv : v.val.length = i.val) :
    add_hist_loop.body a b v i ⦃ r =>
      match r with
      | .done _ => True
      | .cont (v', i') => i'.val = i.val + 1 ∧ i'.val ≤ a.val.length ∧ v'.val.length = i'.val ⦄ := by
  have ha : a.val.length ≤ Usize.max := a.property
  unfold add_hist_loop.body
  dsimp only
  split
  · rename_i hlt
    have hlt' : i.val < a.val.length := by scalar_tac
    step as ⟨x, hx⟩
    have hySpec : (if i < alloc.vec.Vec.len b then alloc.vec.Vec.index_usize b i else ok 0#usize)
        ⦃ _ => True ⦄ := by
      split
      · rename_i hib
        have hib' : i.val < b.val.length := by scalar_tac
        step*
      · step*
    step as ⟨y, _⟩
    have hxc : (if x > 1073741824#usize then ok 1073741824#usize else ok x) ⦃ r => r.val ≤ 1073741824 ⦄ := by
      split
      · simp
      · simp only [WP.spec_ok]; scalar_tac
    step as ⟨xc, hxc'⟩
    have hyc : (if y > 1073741824#usize then ok 1073741824#usize else ok y) ⦃ r => r.val ≤ 1073741824 ⦄ := by
      split
      · simp
      · simp only [WP.spec_ok]; scalar_tac
    step as ⟨yc, hyc'⟩
    step as ⟨s, hs⟩
    have hspace : v.val.length < Usize.max := by omega
    step as ⟨v1, hv1⟩
    step as ⟨i3, hi3⟩
    try simp only [WP.spec_ok]
    refine ⟨hi3, by omega, ?_⟩
    rw [hv1, List.length_append, List.length_singleton, hv, hi3]
  · step*

theorem add_hist_loop_spec (a b v : alloc.vec.Vec Usize) (i : Usize)
    (hi : i.val ≤ a.val.length) (hv : v.val.length = i.val) :
    add_hist_loop a b v i ⦃ _ => True ⦄ := by
  unfold add_hist_loop
  apply loop.spec_decr_nat (fun (_, i') => a.val.length - i'.val)
    (fun (v', i') => i'.val ≤ a.val.length ∧ v'.val.length = i'.val)
  · rintro ⟨v', i'⟩ ⟨hi', hv'⟩
    refine WP.spec_mono (add_hist_body a b v' i' hi' hv') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨v'', i''⟩ := state
        obtain ⟨h1, h2, h3⟩ := hr
        exact ⟨⟨h2, h3⟩, by change a.val.length - i''.val < a.val.length - i'.val; omega⟩
  · exact ⟨hi, hv⟩

theorem add_hist_spec (a b : alloc.vec.Vec Usize) : add_hist a b ⦃ _ => True ⦄ := by
  unfold add_hist
  exact add_hist_loop_spec a b _ 0#usize (by simp) (by simp [alloc.vec.Vec.with_capacity])

/-! ### The weighted symbol bits -/

theorem extra_spec (dist : Bool) (s : Usize) :
    (if dist
      then
        if s < 30#usize
        then
          do
          let i3 ← Array.index_usize DIST_EXTRA s
          ok (UScalar.cast .Usize i3)
        else ok 0#usize
      else
        if s >= 257#usize
        then
          if s < 286#usize
          then
            do
            let i3 ← s - 257#usize
            let i4 ← Array.index_usize LENGTH_EXTRA i3
            ok (UScalar.cast .Usize i4)
          else ok 0#usize
        else ok 0#usize) ⦃ r => r.val ≤ 13 ⦄ := by
  split
  · split
    · rename_i hs
      have hs' : s.val < 30 := by scalar_tac
      have hde := Costs.distance_extra_bound s.val hs'
      have hdd : s.val < DIST_EXTRA.val.length := by simp [DIST_EXTRA, Array.make]; omega
      rw [getElem!_pos DIST_EXTRA.val s.val hdd] at hde
      step as ⟨i3, hi3⟩
      try simp only [WP.spec_ok]
      rw [UScalar.cast_val_eq, hi3]
      exact (Nat.mod_le _ _).trans hde
    · simp
  · split
    · split
      · rename_i h257 h286
        have h257' : 257 ≤ s.val := by scalar_tac
        have h286' : s.val < 286 := by scalar_tac
        step as ⟨i3, hi3⟩
        have hi3' : i3.val < 29 := by omega
        have hle := Costs.length_extra_bound i3.val hi3'
        have hll : i3.val < LENGTH_EXTRA.val.length := by simp [LENGTH_EXTRA, Array.make]; omega
        rw [getElem!_pos LENGTH_EXTRA.val i3.val hll] at hle
        step as ⟨i4, hi4⟩
        try simp only [WP.spec_ok]
        rw [UScalar.cast_val_eq, hi4]
        exact (Nat.mod_le _ _).trans (hle.trans (by norm_num))
      · simp
    · simp

theorem weighted_body (freq : alloc.vec.Vec Usize) (lens : alloc.vec.Vec U8) (dist : Bool)
    (total s : Usize) (ht : total.val ≤ 1073741824) :
    weighted_bits_loop.body freq lens dist total s ⦃ r =>
      match r with
      | .done t => t.val ≤ 1073741824
      | .cont (t, s') => t.val ≤ 1073741824 ∧ s'.val = s.val + 1 ∧ s.val < freq.val.length ⦄ := by
  unfold weighted_bits_loop.body
  dsimp only
  split
  · rename_i hlt
    have hlt' : s.val < freq.val.length := by scalar_tac
    split
    · rename_i hlt2
      have hlt2' : s.val < lens.val.length := by scalar_tac
      step as ⟨f, hf⟩
      have hinner : (if f > 0#usize
          then
            do
            let i2 ← alloc.vec.Vec.index_usize lens s
            let l ← lift (UScalar.cast .Usize i2)
            let code ← if l = 0#usize
                       then ok 15#usize
                       else ok l
            let extra ←
              if dist
              then
                if s < 30#usize
                then
                  do
                  let i3 ← Array.index_usize DIST_EXTRA s
                  ok (UScalar.cast .Usize i3)
                else ok 0#usize
              else
                if s >= 257#usize
                then
                  if s < 286#usize
                  then
                    do
                    let i3 ← s - 257#usize
                    let i4 ← Array.index_usize LENGTH_EXTRA i3
                    ok (UScalar.cast .Usize i4)
                  else ok 0#usize
                else ok 0#usize
            let fc ← if f > 1048576#usize
                     then ok 1048576#usize
                     else ok f
            let i3 ← code + extra
            let add ← fc * i3
            let sum ← total + add
            if sum > 1073741824#usize
            then ok 1073741824#usize
            else ok sum
          else ok total) ⦃ r => r.val ≤ 1073741824 ⦄ := by
        split
        · step as ⟨i2, hi2⟩
          step as ⟨l, hl⟩
          have hl' : l.val ≤ 255 := by
            rw [hl, UScalar.cast_val_eq]
            exact (Nat.mod_le _ _).trans (by have := i2.hBounds; scalar_tac)
          have hcode : (if l = 0#usize then ok 15#usize else ok l) ⦃ r => r.val ≤ 255 ⦄ := by
            split
            · simp
            · simp only [WP.spec_ok]; exact hl'
          step as ⟨code, hcode'⟩
          have hextra := extra_spec dist s
          step as ⟨extra, hextra'⟩
          have hfc : (if f > 1048576#usize then ok 1048576#usize else ok f) ⦃ r => r.val ≤ 1048576 ⦄ := by
            split
            · simp
            · simp only [WP.spec_ok]; scalar_tac
          step as ⟨fc, hfc'⟩
          step as ⟨i3, hi3⟩
          have hprod : fc.val * i3.val ≤ 1048576 * 268 := Nat.mul_le_mul hfc' (by omega)
          step as ⟨add, hadd⟩
          step as ⟨sum, hsum⟩
          split
          · simp
          · simp only [WP.spec_ok]; scalar_tac
        · simp only [WP.spec_ok]; exact ht
      step as ⟨total1, htotal1⟩
      step as ⟨s1, hs1⟩
      try simp only [WP.spec_ok]
      exact ⟨htotal1, hs1, hlt'⟩
    · try simp only [WP.spec_ok]
      exact ht
  · try simp only [WP.spec_ok]
    exact ht

theorem weighted_loop (freq : alloc.vec.Vec Usize) (lens : alloc.vec.Vec U8) (dist : Bool)
    (total s : Usize) (ht : total.val ≤ 1073741824) :
    weighted_bits_loop freq lens dist total s ⦃ r => r.val ≤ 1073741824 ⦄ := by
  unfold weighted_bits_loop
  apply loop.spec_decr_nat (fun (_, s') => freq.val.length - s'.val)
    (fun (t, _) => t.val ≤ 1073741824)
  · rintro ⟨t, s'⟩ ht'
    refine WP.spec_mono (weighted_body freq lens dist t s' ht') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨t', s''⟩ := state
        obtain ⟨h1, h2, h3⟩ := hr
        exact ⟨h1, by change freq.val.length - s''.val < freq.val.length - s'.val; omega⟩
  · exact ht

theorem weighted_bits_spec (freq : alloc.vec.Vec Usize) (lens : alloc.vec.Vec U8) (dist : Bool) :
    weighted_bits freq lens dist ⦃ r => r.val ≤ 1073741824 ⦄ := by
  unfold weighted_bits
  exact weighted_loop freq lens dist 0#usize 0#usize (by simp)

/-! ### The estimated cost of a block from its frequencies -/

theorem concat0_body (c : alloc.vec.Vec U8) (pre : List U8) (all : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ c.val.length) (hall : all.val = pre ++ c.val.take i.val)
    (hsmall : c.val.length ≤ 1024) (hpre : pre.length ≤ 1024) :
    hist_cost_loop0.body c all i ⦃ r =>
      match r with
      | .done all' => all'.val = pre ++ c.val
      | .cont (all', i') => i'.val = i.val + 1 ∧ i'.val ≤ c.val.length ∧
          all'.val = pre ++ c.val.take i'.val ⦄ := by
  unfold hist_cost_loop0.body
  dsimp only
  split
  · rename_i hlt
    have hlt' : i.val < c.val.length := by scalar_tac
    step as ⟨i2, hi2⟩
    have hspace : all.val.length < Usize.max := by
      rw [hall, List.length_append, List.length_take]; scalar_tac
    step as ⟨all1, hall1⟩
    step as ⟨i3, hi3⟩
    try simp only [WP.spec_ok]
    refine ⟨hi3, by scalar_tac, ?_⟩
    rw [hall1, hall, hi3, List.take_succ_eq_append_getElem hlt', hi2, List.append_assoc]
  · rename_i hge
    have he : i.val = c.val.length := by scalar_tac
    try simp only [WP.spec_ok]
    rw [hall, he, List.take_length]

theorem concat0_loop (c : alloc.vec.Vec U8) (pre : List U8) (all : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ c.val.length) (hall : all.val = pre ++ c.val.take i.val)
    (hsmall : c.val.length ≤ 1024) (hpre : pre.length ≤ 1024) :
    hist_cost_loop0 c all i ⦃ r => r.val = pre ++ c.val ⦄ := by
  unfold hist_cost_loop0
  apply loop.spec_decr_nat (fun (_, i') => c.val.length - i'.val)
    (fun (all', i') => i'.val ≤ c.val.length ∧ all'.val = pre ++ c.val.take i'.val)
  · rintro ⟨all', i'⟩ ⟨hi', hall'⟩
    refine WP.spec_mono (concat0_body c pre all' i' hi' hall' hsmall hpre) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨a, j⟩ := state
        exact ⟨⟨hr.2.1, hr.2.2⟩, by change c.val.length - j.val < c.val.length - i'.val; omega⟩
  · exact ⟨hi, hall⟩

theorem concat1_body (c : alloc.vec.Vec U8) (pre : List U8) (all : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ c.val.length) (hall : all.val = pre ++ c.val.take i.val)
    (hsmall : c.val.length ≤ 1024) (hpre : pre.length ≤ 1024) :
    hist_cost_loop1.body c all i ⦃ r =>
      match r with
      | .done all' => all'.val = pre ++ c.val
      | .cont (all', i') => i'.val = i.val + 1 ∧ i'.val ≤ c.val.length ∧
          all'.val = pre ++ c.val.take i'.val ⦄ := by
  unfold hist_cost_loop1.body
  dsimp only
  split
  · rename_i hlt
    have hlt' : i.val < c.val.length := by scalar_tac
    step as ⟨i2, hi2⟩
    have hspace : all.val.length < Usize.max := by
      rw [hall, List.length_append, List.length_take]; scalar_tac
    step as ⟨all1, hall1⟩
    step as ⟨i3, hi3⟩
    try simp only [WP.spec_ok]
    refine ⟨hi3, by scalar_tac, ?_⟩
    rw [hall1, hall, hi3, List.take_succ_eq_append_getElem hlt', hi2, List.append_assoc]
  · rename_i hge
    have he : i.val = c.val.length := by scalar_tac
    try simp only [WP.spec_ok]
    rw [hall, he, List.take_length]

theorem concat1_loop (c : alloc.vec.Vec U8) (pre : List U8) (all : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ c.val.length) (hall : all.val = pre ++ c.val.take i.val)
    (hsmall : c.val.length ≤ 1024) (hpre : pre.length ≤ 1024) :
    hist_cost_loop1 c all i ⦃ r => r.val = pre ++ c.val ⦄ := by
  unfold hist_cost_loop1
  apply loop.spec_decr_nat (fun (_, i') => c.val.length - i'.val)
    (fun (all', i') => i'.val ≤ c.val.length ∧ all'.val = pre ++ c.val.take i'.val)
  · rintro ⟨all', i'⟩ ⟨hi', hall'⟩
    refine WP.spec_mono (concat1_body c pre all' i' hi' hall' hsmall hpre) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨a, j⟩ := state
        exact ⟨⟨hr.2.1, hr.2.2⟩, by change c.val.length - j.val < c.val.length - i'.val; omega⟩
  · exact ⟨hi, hall⟩

theorem count_body (syms : alloc.vec.Vec Usize) (i : Usize) (cfreq : alloc.vec.Vec Usize)
    (hsmall : syms.val.length ≤ 1024) (hi : i.val ≤ syms.val.length) (hc : cfreq.val.length = 19)
    (hb : ∀ k < 19, (cfreq.val[k]!).val ≤ i.val) :
    hist_cost_loop2.body syms i cfreq ⦃ r =>
      match r with
      | .done cfreq' => cfreq'.val.length = 19
      | .cont (i', cfreq') => i'.val = i.val + 1 ∧ i'.val ≤ syms.val.length ∧ cfreq'.val.length = 19 ∧
          ∀ k < 19, (cfreq'.val[k]!).val ≤ i'.val ⦄ := by
  unfold hist_cost_loop2.body
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

theorem count_loop (syms : alloc.vec.Vec Usize) (i : Usize) (cfreq : alloc.vec.Vec Usize)
    (hsmall : syms.val.length ≤ 1024) (hi : i.val ≤ syms.val.length) (hc : cfreq.val.length = 19)
    (hb : ∀ k < 19, (cfreq.val[k]!).val ≤ i.val) :
    hist_cost_loop2 i syms cfreq ⦃ r => r.val.length = 19 ⦄ := by
  unfold hist_cost_loop2
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

theorem hist_cost_spec (lfreq dfreq : alloc.vec.Vec Usize) : hist_cost lfreq dfreq ⦃ r => r.val ≤ 1073741824 ⦄ := by
  unfold hist_cost
  dsimp only
  split
  · rename_i h286
    have hl : lfreq.val.length = 286 := by
      have := (UScalar.eq_equiv _ _).mp h286
      simpa [alloc.vec.Vec.len_val, alloc.vec.Vec.length] using this
    split
    · rename_i h30
      have hdl : dfreq.val.length = 30 := by
        have := (UScalar.eq_equiv _ _).mp h30
        simpa [alloc.vec.Vec.len_val, alloc.vec.Vec.length] using this
      have hcl := Huff.code_lengths_spec lfreq 15#usize (by omega) (by simp)
      step as ⟨llens, hllen, hlb⟩
      have hcd := Huff.code_lengths_spec dfreq 15#usize (by omega) (by simp)
      step as ⟨dlens, hdlen, hdb⟩
      have hw1 := weighted_bits_spec lfreq llens false
      step as ⟨i2, hi2⟩
      have hw2 := weighted_bits_spec dfreq dlens true
      step as ⟨i3, hi3⟩
      step as ⟨body, hbody⟩
      have hc0 := concat0_loop llens [] (alloc.vec.Vec.with_capacity U8 316#usize) 0#usize (by simp)
        (by simp [alloc.vec.Vec.with_capacity]) (by omega) (by simp)
      step with hc0 as ⟨all, hall⟩
      have hall' : all.val = llens.val := by simpa using hall
      have hc1 := concat1_loop dlens llens.val all 0#usize (by simp) (by simpa using hall') (by omega) (by omega)
      step as ⟨all1, hall1⟩
      have hall1len : all1.val.length ≤ 1024 := by
        rw [hall1, List.length_append]
        omega
      have hall1sym : ∀ k < all1.val.length, (all1.val[k]!).val ≤ 15 := by
        intro k hk
        rw [hall1] at hk ⊢
        rw [List.length_append] at hk
        by_cases hkl : k < llens.val.length
        · rw [List.getElem!_append_left _ _ k hkl]
          have := hlb k hkl
          simpa using this
        · rw [List.getElem!_append_right _ _ k (by omega)]
          have := hdb (k - llens.val.length) (by omega)
          simpa using this
      have hrle := Rle.rle_spec all1 hall1len hall1sym
      step as ⟨syms, extras, hcov, hsl⟩
      step as ⟨cfreq, hcfreq⟩
      have hcnt := count_loop syms 0#usize cfreq (by omega) (by simp) (by rw [hcfreq, List.length_replicate])
        (by
          intro k hk
          rw [hcfreq, List.getElem!_replicate] <;> scalar_tac)
      step as ⟨cfreq1, hcfreq1⟩
      have hm3 := Huff.code_lengths_spec cfreq1 7#usize (by rw [hcfreq1]; omega) (by simp)
      step as ⟨clens, _, _⟩
      have hhc := Rle.header_cost_spec syms
        ({ lens := clens, words := alloc.vec.Vec.new Usize, rev := alloc.vec.Vec.new U32 } : Code) (by omega)
      step as ⟨header, ok5, hheader, _⟩
      step as ⟨i4, hi4⟩
      step as ⟨total, htotal⟩
      split
      · simp
      · simp only [WP.spec_ok]; scalar_tac
    · simp
  · simp

/-! ### The costs of a chunk and of a merge -/

theorem plan_cost_spec (data : Aeneas.Std.Slice U8) (start stop : Usize) (plan : Plan)
    (hr : Runs data.val stop.val start.val stop.val plan.lengths.val plan.distances.val)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length) (hsize : stop.val - start.val ≤ 32768) :
    plan_cost data start stop plan ⦃ _ => True ⦄ := by
  unfold plan_cost
  have hll := runs_lengths hr
  have hsymb := PricingHistogram.correct data start plan.lengths plan.distances stop.val hr hd (by omega)
  step as ⟨lfreq, dfreq, hlf, hdf⟩
  have hhc := hist_cost_spec lfreq dfreq
  step as ⟨dyn, _⟩
  step as ⟨span, hspan⟩
  split
  · rename_i hsp
    have hsp' : span.val ≤ 32768 := by scalar_tac
    step as ⟨i, hi⟩
    step as ⟨sb, hsb⟩
    split
    · simp
    · simp
  · simp only [bind_ok]
    split
    · simp
    · simp

/-- The chunk's parse comes back as the block writer takes it (at the merging levels with the
plan's frequencies counted afresh, so no longer `fused`). -/
theorem costs_at_spec (data : Aeneas.Std.Slice U8) (start stop : Usize) (level : U8) (parsed : Parsed)
    (hpr : Counting.ParsedOk data.val start.val stop.val parsed)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length) (hsize : stop.val - start.val ≤ 32768) :
    costs_at data start stop level parsed ⦃ r => Counting.ParsedOk data.val start.val stop.val r.1 ⦄ := by
  unfold costs_at
  split
  · have hpc := plan_cost_spec data start stop parsed.plan hpr.1 hs hd hsize
    step as ⟨lfreq, dfreq, cost, _⟩
    try simp only [WP.spec_ok]
    exact ⟨hpr.1, fun hf => by simp at hf⟩
  · simp only [WP.spec_ok]
    exact hpr

theorem merged_costs_spec (level : U8) (lf0 df0 lf1 df1 : alloc.vec.Vec Usize) :
    merged_costs level lf0 df0 lf1 df1 ⦃ _ => True ⦄ := by
  unfold merged_costs
  split
  · have h1 := add_hist_spec lf0 lf1
    step as ⟨lf2, _⟩
    have h2 := add_hist_spec df0 df1
    step as ⟨df2, _⟩
    have h3 := hist_cost_spec lf2 df2
    step as ⟨c2, _⟩
    all_goals simp
  · simp

theorem merge_decision_spec (level : U8) (pstart start stop c0 c1 c2 : Usize)
    (hps : pstart.val ≤ stop.val) :
    merge_decision level pstart start stop c0 c1 c2 ⦃ r => r = true →
      9 ≤ level.val ∧ 0 < start.val ∧ stop.val - pstart.val ≤ 1048576 ⦄ := by
  unfold merge_decision
  have ha : (if c0 > 1073741824#usize then ok 1073741824#usize else ok c0) ⦃ r => r.val ≤ 1073741824 ⦄ := by
    split
    · simp
    · simp only [WP.spec_ok]; scalar_tac
  step as ⟨a, ha'⟩
  have hb : (if c1 > 1073741824#usize then ok 1073741824#usize else ok c1) ⦃ r => r.val ≤ 1073741824 ⦄ := by
    split
    · simp
    · simp only [WP.spec_ok]; scalar_tac
  step as ⟨b, hb'⟩
  split
  · rename_i h9
    split
    · rename_i h0
      step as ⟨i, hi⟩
      split
      · rename_i hi1
        step as ⟨i1, hi1'⟩
        try simp only [WP.spec_ok]
        intro _
        exact ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
      · simp
    · simp
  · simp

/-! ### Concatenating plans -/

@[step] theorem extend_lengths (v : alloc.vec.Vec U16) (s : Aeneas.Std.Slice U16)
    (hspace : v.val.length + s.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU16 v s ⦃ r =>
      r.val = v.val ++ s.val ⦄ := by
  have hclone : Slice.clone core.clone.CloneU16.clone s = ok s := by
    have hc := Slice.clone_spec (clone := core.clone.CloneU16.clone) (s := s)
      (by intro x hx; rfl)
    rw [WP.spec_equiv_exists] at hc
    obtain ⟨s1, he, hsame⟩ := hc
    simpa only [← hsame] using he
  unfold alloc.vec.Vec.extend_from_slice
  simp only [alloc.vec.Vec.length, Slice.length] at *
  rw [dif_pos hspace]
  split
  · rename_i s1 he
    have hs : s1 = s := by
      rw [hclone] at he
      cases he
      rfl
    subst s1
    step*
  · rename_i eff k he
    rw [hclone] at he
    cases he
  · rename_i he
    rw [hclone] at he
    cases he

theorem append_plan_spec (plan more : Plan)
    (hlen : more.lengths.val.length = more.distances.val.length)
    (hs1 : plan.lengths.val.length + more.lengths.val.length ≤ 2097152)
    (hs2 : plan.distances.val.length + more.lengths.val.length ≤ 2097152) :
    append_plan plan more ⦃ r =>
      r.lengths.val = plan.lengths.val ++ more.lengths.val ∧
      r.distances.val = plan.distances.val ++ more.distances.val ⦄ := by
  have hspace1 : plan.lengths.val.length + more.lengths.val.length ≤ Usize.max := by scalar_tac
  have hspace2 : plan.distances.val.length + more.distances.val.length ≤ Usize.max := by
    rw [← hlen]
    scalar_tac
  have he1 := extend_lengths plan.lengths (alloc.vec.Vec.deref more.lengths)
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using hspace1)
  have he2 := extend_lengths plan.distances (alloc.vec.Vec.deref more.distances)
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using hspace2)
  unfold append_plan
  step as ⟨ls, hls⟩
  step as ⟨ds, hds⟩
  try simp only [WP.spec_ok]
  exact ⟨by simpa only [alloc.vec.Vec.deref, Slice.from_val] using hls,
    by simpa only [alloc.vec.Vec.deref, Slice.from_val] using hds⟩

/-! ### Writing a chunk at once -/

theorem flush_now_spec (level : U8) (stop len pstart start : Usize) :
    flush_now level stop len pstart start ⦃ r => r = true →
      level.val < 9 ∧ stop.val < len.val ∧ pstart.val = start.val ⦄ := by
  unfold flush_now
  split
  · rename_i h9
    split
    · rename_i hlt
      simp only [WP.spec_ok, decide_eq_true_eq]
      intro h
      exact ⟨by scalar_tac, by scalar_tac, by rw [h]⟩
    · simp
  · simp

/-! ### The pending block -/

/-- The block not yet written: its plan covers the data from its start to `start` (nothing when
its start is `start`); it starts on a chunk boundary and spans at most a million bytes (the
encoding proofs' bound). -/
structure PendingOk (data : List U8) (pd : Pending) (start : ℕ) : Prop where
  le : pd.start.val ≤ start
  aligned : pd.start.val % 32768 = 0
  span : start - pd.start.val ≤ 1048576
  parsed : Counting.ParsedOk data pd.start.val start pd.parsed

/-- An empty pending block, starting where the next chunk starts. -/
theorem no_pending_spec (start : Usize) :
    no_pending start ⦃ r => r.start = start ∧ r.parsed.plan.lengths.val = [] ∧
      r.parsed.plan.distances.val = [] ∧ r.parsed.fused = false ⦄ := by
  unfold no_pending
  step as ⟨p, hpp, hpf⟩
  have hpost : ({ start := start, parsed := p, cost := 0#usize } : Pending).start = start ∧
      p.plan.lengths.val = [] ∧ p.plan.distances.val = [] ∧ p.fused = false :=
    ⟨rfl, by rw [hpp]; rfl, by rw [hpp]; rfl, hpf⟩
  simpa only [WP.spec_ok, true_and] using hpost

/-- A parse with an empty plan covers an empty span. -/
theorem parsedOk_empty (data : List U8) (s : ℕ) (pr : Parsed)
    (hl : pr.plan.lengths.val = []) (hd : pr.plan.distances.val = []) (hf : pr.fused = false) :
    Counting.ParsedOk data s s pr := by
  refine ⟨?_, fun hf' => by rw [hf] at hf'; cases hf'⟩
  rw [hl, hd]
  exact Runs.finish s

end Gzip.Proofs.Merge
