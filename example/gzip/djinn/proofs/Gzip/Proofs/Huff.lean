import Gzip.Proofs.Chains

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Chains

set_option maxHeartbeats 2000000

namespace Gzip.Proofs.Huff

/-! Code lengths from frequencies: only termination, bounds and the lengths of the results
    matter, since every property the decoder needs is checked afterwards. -/

def Bounded (v : List Usize) (bound : ℕ) : Prop := ∀ k < v.length, (v[k]!).val ≤ bound

theorem bounded_set {v : List Usize} {bound : ℕ} (h : Bounded v bound) (i : ℕ) (x : Usize)
    (hx : x.val ≤ bound) : Bounded (v.set i x) bound := by
  intro k hk
  have hk' : k < v.length := by simpa using hk
  rw [Djinn.Vocab.getElem!_set v i k x hk']
  split
  · exact hx
  · exact h k hk'

theorem weight_of_spec (weight : alloc.vec.Vec Usize) (node : Usize) (bound : ℕ)
    (hb : Bounded weight.val bound) :
    weight_of weight node ⦃ w => w.val ≤ bound ⦄ := by
  unfold weight_of
  dsimp only
  split
  · rename_i hlt
    have hlt' : node.val < weight.val.length := by scalar_tac
    step as ⟨w, hw⟩
    rw [hw, ← getElem!_pos weight.val node.val hlt']
    exact hb node.val hlt'
  · simp

theorem weight_of_total (weight : alloc.vec.Vec Usize) (node : Usize) :
    weight_of weight node ⦃ _ => True ⦄ := by
  unfold weight_of
  dsimp only
  split
  · rename_i hlt
    have hlt' : node.val < weight.val.length := by scalar_tac
    step as ⟨w, hw⟩
    try trivial
  · simp

theorem sort_body (freq : alloc.vec.Vec Usize) (i : Usize) (order : alloc.vec.Vec Usize)
    (j : Usize) (moving : Bool) (hi : i.val < freq.val.length) (hj : j.val < order.val.length) :
    tree_depths_loop0_loop0.body freq i order j moving ⦃ r =>
      match r with
      | .done (order', j') => order'.val.length = order.val.length ∧ j'.val < order'.val.length
      | .cont (order', j', moving') => order'.val.length = order.val.length ∧ j'.val < order'.val.length ∧
          (2 * j'.val + (if moving' then 1 else 0) < 2 * j.val + (if moving then 1 else 0)) ⦄ := by
  unfold tree_depths_loop0_loop0.body
  split
  · rename_i hm
    split
    · rename_i hjpos
      have hjpos' : 0 < j.val := by scalar_tac
      step as ⟨i1, hi1⟩
      step as ⟨prev, hprev⟩
      have hw2 := weight_of_total freq prev
      step as ⟨i2, _⟩
      step as ⟨i3, hi3⟩
      split
      · step as ⟨x, back, hx, hback⟩
        simp only [hback, alloc.vec.Vec.set_val_eq, List.length_set, WP.spec_ok, hm, if_true]
        refine ⟨trivial, by omega, by omega⟩
      · try simp only [WP.spec_ok, hm]
        refine ⟨trivial, hj, by simp⟩
    · try simp only [WP.spec_ok]
      exact ⟨trivial, hj⟩
  · try simp only [WP.spec_ok]
    exact ⟨trivial, hj⟩

@[step]
theorem sort_loop (freq : alloc.vec.Vec Usize) (i : Usize) (order : alloc.vec.Vec Usize)
    (j : Usize) (moving : Bool) (hi : i.val < freq.val.length) (hj : j.val < order.val.length) :
    tree_depths_loop0_loop0 freq order i j moving ⦃ r =>
      r.1.val.length = order.val.length ∧ r.2.val < r.1.val.length ⦄ := by
  unfold tree_depths_loop0_loop0
  apply loop.spec_decr_nat (fun (_, j', m) => 2 * j'.val + (if m then 1 else 0))
    (fun (order', j', _) => order'.val.length = order.val.length ∧ j'.val < order'.val.length)
  · rintro ⟨order', j', m⟩ ⟨hl, hj'⟩
    refine WP.spec_mono (sort_body freq i order' j' m hi hj') ?_
    intro r hr
    cases r with
    | done state => exact ⟨hr.1.trans hl, hr.2⟩
    | cont state =>
        obtain ⟨order'', j'', m'⟩ := state
        exact ⟨⟨hr.1.trans hl, hr.2.1⟩, hr.2.2⟩
  · exact ⟨rfl, hj⟩

theorem order_body (freq : alloc.vec.Vec Usize) (n : Usize) (order : alloc.vec.Vec Usize) (i : Usize)
    (hn : n.val = freq.val.length) (hsmall : n.val ≤ 1024)
    (hi : i.val ≤ n.val) (ho : order.val.length ≤ i.val) :
    tree_depths_loop0.body freq n order i ⦃ r =>
      match r with
      | .done order' => order'.val.length ≤ n.val
      | .cont (order', i') => i'.val = i.val + 1 ∧ i'.val ≤ n.val ∧ order'.val.length ≤ i'.val ⦄ := by
  unfold tree_depths_loop0.body
  split
  · rename_i hlt
    have hlt' : i.val < freq.val.length := by scalar_tac
    step as ⟨i1, hi1⟩
    split
    · have hspace : order.val.length < Usize.max := by scalar_tac
      step as ⟨order1, horder1⟩
      have hlen1 : order1.val.length = order.val.length + 1 := by
        rw [horder1, List.length_append, List.length_singleton]
      step as ⟨j, hj⟩
      have hjlt : j.val < order1.val.length := by
        simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length] at hj
        rw [hj, hlen1]
        omega
      step as ⟨order2, j1, hlen2, hj1⟩
      step as ⟨x, back, hx, hback⟩
      step as ⟨i3, hi3⟩
      simp only [hback, alloc.vec.Vec.set_val_eq, List.length_set, WP.spec_ok]
      refine ⟨hi3, by scalar_tac, ?_⟩
      rw [hlen2, hlen1, hi3]
      omega
    · step as ⟨i2, hi2⟩
      try simp only [WP.spec_ok]
      exact ⟨hi2, by scalar_tac, by omega⟩
  · try simp only [WP.spec_ok]
    have : i.val = n.val := by scalar_tac
    omega

@[step]
theorem order_loop (freq : alloc.vec.Vec Usize) (n : Usize) (order : alloc.vec.Vec Usize) (i : Usize)
    (hn : n.val = freq.val.length) (hsmall : n.val ≤ 1024)
    (hi : i.val ≤ n.val) (ho : order.val.length ≤ i.val) :
    tree_depths_loop0 freq n order i ⦃ r => r.val.length ≤ n.val ⦄ := by
  unfold tree_depths_loop0
  apply loop.spec_decr_nat (fun (_, i') => n.val - i'.val)
    (fun (order', i') => i'.val ≤ n.val ∧ order'.val.length ≤ i'.val)
  · rintro ⟨order', i'⟩ ⟨hi', ho'⟩
    refine WP.spec_mono (order_body freq n order' i' hn hsmall hi' ho') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨order'', i''⟩ := state
        exact ⟨⟨hr.2.1, hr.2.2⟩, by change n.val - i''.val < n.val - i'.val; omega⟩
  · exact ⟨hi, ho⟩

theorem weights_body (freq : alloc.vec.Vec Usize) (n i : Usize) (weight : alloc.vec.Vec Usize)
    (hn : n.val = freq.val.length) (hi : i.val ≤ n.val) (hw : n.val ≤ weight.val.length)
    (hb : Bounded weight.val 1073741824) :
    tree_depths_loop1.body freq n i weight ⦃ r =>
      match r with
      | .done weight' => weight'.val.length = weight.val.length ∧ Bounded weight'.val 1073741824
      | .cont (i', weight') => i'.val = i.val + 1 ∧ i'.val ≤ n.val ∧
          weight'.val.length = weight.val.length ∧ Bounded weight'.val 1073741824 ⦄ := by
  unfold tree_depths_loop1.body
  split
  · rename_i hlt
    have hlt' : i.val < freq.val.length := by scalar_tac
    step as ⟨w, hw0⟩
    have hw1spec : (if w > 1073741824#usize then ok 1073741824#usize else ok w) ⦃ w1 =>
        w1.val ≤ 1073741824 ⦄ := by
      split <;> step* <;> scalar_tac
    step as ⟨w1, hw1⟩
    step as ⟨x, back, hx, hback⟩
    step as ⟨i1, hi1⟩
    simp only [hback, alloc.vec.Vec.set_val_eq, List.length_set, WP.spec_ok]
    exact ⟨hi1, by scalar_tac, trivial, bounded_set hb _ _ hw1⟩
  · try simp only [WP.spec_ok]
    exact ⟨trivial, hb⟩

@[step]
theorem weights_loop (freq : alloc.vec.Vec Usize) (n i : Usize) (weight : alloc.vec.Vec Usize)
    (hn : n.val = freq.val.length) (hi : i.val ≤ n.val) (hw : n.val ≤ weight.val.length)
    (hb : Bounded weight.val 1073741824) :
    tree_depths_loop1 freq n i weight ⦃ r =>
      r.val.length = weight.val.length ∧ Bounded r.val 1073741824 ⦄ := by
  unfold tree_depths_loop1
  apply loop.spec_decr_nat (fun (i', _) => n.val - i'.val)
    (fun (i', weight') => i'.val ≤ n.val ∧ weight'.val.length = weight.val.length ∧
      Bounded weight'.val 1073741824)
  · rintro ⟨i', weight'⟩ ⟨hi', hl', hb'⟩
    refine WP.spec_mono (weights_body freq n i' weight' hn hi' (by omega) hb') ?_
    intro r hr
    cases r with
    | done state => exact ⟨hr.1.trans hl', hr.2⟩
    | cont state =>
        obtain ⟨i'', weight''⟩ := state
        exact ⟨⟨hr.2.1, hr.2.2.1.trans hl', hr.2.2.2⟩, by change n.val - i''.val < n.val - i'.val; omega⟩
  · exact ⟨hi, rfl, hb⟩

structure MergeState (n used : ℕ) (order weight left right : alloc.vec.Vec Usize)
    (lq iq created remaining : Usize) : Prop where
  small : n ≤ 1024 ∧ used ≤ 1024
  orderLen : order.val.length = used
  weightLen : weight.val.length = n + used
  leftLen : left.val.length = used
  rightLen : right.val.length = used
  bounded : Bounded weight.val 1073741824
  lqLe : lq.val ≤ used
  iqLe : iq.val ≤ created.val
  createdLe : created.val ≤ used
  remainingEq : remaining.val = (used - lq.val) + (created.val - iq.val)

theorem pick_spec (n used : ℕ) (order weight : alloc.vec.Vec Usize) (nn usedn lq iq created : Usize)
    (hnn : nn.val = n) (husedn : usedn.val = used) (hsmall : n ≤ 1024 ∧ used ≤ 1024)
    (hol : order.val.length = used) (hlq : lq.val ≤ used) (hiq : iq.val ≤ created.val)
    (hcr : created.val ≤ used) (havail : 1 ≤ (used - lq.val) + (created.val - iq.val)) :
    (if lq < usedn then
      if iq >= created then do
        let a1 ← alloc.vec.Vec.index_usize order lq
        let lq2 ← lq + 1#usize
        ok (lq2, iq, a1)
      else do
        let i ← alloc.vec.Vec.index_usize order lq
        let i1 ← weight_of weight i
        let i2 ← nn + iq
        let i3 ← weight_of weight i2
        if i1 <= i3 then do let lq2 ← lq + 1#usize; ok (lq2, iq, i)
        else do let iq2 ← iq + 1#usize; ok (lq, iq2, i2)
    else do
      let a1 ← nn + iq
      let iq2 ← iq + 1#usize
      ok (lq, iq2, a1)) ⦃ r =>
      r.1.val ≤ used ∧ r.2.1.val ≤ created.val ∧
      (used - r.1.val) + (created.val - r.2.1.val) + 1 = (used - lq.val) + (created.val - iq.val) ⦄ := by
  split
  · rename_i hlqlt
    have hlqlt' : lq.val < used := by scalar_tac
    have hlqo : lq.val < order.val.length := by rw [hol]; exact hlqlt'
    split
    · step as ⟨a1, ha1⟩
      step as ⟨lq2, hlq2⟩
      try simp only [WP.spec_ok]
      omega
    · rename_i hiqlt
      have hiqlt' : iq.val < created.val := by scalar_tac
      step as ⟨i, hi⟩
      have hwi := weight_of_total weight i
      step as ⟨i1, _⟩
      step as ⟨i2, hi2⟩
      have hwi2 := weight_of_total weight i2
      step as ⟨i3, _⟩
      split
      · step as ⟨lq2, hlq2⟩
        try simp only [WP.spec_ok]
        omega
      · step as ⟨iq2, hiq2⟩
        try simp only [WP.spec_ok]
        omega
  · rename_i hlqge
    have hlqge' : used ≤ lq.val := by scalar_tac
    have hiqlt : iq.val < created.val := by omega
    step as ⟨a1, ha1⟩
    step as ⟨iq2, hiq2⟩
    try simp only [WP.spec_ok]
    omega

theorem merge_body (n used : ℕ) (order weight left right : alloc.vec.Vec Usize)
    (nn usedn lq iq created remaining : Usize) (hnn : nn.val = n) (husedn : usedn.val = used)
    (h : MergeState n used order weight left right lq iq created remaining) :
    tree_depths_loop2.body nn order usedn weight left right lq iq created remaining ⦃ r =>
      match r with
      | .done (left', right', created') => left'.val.length = used ∧ right'.val.length = used ∧
          created'.val ≤ used
      | .cont (weight', left', right', lq', iq', created', remaining') =>
          MergeState n used order weight' left' right' lq' iq' created' remaining' ∧
          remaining'.val < remaining.val ⦄ := by
  obtain ⟨hsmall, hol, hwl, hll, hrl, hb, hlq, hiq, hcr, hrem⟩ := h
  unfold tree_depths_loop2.body
  split
  · rename_i hrem2
    have hrem2' : 2 ≤ remaining.val := by scalar_tac
    split
    · rename_i hclt
      have hclt' : created.val < used := by scalar_tac
      have hpick1 := pick_spec n used order weight nn usedn lq iq created hnn husedn hsmall hol hlq hiq hcr (by omega)
      step as ⟨lq1, iq1, a, hlq1, hiq1, hcount1⟩
      have hpick2 := pick_spec n used order weight nn usedn lq1 iq1 created hnn husedn hsmall hol hlq1 hiq1 hcr (by omega)
      step as ⟨lq2, iq2, b, hlq2, hiq2, hcount2⟩
      have hwa := weight_of_spec weight a 1073741824 hb
      step as ⟨wa, hwa⟩
      have hwb := weight_of_spec weight b 1073741824 hb
      step as ⟨wb, hwb⟩
      step as ⟨sum, hsum⟩
      have hsum1spec : (if sum > 1073741824#usize then ok 1073741824#usize else ok sum) ⦃ s =>
          s.val ≤ 1073741824 ⦄ := by
        split <;> step* <;> scalar_tac
      step as ⟨sum1, hsum1⟩
      step as ⟨i, hi⟩
      have hiw : i.val < weight.val.length := by rw [hwl]; omega
      step as ⟨x, back, hx, hback⟩
      have hcl : created.val < left.val.length := by rw [hll]; exact hclt'
      step as ⟨x1, back1, hx1, hback1⟩
      have hcr' : created.val < right.val.length := by rw [hrl]; exact hclt'
      step as ⟨x2, back2, hx2, hback2⟩
      step as ⟨created1, hcreated1⟩
      step as ⟨remaining1, hremaining1⟩
      simp only [hback, hback1, hback2, WP.spec_ok]
      refine ⟨⟨hsmall, hol, ?_, ?_, ?_, ?_, hlq2, by omega, by omega, by omega⟩, by omega⟩
      · simp only [alloc.vec.Vec.set_val_eq, List.length_set]; exact hwl
      · simp only [alloc.vec.Vec.set_val_eq, List.length_set]; exact hll
      · simp only [alloc.vec.Vec.set_val_eq, List.length_set]; exact hrl
      · simp only [alloc.vec.Vec.set_val_eq]; exact bounded_set hb _ _ hsum1
    · try simp only [WP.spec_ok]
      exact ⟨hll, hrl, hcr⟩
  · try simp only [WP.spec_ok]
    exact ⟨hll, hrl, hcr⟩

@[step]
theorem merge_loop (n used : ℕ) (order weight left right : alloc.vec.Vec Usize)
    (nn usedn lq iq created remaining : Usize) (hnn : nn.val = n) (husedn : usedn.val = used)
    (h : MergeState n used order weight left right lq iq created remaining) :
    tree_depths_loop2 nn order usedn weight left right lq iq created remaining ⦃ r =>
      r.1.val.length = used ∧ r.2.1.val.length = used ∧ r.2.2.val ≤ used ⦄ := by
  unfold tree_depths_loop2
  apply loop.spec_decr_nat (fun (_, _, _, _, _, _, rem) => rem.val)
    (fun (weight', left', right', lq', iq', created', remaining') =>
      MergeState n used order weight' left' right' lq' iq' created' remaining')
  · rintro ⟨weight', left', right', lq', iq', created', remaining'⟩ h'
    refine WP.spec_mono (merge_body n used order weight' left' right' nn usedn lq' iq' created' remaining' hnn husedn h') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨w, l, rr, a, b, c, d⟩ := state
        exact ⟨hr.1, hr.2⟩
  · exact h

theorem depth_body (n : ℕ) (nn : Usize) (left right depth : alloc.vec.Vec Usize) (k : Usize)
    (hnn : nn.val = n) (hsmall : n ≤ 1024) (used : ℕ) (hused : used ≤ 1024)
    (hll : left.val.length = used) (hrl : right.val.length = used) (hdl : depth.val.length = n + used)
    (hk : k.val ≤ used) :
    tree_depths_loop3.body nn left right depth k ⦃ r =>
      match r with
      | .done depth' => depth'.val.length = n + used
      | .cont (depth', k') => depth'.val.length = n + used ∧ k'.val < k.val ∧ k'.val ≤ used ⦄ := by
  unfold tree_depths_loop3.body
  split
  · rename_i hkpos
    have hkpos' : 0 < k.val := by scalar_tac
    step as ⟨k1, hk1⟩
    step as ⟨i, hi⟩
    have hid : i.val < depth.val.length := by rw [hdl]; omega
    step as ⟨d, hd⟩
    have hchildSpec : (if d < 1000#usize then d + 1#usize else ok 1000#usize) ⦃ c => c.val ≤ 1000 ⦄ := by
      split <;> step* <;> scalar_tac
    step as ⟨child, hchild⟩
    have hk1l : k1.val < left.val.length := by rw [hll]; omega
    step as ⟨l, hl⟩
    have hk1r : k1.val < right.val.length := by rw [hrl]; omega
    step as ⟨r, hr⟩
    have hdepth1Spec : (if l < i then do
          let (_, index_mut_back) ← alloc.vec.Vec.index_mut_usize depth l
          ok (index_mut_back child)
        else ok depth) ⦃ d1 => d1.val.length = n + used ⦄ := by
      split
      · rename_i hli
        have hli' : l.val < depth.val.length := by rw [hdl]; scalar_tac
        step as ⟨x, back, hx, hback⟩
        simp only [hback, alloc.vec.Vec.set_val_eq, List.length_set, WP.spec_ok]
        exact hdl
      · try simp only [WP.spec_ok]
        exact hdl
    step as ⟨depth1, hdepth1⟩
    split
    · rename_i hri
      have hri' : r.val < depth1.val.length := by rw [hdepth1]; scalar_tac
      step as ⟨x, back, hx, hback⟩
      simp only [hback, alloc.vec.Vec.set_val_eq, List.length_set, WP.spec_ok]
      exact ⟨hdepth1, by omega, by omega⟩
    · try simp only [WP.spec_ok]
      exact ⟨hdepth1, by omega, by omega⟩
  · try simp only [WP.spec_ok]
    exact hdl

@[step]
theorem depth_loop (n : ℕ) (nn : Usize) (left right depth : alloc.vec.Vec Usize) (k : Usize)
    (hnn : nn.val = n) (hsmall : n ≤ 1024) (used : ℕ) (hused : used ≤ 1024)
    (hll : left.val.length = used) (hrl : right.val.length = used) (hdl : depth.val.length = n + used)
    (hk : k.val ≤ used) :
    tree_depths_loop3 nn depth left right k ⦃ r => r.val.length = n + used ⦄ := by
  unfold tree_depths_loop3
  apply loop.spec_decr_nat (fun (_, k') => k'.val)
    (fun (depth', k') => depth'.val.length = n + used ∧ k'.val ≤ used)
  · rintro ⟨depth', k'⟩ ⟨hd', hk'⟩
    refine WP.spec_mono (depth_body n nn left right depth' k' hnn hsmall used hused hll hrl hd' hk') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨depth'', k''⟩ := state
        exact ⟨⟨hr.1, hr.2.2⟩, hr.2.1⟩
  · exact ⟨hdl, hk⟩

theorem tree_depths_spec (freq : alloc.vec.Vec Usize) (hsmall : freq.val.length ≤ 1024) :
    tree_depths freq ⦃ r => r.val.length = freq.val.length ⦄ := by
  unfold tree_depths
  dsimp only
  have hlen : (alloc.vec.Vec.len freq).val = freq.val.length := by
    simp [alloc.vec.Vec.len_val, alloc.vec.Vec.length]
  have hord := order_loop freq (alloc.vec.Vec.len freq) (alloc.vec.Vec.with_capacity Usize (alloc.vec.Vec.len freq)) 0#usize
    hlen.symm (by rw [hlen]; exact hsmall) (by simp) (by simp [alloc.vec.Vec.with_capacity])
  step with hord as ⟨order, horder⟩
  have hol : order.val.length ≤ freq.val.length := by rw [← hlen]; exact horder
  have holen : (alloc.vec.Vec.len order).val = order.val.length := by
    simp [alloc.vec.Vec.len_val, alloc.vec.Vec.length]
  step as ⟨i, hi⟩
  rw [hlen, holen] at hi
  step as ⟨depth, hdepth⟩
  have hdl : depth.val.length = freq.val.length + order.val.length := by
    rw [hdepth, List.length_replicate, hi]
  have hsingle : (if alloc.vec.Vec.len order = 1#usize then do
        let s ← alloc.vec.Vec.index_usize order 0#usize
        if s < alloc.vec.Vec.len freq then do
          let (_, index_mut_back) ← alloc.vec.Vec.index_mut_usize depth s
          ok (index_mut_back 1#usize)
        else ok depth
      else ok depth) ⦃ d1 => d1.val.length = freq.val.length + order.val.length ⦄ := by
    split
    · rename_i hone
      have hone' : order.val.length = 1 := by
        have := congrArg UScalar.val hone
        rw [holen] at this
        simpa using this
      step as ⟨s, hs⟩
      split
      · rename_i hsn
        have hsn' : s.val < depth.val.length := by
          rw [hdl]
          have := (UScalar.lt_equiv _ _).mp hsn
          rw [hlen] at this
          omega
        step as ⟨x, back, hx, hback⟩
        simp only [hback, alloc.vec.Vec.set_val_eq, List.length_set, WP.spec_ok]
        exact hdl
      · try simp only [WP.spec_ok]
        exact hdl
    · try simp only [WP.spec_ok]
      exact hdl
  step as ⟨depth1, hdepth1⟩
  split
  · rename_i htwo
    have htwo' : 2 ≤ order.val.length := by
      have := (UScalar.le_equiv _ _).mp htwo
      rw [holen] at this
      simpa using this
    step as ⟨weight, hweight⟩
    step as ⟨left, hleft⟩
    have hwl : weight.val.length = freq.val.length + order.val.length := by
      rw [hweight, List.length_replicate, hi]
    have hwb : Bounded weight.val 1073741824 := by
      intro k hk
      rw [hweight, List.length_replicate] at hk
      rw [hweight, List.getElem!_replicate] <;> scalar_tac
    have hw1 := weights_loop freq (alloc.vec.Vec.len freq) 0#usize weight hlen (by simp) (by rw [hwl, hlen]; omega) hwb
    step as ⟨weight1, hwl1, hwb1⟩
    have hll : left.val.length = order.val.length := by rw [hleft, List.length_replicate, holen]
    have hmerge : MergeState freq.val.length order.val.length order weight1 left left
        0#usize 0#usize 0#usize (alloc.vec.Vec.len order) := by
      refine ⟨⟨hsmall, hol.trans hsmall⟩, rfl, hwl1.trans hwl, hll, hll, hwb1, by simp, by simp, by simp, ?_⟩
      rw [holen]
      simp
    have hm := merge_loop freq.val.length order.val.length order weight1 left left (alloc.vec.Vec.len freq)
      (alloc.vec.Vec.len order) 0#usize 0#usize 0#usize (alloc.vec.Vec.len order) hlen holen hmerge
    step as ⟨left1, right, created, hll1, hrl1, hcr⟩
    have hd := depth_loop freq.val.length (alloc.vec.Vec.len freq) left1 right depth1 created hlen hsmall
      order.val.length (hol.trans hsmall) hll1 hrl1 hdepth1 hcr
    step as ⟨depth2, hdepth2⟩
    have hr := alloc.vec.Vec.resize_spec core.clone.CloneUsize depth2 (alloc.vec.Vec.len freq) 0#usize (by rfl)
    step as ⟨out, hout⟩
    rw [hout]
    simp [List.resize, hlen]
    omega
  · have hr := alloc.vec.Vec.resize_spec core.clone.CloneUsize depth1 (alloc.vec.Vec.len freq) 0#usize (by rfl)
    step as ⟨out, hout⟩
    rw [hout]
    simp [List.resize, hlen]
    omega

/-! ### code_lengths -/

theorem copy_body (freq : alloc.vec.Vec Usize) (n : Usize) (f : alloc.vec.Vec Usize) (i : Usize)
    (hn : n.val = freq.val.length) (hsmall : n.val ≤ 1024) (hi : i.val ≤ n.val) (hf : f.val.length = i.val) :
    code_lengths_loop0.body freq n f i ⦃ r =>
      match r with
      | .done (f', i') => f'.val.length = n.val
      | .cont (f', i') => i'.val = i.val + 1 ∧ i'.val ≤ n.val ∧ f'.val.length = i'.val ⦄ := by
  unfold code_lengths_loop0.body
  split
  · rename_i hlt
    have hlt' : i.val < freq.val.length := by scalar_tac
    step as ⟨i1, hi1⟩
    have hspace : f.val.length < Usize.max := by scalar_tac
    step as ⟨f1, hf1⟩
    step as ⟨i2, hi2⟩
    try simp only [WP.spec_ok]
    refine ⟨hi2, by scalar_tac, ?_⟩
    rw [hf1, List.length_append, List.length_singleton, hf, hi2]
  · try simp only [WP.spec_ok]
    have : i.val = n.val := by scalar_tac
    omega

@[step]
theorem copy_loop (freq : alloc.vec.Vec Usize) (n : Usize) (f : alloc.vec.Vec Usize) (i : Usize)
    (hn : n.val = freq.val.length) (hsmall : n.val ≤ 1024) (hi : i.val ≤ n.val) (hf : f.val.length = i.val) :
    code_lengths_loop0 freq n f i ⦃ r => r.1.val.length = n.val ⦄ := by
  unfold code_lengths_loop0
  apply loop.spec_decr_nat (fun (_, i') => n.val - i'.val)
    (fun (f', i') => i'.val ≤ n.val ∧ f'.val.length = i'.val)
  · rintro ⟨f', i'⟩ ⟨hi', hf'⟩
    refine WP.spec_mono (copy_body freq n f' i' hn hsmall hi' hf') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨f'', i''⟩ := state
        exact ⟨⟨hr.2.1, hr.2.2⟩, by change n.val - i''.val < n.val - i'.val; omega⟩
  · exact ⟨hi, hf⟩

theorem longest_body (n : Usize) (depth : alloc.vec.Vec Usize) (i longest : Usize)
    (hd : n.val ≤ depth.val.length) (hi : i.val ≤ n.val)
    (hmax : ∀ i' < i.val, (depth.val[i']!).val ≤ longest.val) :
    code_lengths_loop1_loop0.body n depth i longest ⦃ r =>
      match r with
      | .done l => ∀ i' < n.val, (depth.val[i']!).val ≤ l.val
      | .cont (i', l) => i'.val = i.val + 1 ∧ i'.val ≤ n.val ∧ ∀ i'' < i'.val, (depth.val[i'']!).val ≤ l.val ⦄ := by
  unfold code_lengths_loop1_loop0.body
  split
  · rename_i hlt
    have hlt' : i.val < depth.val.length := by scalar_tac
    step as ⟨i1, hi1⟩
    have hi1v : i1 = depth.val[i.val]! := by rw [hi1, getElem!_pos depth.val i.val hlt']
    have hlSpec : (if i1 > longest then ok i1 else ok longest) ⦃ l =>
        longest.val ≤ l.val ∧ i1.val ≤ l.val ⦄ := by
      split <;> simp only [WP.spec_ok] <;> scalar_tac
    step as ⟨l1, hl1, hl2⟩
    step as ⟨i2, hi2⟩
    try simp only [WP.spec_ok]
    refine ⟨hi2, by scalar_tac, ?_⟩
    intro i'' hi''
    rw [hi2] at hi''
    by_cases hii : i'' < i.val
    · exact (hmax i'' hii).trans hl1
    · have he : i'' = i.val := by omega
      rw [he, ← hi1v]
      exact hl2
  · rename_i hge
    have he : i.val = n.val := by scalar_tac
    try simp only [WP.spec_ok]
    intro i' hi'
    exact hmax i' (by omega)

@[step]
theorem longest_loop (n : Usize) (depth : alloc.vec.Vec Usize) (i longest : Usize)
    (hd : n.val ≤ depth.val.length) (hi : i.val ≤ n.val)
    (hmax : ∀ i' < i.val, (depth.val[i']!).val ≤ longest.val) :
    code_lengths_loop1_loop0 n i depth longest ⦃ l => ∀ i' < n.val, (depth.val[i']!).val ≤ l.val ⦄ := by
  unfold code_lengths_loop1_loop0
  apply loop.spec_decr_nat (fun (i', _) => n.val - i'.val)
    (fun (i', l') => i'.val ≤ n.val ∧ ∀ i'' < i'.val, (depth.val[i'']!).val ≤ l'.val)
  · rintro ⟨i', l'⟩ ⟨hi', hmax'⟩
    refine WP.spec_mono (longest_body n depth i' l' hd hi' hmax') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨i'', l''⟩ := state
        exact ⟨⟨hr.2.1, hr.2.2⟩, by change n.val - i''.val < n.val - i'.val; omega⟩
  · exact ⟨hi, hmax⟩

theorem assign_body (n : Usize) (depth : alloc.vec.Vec Usize) (i : Usize) (lens : alloc.vec.Vec U8)
    (limit : ℕ) (hlimit : limit ≤ 15)
    (hd : n.val ≤ depth.val.length) (hl : lens.val.length = n.val) (hi : i.val ≤ n.val)
    (hdb : ∀ i' < n.val, (depth.val[i']!).val ≤ limit) (hlb : ∀ i' < n.val, (lens.val[i']!).val ≤ limit) :
    code_lengths_loop1_loop1.body n depth i lens ⦃ r =>
      match r with
      | .done (_, lens') => lens'.val.length = n.val ∧ ∀ i' < n.val, (lens'.val[i']!).val ≤ limit
      | .cont (i', lens') => i'.val = i.val + 1 ∧ i'.val ≤ n.val ∧ lens'.val.length = n.val ∧
          ∀ i'' < n.val, (lens'.val[i'']!).val ≤ limit ⦄ := by
  unfold code_lengths_loop1_loop1.body
  split
  · rename_i hlt
    have hlt' : i.val < depth.val.length := by scalar_tac
    step as ⟨i1, hi1⟩
    have hi1v : i1 = depth.val[i.val]! := by rw [hi1, getElem!_pos depth.val i.val hlt']
    have hi1b : i1.val ≤ limit := by rw [hi1v]; exact hdb i.val (by scalar_tac)
    have hil : i.val < lens.val.length := by rw [hl]; scalar_tac
    step as ⟨x, back, hx, hback⟩
    step as ⟨i2, hi2⟩
    have hi2v : i2.val = i1.val := by
      rw [hi2, UScalar.cast_val_eq]
      exact Nat.mod_eq_of_lt (by scalar_tac)
    step as ⟨i3, hi3⟩
    simp only [hback, alloc.vec.Vec.set_val_eq, List.length_set, WP.spec_ok]
    refine ⟨hi3, by scalar_tac, hl, ?_⟩
    intro i'' hi''
    rw [Djinn.Vocab.getElem!_set lens.val i.val i'' i2 (by rw [hl]; exact hi'')]
    split
    · rw [hi2v]; exact hi1b
    · exact hlb i'' hi''
  · try simp only [WP.spec_ok]
    exact ⟨hl, hlb⟩

@[step]
theorem assign_loop (n : Usize) (depth : alloc.vec.Vec Usize) (i : Usize) (lens : alloc.vec.Vec U8)
    (limit : ℕ) (hlimit : limit ≤ 15)
    (hd : n.val ≤ depth.val.length) (hl : lens.val.length = n.val) (hi : i.val ≤ n.val)
    (hdb : ∀ i' < n.val, (depth.val[i']!).val ≤ limit) (hlb : ∀ i' < n.val, (lens.val[i']!).val ≤ limit) :
    code_lengths_loop1_loop1 n i lens depth ⦃ r => r.2.val.length = n.val ∧
      ∀ i' < n.val, (r.2.val[i']!).val ≤ limit ⦄ := by
  unfold code_lengths_loop1_loop1
  apply loop.spec_decr_nat (fun (i', _) => n.val - i'.val)
    (fun (i', lens') => i'.val ≤ n.val ∧ lens'.val.length = n.val ∧ ∀ i'' < n.val, (lens'.val[i'']!).val ≤ limit)
  · rintro ⟨i', lens'⟩ ⟨hi', hl', hlb'⟩
    refine WP.spec_mono (assign_body n depth i' lens' limit hlimit hd hl' hi' hdb hlb') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨i'', lens''⟩ := state
        exact ⟨⟨hr.2.1, hr.2.2.1, hr.2.2.2⟩, by change n.val - i''.val < n.val - i'.val; omega⟩
  · exact ⟨hi, hl, hlb⟩

theorem halve_body (n : Usize) (f : alloc.vec.Vec Usize) (i : Usize)
    (hf : f.val.length = n.val) (hi : i.val ≤ n.val) :
    code_lengths_loop1_loop2.body n f i ⦃ r =>
      match r with
      | .done (f', _) => f'.val.length = n.val
      | .cont (f', i') => i'.val = i.val + 1 ∧ i'.val ≤ n.val ∧ f'.val.length = n.val ⦄ := by
  unfold code_lengths_loop1_loop2.body
  split
  · rename_i hlt
    have hlt' : i.val < f.val.length := by rw [hf]; scalar_tac
    step as ⟨v, hv⟩
    have hf1Spec : (if v > 1#usize then do
          let i1 ← v / 2#usize
          let i2 ← v % 2#usize
          let half ← i1 + i2
          let (_, index_mut_back) ← alloc.vec.Vec.index_mut_usize f i
          ok (index_mut_back half)
        else ok f) ⦃ f' => f'.val.length = n.val ⦄ := by
      split
      · step as ⟨i1, hi1⟩
        step as ⟨i2, hi2⟩
        step as ⟨half, hhalf⟩
        step as ⟨x, back, hx, hback⟩
        simp only [hback, alloc.vec.Vec.set_val_eq, List.length_set, WP.spec_ok]
        exact hf
      · try simp only [WP.spec_ok]
        exact hf
    step as ⟨f1, hf1⟩
    step as ⟨i1, hi1⟩
    try simp only [WP.spec_ok]
    exact ⟨hi1, by scalar_tac, hf1⟩
  · try simp only [WP.spec_ok]
    exact hf

@[step]
theorem halve_loop (n : Usize) (f : alloc.vec.Vec Usize) (i : Usize)
    (hf : f.val.length = n.val) (hi : i.val ≤ n.val) :
    code_lengths_loop1_loop2 n f i ⦃ r => r.1.val.length = n.val ⦄ := by
  unfold code_lengths_loop1_loop2
  apply loop.spec_decr_nat (fun (_, i') => n.val - i'.val)
    (fun (f', i') => i'.val ≤ n.val ∧ f'.val.length = n.val)
  · rintro ⟨f', i'⟩ ⟨hi', hf'⟩
    refine WP.spec_mono (halve_body n f' i' hf' hi') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨f'', i''⟩ := state
        exact ⟨⟨hr.2.1, hr.2.2⟩, by change n.val - i''.val < n.val - i'.val; omega⟩
  · exact ⟨hi, hf⟩

theorem retry_body (limit n : Usize) (f : alloc.vec.Vec Usize) (i : Usize) (lens : alloc.vec.Vec U8)
    (attempts : I32) (done1 : Bool) (hsmall : n.val ≤ 1024) (hf : f.val.length = n.val)
    (hl : lens.val.length = n.val) (ha : 0 ≤ attempts.val ∧ attempts.val ≤ 40)
    (hlimit : limit.val ≤ 15) (hlb : ∀ i' < n.val, (lens.val[i']!).val ≤ limit.val) :
    code_lengths_loop1.body limit n f i lens attempts done1 ⦃ r =>
      match r with
      | .done lens' => lens'.val.length = n.val ∧ ∀ i' < n.val, (lens'.val[i']!).val ≤ limit.val
      | .cont (f', _, lens', attempts', done') => f'.val.length = n.val ∧ lens'.val.length = n.val ∧
          (∀ i' < n.val, (lens'.val[i']!).val ≤ limit.val) ∧
          0 ≤ attempts'.val ∧ attempts'.val ≤ 40 ∧
          (if done' then 0 else 1) + 2 * (40 - attempts'.val).toNat <
            (if done1 then 0 else 1) + 2 * (40 - attempts.val).toNat ⦄ := by
  unfold code_lengths_loop1.body
  split
  · try simp only [WP.spec_ok]
    exact ⟨hl, hlb⟩
  · rename_i hnd
    have hnd' : done1 = false := by cases done1 <;> simp_all
    split
    · rename_i hlt
      have hlt' : attempts.val < 40 := by scalar_tac
      have htd := tree_depths_spec f (by rw [hf]; exact hsmall)
      step as ⟨depth, hdepth⟩
      have hlong := longest_loop n depth 0#usize 0#usize (by rw [hdepth, hf]) (by simp)
        (fun i' hi' => by simp at hi')
      step as ⟨longest, hlongest⟩
      split
      · rename_i hle
        have hle' : longest.val ≤ limit.val := by scalar_tac
        have hassign := assign_loop n depth 0#usize lens limit.val hlimit (by rw [hdepth, hf]) hl (by simp)
          (fun i' hi' => (hlongest i' hi').trans hle') hlb
        step as ⟨i1, lens1, hlens1, hlb1⟩
        try simp only [WP.spec_ok, hnd']
        refine ⟨hf, hlens1, hlb1, ha.1, ha.2, ?_⟩
        simp [hnd']
      · have hhalve := halve_loop n f 0#usize hf (by simp)
        step as ⟨f1, i1, hf1⟩
        step as ⟨attempts1, hattempts1⟩
        simp only [WP.spec_ok, hnd']
        refine ⟨hf1, hl, hlb, by omega, by omega, ?_⟩
        simp only [Bool.false_eq_true, if_false]
        omega
    · try simp only [WP.spec_ok]
      exact ⟨hl, hlb⟩

@[step]
theorem retry_loop (limit n : Usize) (f : alloc.vec.Vec Usize) (i : Usize) (lens : alloc.vec.Vec U8)
    (attempts : I32) (done1 : Bool) (hsmall : n.val ≤ 1024) (hf : f.val.length = n.val)
    (hl : lens.val.length = n.val) (ha : 0 ≤ attempts.val ∧ attempts.val ≤ 40)
    (hlimit : limit.val ≤ 15) (hlb : ∀ i' < n.val, (lens.val[i']!).val ≤ limit.val) :
    code_lengths_loop1 limit n f i lens attempts done1 ⦃ r => r.val.length = n.val ∧
      ∀ i' < n.val, (r.val[i']!).val ≤ limit.val ⦄ := by
  unfold code_lengths_loop1
  apply loop.spec_decr_nat (fun (_, _, _, a, d) => (if d then 0 else 1) + 2 * (40 - a.val).toNat)
    (fun (f', _, lens', a, _) => f'.val.length = n.val ∧ lens'.val.length = n.val ∧
      (∀ i' < n.val, (lens'.val[i']!).val ≤ limit.val) ∧ 0 ≤ a.val ∧ a.val ≤ 40)
  · rintro ⟨f', i', lens', a, d⟩ ⟨hf', hl', hlb', ha0, ha1⟩
    refine WP.spec_mono (retry_body limit n f' i' lens' a d hsmall hf' hl' ⟨ha0, ha1⟩ hlimit hlb') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨f'', i'', lens'', a', d'⟩ := state
        exact ⟨⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1⟩, hr.2.2.2.2.2⟩
  · exact ⟨hf, hl, hlb, ha⟩

@[step]
theorem zeros_u8_correct (n : Usize) :
    zeros_u8 n ⦃ out => out.val = List.replicate n.val 0#u8 ⦄ := by
  unfold zeros_u8
  have hr := alloc.vec.Vec.resize_spec core.clone.CloneU8 (alloc.vec.Vec.new U8) n 0#u8 (by rfl)
  step as ⟨v, hv⟩
  rw [hv]
  unfold List.resize
  simp [alloc.vec.Vec.new]

theorem code_lengths_spec (freq : alloc.vec.Vec Usize) (limit : Usize) (hsmall : freq.val.length ≤ 1024)
    (hlimit : limit.val ≤ 15) :
    code_lengths freq limit ⦃ r => r.val.length = freq.val.length ∧
      ∀ i' < r.val.length, (r.val[i']!).val ≤ limit.val ⦄ := by
  unfold code_lengths
  dsimp only
  have hlen : (alloc.vec.Vec.len freq).val = freq.val.length := by
    simp [alloc.vec.Vec.len_val, alloc.vec.Vec.length]
  have hc := copy_loop freq (alloc.vec.Vec.len freq) (alloc.vec.Vec.with_capacity Usize (alloc.vec.Vec.len freq)) 0#usize hlen
    (by rw [hlen]; exact hsmall) (by simp) (by simp [alloc.vec.Vec.with_capacity])
  step with hc as ⟨f, i, hf⟩
  step as ⟨lens, hlens⟩
  have hr := retry_loop limit (alloc.vec.Vec.len freq) f i lens 0#i32 false (by rw [hlen]; exact hsmall) hf
    (by rw [hlens, List.length_replicate]) (by simp) hlimit
    (by
      intro i' hi'
      rw [hlens, List.getElem!_replicate] <;> scalar_tac)
  refine WP.spec_mono hr ?_
  intro r hr'
  obtain ⟨h1, h2⟩ := hr'
  refine ⟨by rw [h1, hlen], ?_⟩
  intro i' hi'
  exact h2 i' (by rw [h1] at hi'; exact hi')

end Gzip.Proofs.Huff
