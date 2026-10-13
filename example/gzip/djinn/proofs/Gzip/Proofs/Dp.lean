import Gzip.Proofs.Plans
import Gzip.Proofs.Costs
import Gzip.Proofs.Chains
import Gzip.Proofs.Reverse
import Gzip.Proofs.Tables
import Gzip.Proofs.Hints
import Gzip.Proofs.Edges
import Gzip.Proofs.Cache
import Gzip.Proofs.Cells

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Plans Gzip.Proofs.Matches Gzip.Proofs.Cells

set_option maxRecDepth 10000

namespace Gzip.Proofs.Dp

def infinity : ℕ := 1073741823

/-- A price list: the bits of the 286 literal/length symbols (each at most 15), then from index
286 on the bits of a copy of each length 0..258 (the length symbol with its extra bits, at most
20), and of the 30 distance symbols (each at most 15). -/
def Prices (lcost dcost : List U32) : Prop :=
  lcost.length = 545 ∧ dcost.length = 30 ∧
  (∀ k < 286, (lcost[k]!).val ≤ 15) ∧ (∀ k < 30, (dcost[k]!).val ≤ 15) ∧
  (∀ k, 286 ≤ k → k < 545 → (lcost[k]!).val ≤ 20)

/-- The row of cells (`Cells`) while the first `done` positions have been priced: every path's
bits are in bounds, the positions up to `done` are reached (at most 15 bits per byte), and every
cell with a finite path records a valid last token ending at its position. -/
structure Matrix (data : List U8) (start stop size done : ℕ) (dp : List U64) : Prop where
  sizeBound : size ≤ 32768
  dpSize : dp.length = size + 1
  progressed : done ≤ size
  bounded : ∀ j < dp.length, cost dp[j]! ≤ infinity
  reached : ∀ j ≤ done, cost dp[j]! ≤ 15 * j
  valid : ∀ j < dp.length, 0 < j → cost dp[j]! < infinity →
    len dp[j]! ≤ j ∧ StepN data (start + (j - len dp[j]!)) stop (len dp[j]!) (dist dp[j]!)

theorem get_set {α : Type} [Inhabited α] (xs : List α) (i k : ℕ) (x : α) (hk : k < xs.length) :
    (xs.set i x)[k]! = if i = k then x else xs[k]! := by
  rw [getElem!_pos (xs.set i x) k (by simpa using hk), List.getElem_set,
    getElem!_pos xs k hk]

/-- A cell beyond the priced positions may change to any cell in bounds that, if its path is
finite, records a valid last token. -/
theorem future {data : List U8} {start stop size done j : ℕ} {dp : List U64}
    (h : Matrix data start stop size done dp) (c : U64) (hj : done < j) (hjs : j ≤ size)
    (hb : cost c ≤ infinity)
    (hv : cost c < infinity → len c ≤ j ∧ StepN data (start + (j - len c)) stop (len c) (dist c)) :
    Matrix data start stop size done (dp.set j c) := by
  refine ⟨h.sizeBound, by simpa using h.dpSize, h.progressed, ?_, ?_, ?_⟩
  · intro k hk
    have hk' : k < dp.length := by simpa using hk
    rw [get_set dp j k c hk']
    split
    · exact hb
    · exact h.bounded k hk'
  · intro k hk
    have hk' : k < dp.length := by rw [h.dpSize]; omega
    rw [get_set dp j k c hk', if_neg (by omega)]
    exact h.reached k hk
  · intro k hk hkpos hkfinite
    have hk' : k < dp.length := by simpa using hk
    rw [get_set dp j k c hk'] at hkfinite ⊢
    by_cases he : j = k
    · subst k
      simp only [if_pos rfl] at hkfinite ⊢
      exact hv hkfinite
    · simp only [if_neg he] at hkfinite ⊢
      exact h.valid k hk' hkpos hkfinite

theorem advance {data : List U8} {start stop size done : ℕ} {dp : List U64}
    (h : Matrix data start stop size done dp) (hd : done < size)
    (hc : cost dp[done + 1]! ≤ 15 * (done + 1)) :
    Matrix data start stop size (done + 1) dp := by
  refine ⟨h.sizeBound, h.dpSize, by omega, h.bounded, ?_, h.valid⟩
  intro j hj
  by_cases hj0 : j ≤ done
  · exact h.reached j hj0
  · have he : j = done + 1 := by omega
    simpa [he] using hc

theorem full {data : List U8} {start stop size : ℕ} {dp : List U64}
    (h : Matrix data start stop size size dp) :
    Predecessors data start stop dp := by
  intro j hj hjs
  have hjbound : j ≤ size := by rw [h.dpSize] at hjs; omega
  have hc := h.reached j hjbound
  apply h.valid j hjs hj
  have hs := h.sizeBound
  unfold infinity
  omega

-- ================================================================ pricing one candidate

theorem relax_body (data : List U8) (start stop size : ℕ)
    (i n dist len j last : Usize) (lcost : alloc.vec.Vec U32) (base tail : U64)
    (dp : alloc.vec.Vec U64)
    (h : Matrix data start stop size (i.val + 1) dp.val)
    (hend : start + size = stop) (hn : n.val ≤ 258) (hin : i.val + n.val ≤ size)
    (hlc : lcost.val.length = 545) (hlb : ∀ k, 286 ≤ k → k < 545 → (lcost.val[k]!).val ≤ 20)
    (hbase : base.val ≤ 15 * i.val + 28) (htail : tail.val = dist.val)
    (hlen : 3 ≤ len.val ∧ len.val ≤ 259)
    (hlast : last.val = i.val + n.val) (hj : j.val = i.val + len.val)
    (hd : 0 < dist.val ∧ dist.val ≤ start + i.val ∧ dist.val ≤ 32768)
    (hrun : EqualRun data (start + i.val) (start + i.val - dist.val) n.val) :
    relax_loop.body lcost base tail last dp len j ⦃ r =>
      match r with
      | .done d => Matrix data start stop size (i.val + 1) d.val
      | .cont (d, next, nj) => Matrix data start stop size (i.val + 1) d.val ∧
          next.val = len.val + 1 ∧ 3 ≤ next.val ∧ next.val ≤ 259 ∧
          nj.val = i.val + next.val ⦄ := by
  have hsize := h.sizeBound
  have hprocessed := h.progressed
  have hdsize := h.dpSize
  unfold relax_loop.body
  split
  · have hln : len.val ≤ n.val := by scalar_tac
    step as ⟨i1, hi1⟩
    have hi1b : i1.val < lcost.val.length := by omega
    step as ⟨i2, hi2⟩
    have hi2b : i2.val ≤ 20 := by
      rw [hi2, ← getElem!_pos lcost.val i1.val hi1b]
      exact hlb i1.val (by omega) (by omega)
    step as ⟨i3, hi3⟩
    have hi3v : i3.val = i2.val := by rw [hi3]; exact cast_u32_u64 i2
    step as ⟨cost, hcost⟩
    have hcf : cost.val < infinity := by unfold infinity; omega
    have hc32 : cost.val < 4294967296 := by unfold infinity at hcf; omega
    have hjb : j.val < dp.val.length := by omega
    step as ⟨old, hold⟩
    have holdE : old = dp.val[j.val]! := by rw [hold, getElem!_pos dp.val j.val hjb]
    step as ⟨i4, hi4⟩
    step as ⟨i5, hi5⟩
    have hi5v : i5.val = len.val := by rw [hi5]; exact Hints.cast_u64 len
    step as ⟨i6, hi6⟩
    step as ⟨i7, hi7⟩
    step as ⟨fresh, hfresh⟩
    have hfreshv : fresh.val = cost.val * 4294967296 + len.val * 65536 + dist.val := by omega
    have hpr := probe_spec cost hc32
    step as ⟨i8, hi8⟩
    have hvalidN : StepN data (start + i.val) stop len.val dist.val := by
      refine Or.inr ⟨Or.inr ⟨hlen.1, by omega, by omega, hd.1, hd.2.1, hd.2.2, ?_⟩, hd.1⟩
      intro k hk
      exact hrun k (by omega)
    have hf := fields cost.val len.val dist.val hc32 (by omega) (by omega)
    have hcellSpec : (if i8 < old then ok fresh else ok old) ⦃ c =>
        Cells.cost c ≤ infinity ∧
        (Cells.cost c < infinity → Cells.len c ≤ j.val ∧
          StepN data (start + (j.val - Cells.len c)) stop (Cells.len c) (Cells.dist c)) ⦄ := by
      split
      · simp only [WP.spec_ok]
        unfold Cells.cost Cells.len Cells.dist
        rw [hfreshv, hf.1, hf.2.1, hf.2.2]
        refine ⟨by omega, fun _ => ⟨by omega, ?_⟩⟩
        have he : j.val - len.val = i.val := by omega
        rw [he]
        exact hvalidN
      · simp only [WP.spec_ok]
        rw [holdE]
        exact ⟨h.bounded j.val hjb, h.valid j.val hjb (by omega)⟩
    step as ⟨cell, hcb, hcv⟩
    step
    step as ⟨len1, hlen1⟩
    step as ⟨j1, hj1⟩
    try simp only [WP.spec_ok]
    refine ⟨?_, hlen1, by omega, by omega, by omega⟩
    rw [index_mut_back_post, alloc.vec.Vec.set_val_eq]
    exact future (j := j.val) h cell (by omega) (by omega) hcb hcv
  · step*

@[step]
theorem relax_loop_spec (data : List U8) (start stop size : ℕ)
    (i n dist len j last : Usize) (lcost : alloc.vec.Vec U32) (base tail : U64)
    (dp : alloc.vec.Vec U64)
    (h : Matrix data start stop size (i.val + 1) dp.val)
    (hend : start + size = stop) (hn : n.val ≤ 258) (hin : i.val + n.val ≤ size)
    (hlc : lcost.val.length = 545) (hlb : ∀ k, 286 ≤ k → k < 545 → (lcost.val[k]!).val ≤ 20)
    (hbase : base.val ≤ 15 * i.val + 28) (htail : tail.val = dist.val)
    (hlen : 3 ≤ len.val ∧ len.val ≤ 259)
    (hlast : last.val = i.val + n.val) (hj : j.val = i.val + len.val)
    (hd : 0 < dist.val ∧ dist.val ≤ start + i.val ∧ dist.val ≤ 32768)
    (hrun : EqualRun data (start + i.val) (start + i.val - dist.val) n.val) :
    relax_loop lcost dp base tail len last j ⦃ r =>
      Matrix data start stop size (i.val + 1) r.val ⦄ := by
  unfold relax_loop
  apply loop.spec_decr_nat (fun (_, k, _) => 259 - k.val)
    (fun (d, k, jj) => Matrix data start stop size (i.val + 1) d.val ∧
      3 ≤ k.val ∧ k.val ≤ 259 ∧ jj.val = i.val + k.val)
  · rintro ⟨d, k, jj⟩ ⟨hmat, hk0, hk1, hjj⟩
    refine WP.spec_mono (relax_body data start stop size i n dist k jj last lcost base tail d
      hmat hend hn hin hlc hlb hbase htail ⟨hk0, hk1⟩ hlast hjj hd hrun) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨d', k', jj'⟩ := state
        obtain ⟨hmat', he, hk0', hk1', hjj'⟩ := hr
        exact ⟨⟨hmat', hk0', hk1', hjj'⟩, by change 259 - k'.val < 259 - k.val; omega⟩
  · exact ⟨h, hlen.1, hlen.2, hj⟩

theorem relax_correct (data : List U8) (start stop size : ℕ)
    (i n dist longest : Usize) (lcost dcost : alloc.vec.Vec U32)
    (dp : alloc.vec.Vec U64)
    (h : Matrix data start stop size (i.val + 1) dp.val)
    (hend : start + size = stop) (hprices : Prices lcost.val dcost.val)
    (hn : n.val ≤ 258) (hin : i.val + n.val ≤ size) (hlong : 2 ≤ longest.val ∧ longest.val ≤ 258)
    (hd : 0 < dist.val ∧ dist.val ≤ start + i.val ∧ dist.val ≤ 32768)
    (hrun : EqualRun data (start + i.val) (start + i.val - dist.val) n.val) :
    relax i n dist longest lcost dcost dp ⦃ r =>
      Matrix data start stop size (i.val + 1) r.val ⦄ := by
  obtain ⟨hlc, hdc, hlb, hdbnd, hbig⟩ := hprices
  have hsize := h.sizeBound
  have hdsize := h.dpSize
  have hi : i.val < dp.val.length := by omega
  have hc := h.reached i.val (by omega)
  unfold relax
  step as ⟨dc, hdc0, hdc1, hdc2⟩
  have hdcb : dc.val < dcost.val.length := by omega
  step as ⟨i1, hi1⟩
  have hi1E : i1 = dp.val[i.val]! := by rw [hi1, getElem!_pos dp.val i.val hi]
  step as ⟨i2, hi2⟩
  have hi2b : i2.val ≤ 15 * i.val := by rw [hi2, hi1E]; exact hc
  step as ⟨i3, hi3⟩
  have hi3b : i3.val ≤ 15 := by
    rw [hi3, ← getElem!_pos dcost.val dc.val hdcb]
    exact hdbnd dc.val (by omega)
  have hde := Costs.distance_extra_bound dc.val (by omega)
  have hdd : dc.val < DIST_EXTRA.val.length := by simp [DIST_EXTRA, Array.make]; omega
  rw [getElem!_pos DIST_EXTRA.val dc.val hdd] at hde
  step as ⟨i4, hi4⟩
  step as ⟨i5, hi5⟩
  have hi5b : i5.val ≤ 28 := by scalar_tac
  step as ⟨i6, hi6⟩
  have hi6v : i6.val = i5.val := by rw [hi6]; exact cast_u32_u64 i5
  step as ⟨base, hbase⟩
  have hbase' : base.val ≤ 15 * i.val + 28 := by omega
  step as ⟨tail, htail⟩
  have htail' : tail.val = dist.val := by rw [htail]; exact Hints.cast_u64 dist
  step as ⟨len, hlen⟩
  have hlen' : 3 ≤ len.val ∧ len.val ≤ 259 := by scalar_tac
  step as ⟨last, hlast⟩
  -- The guards hold (`n` below 259, the last cell within the row, 545 prices); the branches
  -- that skip the loop leave the row as it is.
  split
  · try dsimp only
    split
    · try dsimp only
      split
      · step as ⟨j, hj⟩
        have hl := relax_loop_spec data start stop size i n dist len j last lcost base tail dp
          h hend hn hin hlc hbig hbase' htail' hlen' hlast hj hd hrun
        step*
      · simp only [WP.spec_ok]
        exact h
    · simp only [WP.spec_ok]
      exact h
  · simp only [WP.spec_ok]
    exact h

-- ================================================================ pricing and recording

theorem relax_rec_body (data : List U8) (start stop size : ℕ)
    (i n dist len j last dc : Usize) (lcost : alloc.vec.Vec U32) (base tail ebase : U64)
    (dp edges : alloc.vec.Vec U64)
    (h : Matrix data start stop size (i.val + 1) dp.val)
    (he : Edges.Edges data start stop edges.val)
    (hend : start + size = stop) (hn : n.val ≤ 258) (hin : i.val + n.val ≤ size)
    (hlc : lcost.val.length = 545) (hlb : ∀ k, 286 ≤ k → k < 545 → (lcost.val[k]!).val ≤ 20)
    (hbase : base.val ≤ 15 * i.val + 28) (htail : tail.val = dist.val)
    (hdc : dc.val < 30)
    (hebase : ebase.val = i.val * 281474976710656 + (253 + 256 * dc.val) * 4294967296 + dist.val)
    (hlen : 3 ≤ len.val ∧ len.val ≤ 259)
    (hlast : last.val = i.val + n.val) (hj : j.val = i.val + len.val)
    (hd : 0 < dist.val ∧ dist.val ≤ start + i.val ∧ dist.val ≤ 32768)
    (hrun : EqualRun data (start + i.val) (start + i.val - dist.val) n.val) :
    relax_rec_loop.body lcost base tail last ebase dp edges len j ⦃ r =>
      match r with
      | .done (d, e) => Matrix data start stop size (i.val + 1) d.val ∧
          Edges.Edges data start stop e.val
      | .cont (d, e, next, nj) => Matrix data start stop size (i.val + 1) d.val ∧
          Edges.Edges data start stop e.val ∧
          next.val = len.val + 1 ∧ 3 ≤ next.val ∧ next.val ≤ 259 ∧
          nj.val = i.val + next.val ⦄ := by
  have hsize := h.sizeBound
  have hprocessed := h.progressed
  have hdsize := h.dpSize
  unfold relax_rec_loop.body
  split
  · have hln : len.val ≤ n.val := by scalar_tac
    step as ⟨i1, hi1⟩
    have hi1b : i1.val < lcost.val.length := by omega
    step as ⟨i2, hi2⟩
    have hi2b : i2.val ≤ 20 := by
      rw [hi2, ← getElem!_pos lcost.val i1.val hi1b]
      exact hlb i1.val (by omega) (by omega)
    step as ⟨i3, hi3⟩
    have hi3v : i3.val = i2.val := by rw [hi3]; exact cast_u32_u64 i2
    step as ⟨cost, hcost⟩
    have hcf : cost.val < infinity := by unfold infinity; omega
    have hc32 : cost.val < 4294967296 := by unfold infinity at hcf; omega
    have hjb : j.val < dp.val.length := by omega
    step as ⟨old, hold⟩
    have holdE : old = dp.val[j.val]! := by rw [hold, getElem!_pos dp.val j.val hjb]
    step as ⟨i4, hi4⟩
    step as ⟨i5, hi5⟩
    have hi5v : i5.val = len.val := by rw [hi5]; exact Hints.cast_u64 len
    step as ⟨i6, hi6⟩
    step as ⟨i7, hi7⟩
    step as ⟨fresh, hfresh⟩
    have hfreshv : fresh.val = cost.val * 4294967296 + len.val * 65536 + dist.val := by omega
    have hpr := probe_spec cost hc32
    step as ⟨i8, hi8⟩
    have hvalidN : StepN data (start + i.val) stop len.val dist.val := by
      refine Or.inr ⟨Or.inr ⟨hlen.1, by omega, by omega, hd.1, hd.2.1, hd.2.2, ?_⟩, hd.1⟩
      intro k hk
      exact hrun k (by omega)
    have hf := fields cost.val len.val dist.val hc32 (by omega) (by omega)
    have hcellSpec : (if i8 < old then ok fresh else ok old) ⦃ c =>
        Cells.cost c ≤ infinity ∧
        (Cells.cost c < infinity → Cells.len c ≤ j.val ∧
          StepN data (start + (j.val - Cells.len c)) stop (Cells.len c) (Cells.dist c)) ⦄ := by
      split
      · simp only [WP.spec_ok]
        unfold Cells.cost Cells.len Cells.dist
        rw [hfreshv, hf.1, hf.2.1, hf.2.2]
        refine ⟨by omega, fun _ => ⟨by omega, ?_⟩⟩
        have he' : j.val - len.val = i.val := by omega
        rw [he']
        exact hvalidN
      · simp only [WP.spec_ok]
        rw [holdE]
        exact ⟨h.bounded j.val hjb, h.valid j.val hjb (by omega)⟩
    step as ⟨cell, hcb, hcv⟩
    step
    have hmatN : Matrix data start stop size (i.val + 1) (index_mut_back cell).val := by
      rw [index_mut_back_post, alloc.vec.Vec.set_val_eq]
      exact future (j := j.val) h cell (by omega) (by omega) hcb hcv
    split
    · rename_i hsmall
      have hsmall' : edges.val.length < 1073741824 := by
        have := (UScalar.lt_equiv _ _).mp hsmall
        simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length] at this
        scalar_tac
      step as ⟨i9, hi9⟩
      have hi9v : i9.val = len.val := by rw [hi9]; exact Hints.cast_u64 len
      step as ⟨i10, hi10⟩
      step as ⟨i11, hi11⟩
      have hok : Edges.EdgeOk data start stop i11 :=
        Edges.edge_ok i11 i.val (253 + 256 * dc.val + len.val) len.val dist.val
          (by omega) (by omega) (by omega) (by omega) (by omega) hvalidN
      have hcap : edges.val.length < Usize.max := by scalar_tac
      step as ⟨edges2, hedges2⟩
      step as ⟨len1, hlen1⟩
      step as ⟨j1, hj1⟩
      try simp only [WP.spec_ok]
      refine ⟨hmatN, ?_, hlen1, by omega, by omega, by omega⟩
      rw [hedges2]
      exact Edges.push he i11 hok
    · step as ⟨len1, hlen1⟩
      step as ⟨j1, hj1⟩
      try simp only [WP.spec_ok]
      exact ⟨hmatN, he, hlen1, by omega, by omega, by omega⟩
  · step*

@[step]
theorem relax_rec_loop_spec (data : List U8) (start stop size : ℕ)
    (i n dist len j last dc : Usize) (lcost : alloc.vec.Vec U32) (base tail ebase : U64)
    (dp edges : alloc.vec.Vec U64)
    (h : Matrix data start stop size (i.val + 1) dp.val)
    (he : Edges.Edges data start stop edges.val)
    (hend : start + size = stop) (hn : n.val ≤ 258) (hin : i.val + n.val ≤ size)
    (hlc : lcost.val.length = 545) (hlb : ∀ k, 286 ≤ k → k < 545 → (lcost.val[k]!).val ≤ 20)
    (hbase : base.val ≤ 15 * i.val + 28) (htail : tail.val = dist.val)
    (hdc : dc.val < 30)
    (hebase : ebase.val = i.val * 281474976710656 + (253 + 256 * dc.val) * 4294967296 + dist.val)
    (hlen : 3 ≤ len.val ∧ len.val ≤ 259)
    (hlast : last.val = i.val + n.val) (hj : j.val = i.val + len.val)
    (hd : 0 < dist.val ∧ dist.val ≤ start + i.val ∧ dist.val ≤ 32768)
    (hrun : EqualRun data (start + i.val) (start + i.val - dist.val) n.val) :
    relax_rec_loop lcost dp edges base tail len last j ebase ⦃ r =>
      Matrix data start stop size (i.val + 1) r.1.val ∧
      Edges.Edges data start stop r.2.val ⦄ := by
  unfold relax_rec_loop
  apply loop.spec_decr_nat (fun (_, _, k, _) => 259 - k.val)
    (fun (d, e, k, jj) => Matrix data start stop size (i.val + 1) d.val ∧
      Edges.Edges data start stop e.val ∧
      3 ≤ k.val ∧ k.val ≤ 259 ∧ jj.val = i.val + k.val)
  · rintro ⟨d, e, k, jj⟩ ⟨hmat, he', hk0, hk1, hjj⟩
    refine WP.spec_mono (relax_rec_body data start stop size i n dist k jj last dc lcost base tail
      ebase d e hmat he' hend hn hin hlc hlb hbase htail hdc hebase ⟨hk0, hk1⟩ hlast hjj hd hrun) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨d', e', k', jj'⟩ := state
        obtain ⟨hmat', he'', hk, hk0', hk1', hjj'⟩ := hr
        exact ⟨⟨hmat', he'', hk0', hk1', hjj'⟩, by change 259 - k'.val < 259 - k.val; omega⟩
  · exact ⟨h, he, hlen.1, hlen.2, hj⟩

theorem relax_rec_correct (data : List U8) (start stop size : ℕ)
    (i n dist longest : Usize) (lcost dcost : alloc.vec.Vec U32)
    (dp edges : alloc.vec.Vec U64)
    (h : Matrix data start stop size (i.val + 1) dp.val)
    (he : Edges.Edges data start stop edges.val)
    (hend : start + size = stop) (hprices : Prices lcost.val dcost.val)
    (hn : n.val ≤ 258) (hin : i.val + n.val ≤ size) (hlong : 2 ≤ longest.val ∧ longest.val ≤ 258)
    (hd : 0 < dist.val ∧ dist.val ≤ start + i.val ∧ dist.val ≤ 32768)
    (hrun : EqualRun data (start + i.val) (start + i.val - dist.val) n.val) :
    relax_rec i n dist longest lcost dcost dp edges ⦃ r =>
      Matrix data start stop size (i.val + 1) r.1.val ∧
      Edges.Edges data start stop r.2.val ⦄ := by
  obtain ⟨hlc, hdc, hlb, hdbnd, hbig⟩ := hprices
  have hsize := h.sizeBound
  have hdsize := h.dpSize
  have hi : i.val < dp.val.length := by omega
  have hc := h.reached i.val (by omega)
  unfold relax_rec
  step as ⟨dc, hdc0, hdc1, hdc2⟩
  have hdcb : dc.val < dcost.val.length := by omega
  step as ⟨i1, hi1⟩
  have hi1E : i1 = dp.val[i.val]! := by rw [hi1, getElem!_pos dp.val i.val hi]
  step as ⟨i2, hi2⟩
  have hi2b : i2.val ≤ 15 * i.val := by rw [hi2, hi1E]; exact hc
  step as ⟨i3, hi3⟩
  have hi3b : i3.val ≤ 15 := by
    rw [hi3, ← getElem!_pos dcost.val dc.val hdcb]
    exact hdbnd dc.val (by omega)
  have hde := Costs.distance_extra_bound dc.val (by omega)
  have hdd : dc.val < DIST_EXTRA.val.length := by simp [DIST_EXTRA, Array.make]; omega
  rw [getElem!_pos DIST_EXTRA.val dc.val hdd] at hde
  step as ⟨i4, hi4⟩
  step as ⟨i5, hi5⟩
  have hi5b : i5.val ≤ 28 := by scalar_tac
  step as ⟨i6, hi6⟩
  have hi6v : i6.val = i5.val := by rw [hi6]; exact cast_u32_u64 i5
  step as ⟨base, hbase⟩
  have hbase' : base.val ≤ 15 * i.val + 28 := by omega
  step as ⟨tail, htail⟩
  have htail' : tail.val = dist.val := by rw [htail]; exact Hints.cast_u64 dist
  step as ⟨len, hlen⟩
  have hlen' : 3 ≤ len.val ∧ len.val ≤ 259 := by scalar_tac
  step as ⟨last, hlast⟩
  split
  · try dsimp only
    split
    · try dsimp only
      split
      · step as ⟨j, hj⟩
        step as ⟨i9, hi9⟩
        have hi9v : i9.val = i.val := by rw [hi9]; exact Hints.cast_u64 i
        step as ⟨i10, hi10⟩
        step as ⟨i11, hi11⟩
        step as ⟨i12, hi12⟩
        step as ⟨i13, hi13⟩
        have hi13v : i13.val = i12.val := by rw [hi13]; exact Hints.cast_u64 i12
        step as ⟨i14, hi14⟩
        step as ⟨i15, hi15⟩
        step as ⟨ebase, hebase⟩
        have hdc30 : dc.val < 30 := by omega
        have hebase' : ebase.val =
            i.val * 281474976710656 + (253 + 256 * dc.val) * 4294967296 + dist.val := by
          omega
        have hl := relax_rec_loop_spec data start stop size i n dist len j last dc lcost base tail
          ebase dp edges h he hend hn hin hlc hbig hbase' htail' hdc30 hebase' hlen' hlast hj hd hrun
        step*
      · simp only [WP.spec_ok]
        exact ⟨h, he⟩
    · simp only [WP.spec_ok]
      exact ⟨h, he⟩
  · simp only [WP.spec_ok]
    exact ⟨h, he⟩

/-- A verified match priced, and recorded as edges when `record`. -/
theorem price_match_correct (data : List U8) (start stop size : ℕ)
    (i n dist longest : Usize) (lcost dcost : alloc.vec.Vec U32)
    (dp edges : alloc.vec.Vec U64) (record : Bool)
    (h : Matrix data start stop size (i.val + 1) dp.val)
    (he : Edges.Edges data start stop edges.val)
    (hend : start + size = stop) (hprices : Prices lcost.val dcost.val)
    (hn : n.val ≤ 258) (hin : i.val + n.val ≤ size) (hlong : 2 ≤ longest.val ∧ longest.val ≤ 258)
    (hd : 0 < dist.val ∧ dist.val ≤ start + i.val ∧ dist.val ≤ 32768)
    (hrun : EqualRun data (start + i.val) (start + i.val - dist.val) n.val) :
    price_match i n dist longest lcost dcost dp record edges ⦃ r =>
      Matrix data start stop size (i.val + 1) r.1.val ∧
      Edges.Edges data start stop r.2.val ⦄ := by
  unfold price_match
  split
  · exact relax_rec_correct data start stop size i n dist longest lcost dcost dp edges h he hend
      hprices hn hin hlong hd hrun
  · have hr := relax_correct data start stop size i n dist longest lcost dcost dp h hend hprices
      hn hin hlong hd hrun
    step as ⟨dp1, hmat1⟩
    try simp only [WP.spec_ok]
    exact ⟨hmat1, he⟩

-- ================================================================ the initial row

def Initial (dp : List U64) (n : ℕ) : Prop :=
  dp.length = n ∧ ∀ k < n, (dp[k]!).val = if k = 0 then 0 else 4611686014132420608

@[step]
theorem initial_costs_correct (size : Usize) (hs : size.val ≤ 32768) :
    initial_costs size ⦃ c => Initial c.val (size.val + 1) ⦄ := by
  unfold initial_costs
  step as ⟨i, hi⟩
  have hr := alloc.vec.Vec.resize_spec core.clone.CloneU64 (alloc.vec.Vec.new U64) i
    4611686014132420608#u64 (by rfl)
  step as ⟨dp, hdp⟩
  have hval : dp.val = List.replicate (size.val + 1) 4611686014132420608#u64 := by
    rw [hdp, hi]
    unfold List.resize
    simp [alloc.vec.Vec.new]
  have hlen : dp.val.length = size.val + 1 := by rw [hval, List.length_replicate]
  step
  try simp only [WP.spec_ok]
  rw [index_mut_back_post, alloc.vec.Vec.set_val_eq]
  refine ⟨by simp [List.length_set, hlen], ?_⟩
  intro k hk
  have h0 : (0#usize).val = 0 := by simp
  rw [h0, get_set dp.val 0 k 0#u64 (by omega)]
  split
  · rw [if_pos (by omega)]
    rfl
  · rw [if_neg (by omega), hval, List.getElem!_replicate _ (by omega)]
    rfl

theorem initial_matrix (data : List U8) (start stop size : ℕ) (dp : List U64)
    (hs : size ≤ 32768) (ht : Initial dp (size + 1)) :
    Matrix data start stop size 0 dp := by
  refine ⟨hs, ht.1, by omega, ?_, ?_, ?_⟩
  · intro j hj
    have he := ht.2 j (by rw [← ht.1]; exact hj)
    unfold Cells.cost
    rw [he]
    split <;> unfold infinity <;> omega
  · intro j hj
    have hz : j = 0 := by omega
    subst j
    have he := ht.2 0 (by omega)
    simp only [eq_self_iff_true, ite_true] at he
    unfold Cells.cost
    rw [he]
  · intro j hj hjpos hjfinite
    have he := ht.2 j (by rw [← ht.1]; exact hj)
    rw [if_neg (by omega)] at he
    unfold Cells.cost at hjfinite
    rw [he] at hjfinite
    unfold infinity at hjfinite
    omega

-- ================================================================ one position

@[step]
theorem literal_update (data : List U8) (start stop size : ℕ) (bits : U32) (i : Usize)
    (dp : alloc.vec.Vec U64)
    (h : Matrix data start stop size i.val dp.val)
    (hi : i.val < size) (hb : bits.val ≤ 15) :
    literal_step bits i dp ⦃ r =>
      Matrix data start stop size (i.val + 1) r.val ⦄ := by
  have hs := h.sizeBound
  have hds := h.dpSize
  have hib : i.val < dp.val.length := by omega
  have hc := h.reached i.val (by omega)
  unfold literal_step
  step as ⟨i1, hi1⟩
  have hi1E : i1 = dp.val[i.val]! := by rw [hi1, getElem!_pos dp.val i.val hib]
  step as ⟨i2, hi2⟩
  have hi2b : i2.val ≤ 15 * i.val := by rw [hi2, hi1E]; exact hc
  step as ⟨i3, hi3⟩
  have hi3v : i3.val = bits.val := by rw [hi3]; exact cast_u32_u64 bits
  step as ⟨cost, hcost⟩
  have hcb : cost.val ≤ 15 * (i.val + 1) := by omega
  have hcf : cost.val < infinity := by unfold infinity; omega
  have hc32 : cost.val < 4294967296 := by omega
  step as ⟨next, hnext⟩
  have hnb : next.val < dp.val.length := by omega
  step as ⟨old, hold⟩
  have holdE : old = dp.val[next.val]! := by rw [hold, getElem!_pos dp.val next.val hnb]
  step as ⟨i4, hi4⟩
  step as ⟨fresh, hfresh⟩
  have hfreshv : fresh.val = cost.val * 4294967296 + 1 * 65536 + 0 := by omega
  have hpr := probe_spec cost hc32
  step as ⟨i5, hi5⟩
  have hf := fields cost.val 1 0 hc32 (by omega) (by omega)
  have hcellSpec : (if i5 < old then ok fresh else ok old) ⦃ c =>
      Cells.cost c ≤ infinity ∧ Cells.cost c ≤ 15 * next.val ∧
      (Cells.cost c < infinity → Cells.len c ≤ next.val ∧
        StepN data (start + (next.val - Cells.len c)) stop (Cells.len c) (Cells.dist c)) ⦄ := by
    split
    · simp only [WP.spec_ok]
      unfold Cells.cost Cells.len Cells.dist
      rw [hfreshv, hf.1, hf.2.1, hf.2.2]
      exact ⟨by omega, by omega, fun _ => ⟨by omega, Or.inl ⟨rfl, rfl⟩⟩⟩
    · rename_i hnot
      simp only [WP.spec_ok]
      have hle : old.val ≤ i5.val := by scalar_tac
      have hco : Cells.cost old ≤ cost.val := by
        unfold Cells.cost
        rw [hi5] at hle
        omega
      rw [holdE] at hco ⊢
      exact ⟨h.bounded next.val hnb, by omega, h.valid next.val hnb (by omega)⟩
  step as ⟨cell, hcb', hcr, hcv⟩
  step
  try simp only [WP.spec_ok]
  rw [index_mut_back_post, alloc.vec.Vec.set_val_eq]
  have hf' := future (j := next.val) h cell (by omega) (by omega) hcb' hcv
  apply advance hf' (by omega)
  rw [← hnext, get_set dp.val next.val next.val cell (by omega)]
  simp only [ite_true]
  exact hcr

/-- The literal at `i` priced, and recorded as an edge when `record`. -/
@[step]
theorem literal_entry_update (data : List U8) (start stop size : ℕ) (bits : U32) (b : U8)
    (i : Usize) (dp : alloc.vec.Vec U64) (record : Bool) (edges : alloc.vec.Vec U64)
    (h : Matrix data start stop size i.val dp.val)
    (hi : i.val < size) (hb : bits.val ≤ 15)
    (he : Edges.Edges data start stop edges.val) :
    literal_entry bits b i dp record edges ⦃ r =>
      Matrix data start stop size (i.val + 1) r.1.val ∧
      Edges.Edges data start stop r.2.val ⦄ := by
  have hs := h.sizeBound
  unfold literal_entry
  step as ⟨dp1, hmat1⟩
  split
  · split
    · rename_i hsmall
      have hsmall' : edges.val.length < 1073741824 := by
        have := (UScalar.lt_equiv _ _).mp hsmall
        simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length] at this
        scalar_tac
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = i.val := by rw [hi2]; exact Hints.cast_u64 i
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = b.val := by
        rw [hi4]
        apply UScalar.cast_val_mod_pow_greater_numBits_eq
        simp [UScalarTy.numBits]
      step as ⟨i5, hi5⟩
      step as ⟨i6, hi6⟩
      step as ⟨i7, hi7⟩
      have hok : Edges.EdgeOk data start stop i7 :=
        Edges.literal_ok i7 i.val b.val (by omega) (by scalar_tac) (by omega)
      have hcap : edges.val.length < Usize.max := by scalar_tac
      step as ⟨edges1, hedges1⟩
      try simp only [WP.spec_ok]
      refine ⟨hmat1, ?_⟩
      rw [hedges1]
      exact Edges.push he i7 hok
    · simp only [WP.spec_ok]
      exact ⟨hmat1, he⟩
  · simp only [WP.spec_ok]
    exact ⟨hmat1, he⟩

/-- The literal price of the byte at `p`. -/
theorem literal_price (lcost : alloc.vec.Vec U32) (hlc : lcost.val.length = 545)
    (hlb : ∀ k < 286, (lcost.val[k]!).val ≤ 15) (b : U8) :
    (do
      let i ← lift (UScalar.cast .Usize b)
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) lcost i : Result U32) ⦃ c =>
      c.val ≤ 15 ⦄ := by
  step as ⟨i, hi⟩
  have hib : i.val < lcost.val.length := by scalar_tac
  step as ⟨c, hc⟩
  rw [hc, ← getElem!_pos lcost.val i.val hib]
  exact hlb i.val (by scalar_tac)

-- ================================================================ the tree walk

set_option maxHeartbeats 4000000

/-- A link table keeps its size when written. -/
theorem set_length (chain : alloc.vec.Vec U32) (k : Usize) (x : U32) (h : chain.val.length = 65536) :
    (chain.set k x).val.length = 65536 := by
  simp only [alloc.vec.Vec.set_val_eq, List.length_set, h]

/-- One step of a searching walk down the tree: whatever the links say, the matrix only changes
through `relax` with a verified match, the pending links stay inside the table, and a verified
match of the position joins the hints (so the invariant on them is kept). -/
theorem search_body (data : Aeneas.Std.Slice U8) (start size : ℕ)
    (stop p i limit cur lt gt longest count depth tail_lt tail_gt : Usize)
    (go record : Bool)
    (chain : alloc.vec.Vec U32) (lcost dcost : alloc.vec.Vec U32)
    (dp : alloc.vec.Vec U64)
    (hints : alloc.vec.Vec U64)
    (h : Matrix data.val start stop.val size (i.val + 1) dp.val)
    (hp : p.val = start + i.val) (hend : start + size = stop.val) (hdata : stop.val ≤ data.val.length)
    (hprices : Prices lcost.val dcost.val)
    (hlimit : limit.val ≤ 258 ∧ p.val + limit.val ≤ stop.val)
    (hlong : 2 ≤ longest.val ∧ longest.val ≤ 258)
    (hchain : chain.val.length = 65536) (hcount : count.val ≤ depth.val)
    (hlt : lt.val < 65536) (hgt : gt.val < 65536)
    (hh : Edges.Edges data.val start stop.val hints.val) :
    walk_search_loop.body data p i depth limit lcost dcost record chain dp hints cur lt gt
      longest count go tail_lt tail_gt ⦃ r =>
      match r with
      | .done (c, d, hints', lt', gt', _, _, _) =>
          c.val.length = 65536 ∧ lt'.val < 65536 ∧ gt'.val < 65536 ∧
          Matrix data.val start stop.val size (i.val + 1) d.val ∧
          Edges.Edges data.val start stop.val hints'.val
      | .cont (c, d, hints', _, lt', gt', lo, cnt, _, _, _) =>
          c.val.length = 65536 ∧ lt'.val < 65536 ∧ gt'.val < 65536 ∧
          Matrix data.val start stop.val size (i.val + 1) d.val ∧
          Edges.Edges data.val start stop.val hints'.val ∧
          2 ≤ lo.val ∧ lo.val ≤ 258 ∧ cnt.val = count.val + 1 ∧ cnt.val ≤ depth.val ⦄ := by
  have hprogress := h.progressed
  have hsize := h.sizeBound
  rw [walk_search_loop.body]
  cases go
  · simp only [Bool.false_eq_true, if_false]
    step*
    all_goals exact ⟨hchain, hlt, hgt, h, hh⟩
  · simp only [if_true]
    split
    · split
      · step as ⟨count1, hcount1⟩
        step as ⟨q, hqv, hqv1⟩
        split
        · -- a node ahead of the position: the walk ends here
          step*
          all_goals (try simp only [WP.spec_ok])
          all_goals exact ⟨hchain, hlt, hgt, h, hh, hlong.1, hlong.2, hcount1, by scalar_tac⟩
        · step as ⟨i1, hi1⟩
          split
          · -- a node out of the window: the walk ends here
            step*
            all_goals (try simp only [WP.spec_ok])
            all_goals exact ⟨hchain, hlt, hgt, h, hh, hlong.1, hlong.2, hcount1, by scalar_tac⟩
          · step as ⟨qs, hqs, hqs1⟩
            have hqsb : qs.val ≤ 32767 := by
              have hmask : q.val &&& 32767 ≤ 32767 := Nat.and_le_right
              rw [hqs, UScalar.val_and]
              change q.val &&& 32767 ≤ 32767
              exact hmask
            -- both children of the node, read before the comparison
            step as ⟨lowi, hlowi⟩
            step as ⟨highi, hhighi⟩
            have hlowib : lowi.val < chain.val.length := by rw [hchain]; omega
            step as ⟨c_lt0, hclt⟩
            step as ⟨c_lt, hc_lt_cast⟩
            have hhighib : highi.val < chain.val.length := by rw [hchain]; omega
            step as ⟨c_gt0, hcgt⟩
            step as ⟨c_gt, hc_gt_cast⟩
            have hf := Cache.match_dir_spec data p q 0#usize limit (by scalar_tac) (by omega)
            step as ⟨n, lower, _, hn0⟩
            have hn : Matches.EqualRun data.val p.val q.val n.val := by
              intro k hk
              exact hn0 k (by simp) hk
            have hl1 := hlimit.1
            have hl2 := hlimit.2
            -- The comparison verified the whole prefix already.
            have hmSpec : (if n <= limit then ok n
                else ok 0#usize) ⦃ m =>
                m.val ≤ limit.val ∧ Matches.EqualRun data.val p.val q.val m.val ⦄ := by
              split
              · have hle : n.val ≤ limit.val := by scalar_tac
                simp only [WP.spec_ok]
                exact ⟨hle, hn⟩
              · step*
                all_goals (try simp only [WP.spec_ok])
                all_goals exact ⟨by simp, by simp [Matches.EqualRun]⟩
            have hsearch : (if n > longest then do
                    let m ← if n <= limit then ok n
                      else ok 0#usize
                    if m > longest then do
                      let (dp2, hints2) ← price_match i m i1 longest lcost dcost dp record hints
                      ok (dp2, hints2, m)
                    else ok (dp, hints, longest)
                  else ok (dp, hints, longest)) ⦃ r =>
                Matrix data.val start stop.val size (i.val + 1) r.1.val ∧
                Edges.Edges data.val start stop.val r.2.1.val ∧
                2 ≤ r.2.2.val ∧ r.2.2.val ≤ 258 ⦄ := by
              split
              · step as ⟨m, hm1, hmEq⟩
                have hm0 : m.val ≤ 258 := by omega
                split
                · have hd : 0 < i1.val ∧ i1.val ≤ start + i.val ∧ i1.val ≤ 32768 := by
                    refine ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
                  have hrun : EqualRun data.val (start + i.val) (start + i.val - i1.val) m.val := by
                    have hdiff : start + i.val - i1.val = q.val := by omega
                    rw [hdiff, ← hp]
                    exact hmEq
                  have hrel := price_match_correct data.val start stop.val size i m i1 longest lcost
                    dcost dp hints record h hh hend hprices hm0 (by omega) hlong hd hrun
                  step as ⟨dp2, hints2, hmat2, hh2⟩
                  try simp only [WP.spec_ok]
                  exact ⟨hmat2, hh2, by scalar_tac, by scalar_tac⟩
                · step*
                  all_goals (try simp only [WP.spec_ok])
                  all_goals exact ⟨h, hh, hlong.1, hlong.2⟩
              · step*
                all_goals (try simp only [WP.spec_ok])
                all_goals exact ⟨h, hh, hlong.1, hlong.2⟩
            step as ⟨dp1, hints1, longest1, hmat1, hh1, hlo0, hlo1⟩
            split
            · -- equal as far as the walk compares: the position takes the node's place
              step*
              all_goals (try simp only [WP.spec_ok])
              all_goals exact ⟨hchain, hlt, hgt, hmat1, hh1, hlo0, hlo1, hcount1, by scalar_tac⟩
            · -- the direction selects: a smaller node is linked below and the walk goes on
              -- with its greater child, a greater node the other way round
              have hslotSpec : (if lower then ok lt else ok gt) ⦃ r => r.val < 65536 ⦄ := by
                split
                all_goals (try simp only [WP.spec_ok])
                all_goals omega
              step as ⟨slot, hslot⟩
              have hnltSpec : (if lower then ok highi else ok lt) ⦃ r => r.val < 65536 ⦄ := by
                split
                all_goals (try simp only [WP.spec_ok])
                all_goals omega
              step as ⟨next_lt, hnlt⟩
              have hngtSpec : (if lower then ok gt else ok lowi) ⦃ r => r.val < 65536 ⦄ := by
                split
                all_goals (try simp only [WP.spec_ok])
                all_goals omega
              step as ⟨next_gt, hngt⟩
              have hncurSpec : (if lower then ok c_gt else ok c_lt) ⦃ _ => True ⦄ := by
                split
                all_goals (try simp only [WP.spec_ok])
                all_goals trivial
              step as ⟨next_cur, _⟩
              step
              step as ⟨cur32, hcur32⟩
              have hlen1 : (index_mut_back cur32).val.length = 65536 := by
                rw [index_mut_back_post]; exact set_length _ _ _ hchain
              all_goals (try simp only [WP.spec_ok])
              all_goals exact ⟨hlen1, hnlt, hngt, hmat1, hh1, hlo0, hlo1, hcount1, by scalar_tac⟩
      · step*
        all_goals exact ⟨hchain, hlt, hgt, h, hh⟩
    · step*
      all_goals exact ⟨hchain, hlt, hgt, h, hh⟩

theorem search_loop (data : Aeneas.Std.Slice U8) (start size : ℕ)
    (stop p i limit cur lt gt longest count depth tail_lt tail_gt : Usize)
    (go record : Bool)
    (chain : alloc.vec.Vec U32) (lcost dcost : alloc.vec.Vec U32)
    (dp : alloc.vec.Vec U64)
    (hints : alloc.vec.Vec U64)
    (h : Matrix data.val start stop.val size (i.val + 1) dp.val)
    (hp : p.val = start + i.val) (hend : start + size = stop.val) (hdata : stop.val ≤ data.val.length)
    (hprices : Prices lcost.val dcost.val)
    (hlimit : limit.val ≤ 258 ∧ p.val + limit.val ≤ stop.val)
    (hlong : 2 ≤ longest.val ∧ longest.val ≤ 258)
    (hchain : chain.val.length = 65536) (hcount : count.val ≤ depth.val)
    (hlt : lt.val < 65536) (hgt : gt.val < 65536)
    (hh : Edges.Edges data.val start stop.val hints.val) :
    walk_search_loop data p i depth limit chain lcost dcost dp record hints cur lt gt longest
      count go tail_lt tail_gt ⦃ r =>
      r.1.val.length = 65536 ∧ r.2.2.2.1.val < 65536 ∧ r.2.2.2.2.1.val < 65536 ∧
      Matrix data.val start stop.val size (i.val + 1) r.2.1.val ∧
      Edges.Edges data.val start stop.val r.2.2.1.val ⦄ := by
  unfold walk_search_loop
  apply loop.spec_decr_nat (fun (_, _, _, _, _, _, _, cnt, _, _, _) => depth.val - cnt.val)
    (fun (c, d, hints', _, lt', gt', lo, cnt, _, _, _) =>
      c.val.length = 65536 ∧ lt'.val < 65536 ∧ gt'.val < 65536 ∧
      Matrix data.val start stop.val size (i.val + 1) d.val ∧
      Edges.Edges data.val start stop.val hints'.val ∧
      2 ≤ lo.val ∧ lo.val ≤ 258 ∧ cnt.val ≤ depth.val)
  · rintro ⟨c, d, hints', cu, lt', gt', lo, cnt, g, tl, tg⟩
      ⟨hc, hlt', hgt', hmat, hhq, hlo0, hlo1, hcnt⟩
    refine WP.spec_mono (search_body data start size stop p i limit cu lt' gt' lo cnt depth tl tg
      g record c lcost dcost d hints' hmat hp hend hdata hprices hlimit ⟨hlo0, hlo1⟩
      hc hcnt hlt' hgt' hhq) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨c', d', hints'', cu', lt'', gt'', lo', cnt', g', tl', tg'⟩ := state
        obtain ⟨hc', hlt'', hgt'', hmat', hhq', hlo0', hlo1', hcnt', hcnt''⟩ := hr
        exact ⟨⟨hc', hlt'', hgt'', hmat', hhq', hlo0', hlo1', hcnt''⟩,
          by change depth.val - cnt'.val < depth.val - cnt.val; omega⟩
  · exact ⟨hchain, hlt, hgt, h, hh, hlong.1, hlong.2, hcount⟩

/-- A searching walk keeps the link table's size, the matrix and the hints' invariant. -/
theorem walk_search_correct (data : Aeneas.Std.Slice U8) (start size : ℕ)
    (stop p i limit cur lt gt longest depth : Usize)
    (record : Bool)
    (chain : alloc.vec.Vec U32) (lcost dcost : alloc.vec.Vec U32)
    (dp : alloc.vec.Vec U64)
    (hints : alloc.vec.Vec U64)
    (h : Matrix data.val start stop.val size (i.val + 1) dp.val)
    (hp : p.val = start + i.val) (hend : start + size = stop.val) (hdata : stop.val ≤ data.val.length)
    (hprices : Prices lcost.val dcost.val)
    (hlimit : limit.val ≤ 258 ∧ p.val + limit.val ≤ stop.val)
    (hlong : 2 ≤ longest.val ∧ longest.val ≤ 258)
    (hchain : chain.val.length = 65536)
    (hlt : lt.val < 65536) (hgt : gt.val < 65536)
    (hh : Edges.Edges data.val start stop.val hints.val) :
    walk_search data p i cur depth limit chain lt gt longest lcost dcost dp record hints ⦃ r =>
      r.2.1.val.length = 65536 ∧
      Matrix data.val start stop.val size (i.val + 1) r.2.2.1.val ∧
      Edges.Edges data.val start stop.val r.2.2.2.val ⦄ := by
  unfold walk_search
  have hcl := search_loop data start size stop p i limit cur lt gt longest 0#usize depth
    0#usize 0#usize true record chain lcost dcost dp hints h hp hend hdata hprices hlimit hlong
    hchain (by simp) hlt hgt hh
  step as ⟨chain1, dp1, hints1, lt1, gt1, longest1, tail_lt, tail_gt,
    hchain1, hlt1, hgt1, hmat1, hh1⟩
  step
  step as ⟨tail_lt32, htail_lt32⟩
  have hlen3 : (index_mut_back tail_lt32).val.length = 65536 := by
    rw [index_mut_back_post]; exact set_length _ _ _ hchain1
  have hgt1b : gt1.val < (index_mut_back tail_lt32).val.length := by rw [hlen3]; exact hgt1
  step
  step as ⟨tail_gt32, htail_gt32⟩
  have hlen4 : (index_mut_back1 tail_gt32).val.length = 65536 := by
    rw [index_mut_back1_post]; exact set_length _ _ _ hlen3
  try simp only [WP.spec_ok]
  exact ⟨hlen4, hmat1, hh1⟩

/-- One step of an insertion-only walk: the pending links stay inside the table. -/
theorem insert_body (data : Aeneas.Std.Slice U8)
    (p limit cur lt gt count depth best_lt best_gt tail_lt tail_gt skip : Usize)
    (go : Bool) (chain : alloc.vec.Vec U32)
    (hlimit : p.val + limit.val ≤ data.val.length)
    (hchain : chain.val.length = 65536) (hcount : count.val ≤ depth.val)
    (hlt : lt.val < 65536) (hgt : gt.val < 65536) :
    walk_insert_loop.body data p depth limit skip chain cur lt gt count go best_lt best_gt
      tail_lt tail_gt ⦃ r =>
      match r with
      | .done (c, lt', gt', _, _) =>
          c.val.length = 65536 ∧ lt'.val < 65536 ∧ gt'.val < 65536
      | .cont (c, _, lt', gt', cnt, _, _, _, _, _) =>
          c.val.length = 65536 ∧ lt'.val < 65536 ∧ gt'.val < 65536 ∧
          cnt.val = count.val + 1 ∧ cnt.val ≤ depth.val ⦄ := by
  rw [walk_insert_loop.body]
  cases go
  · simp only [Bool.false_eq_true, if_false]
    step*
    all_goals exact ⟨hchain, hlt, hgt⟩
  · simp only [if_true]
    split
    · split
      · step as ⟨count1, hcount1⟩
        step as ⟨q, hqv, hqv1⟩
        split
        · step*
          all_goals (try simp only [WP.spec_ok])
          all_goals exact ⟨hchain, hlt, hgt, hcount1, by scalar_tac⟩
        · step as ⟨i1, hi1⟩
          split
          · step*
            all_goals (try simp only [WP.spec_ok])
            all_goals exact ⟨hchain, hlt, hgt, hcount1, by scalar_tac⟩
          · step as ⟨qs, hqs, hqs1⟩
            have hqsb : qs.val ≤ 32767 := by
              have hmask : q.val &&& 32767 ≤ 32767 := Nat.and_le_right
              rw [hqs, UScalar.val_and]
              change q.val &&& 32767 ≤ 32767
              exact hmask
            step as ⟨lowi, hlowi⟩
            step as ⟨highi, hhighi⟩
            have hlowib : lowi.val < chain.val.length := by rw [hchain]; omega
            step as ⟨c_lt0, hclt⟩
            step as ⟨c_lt, hc_lt_cast⟩
            have hhighib : highi.val < chain.val.length := by rw [hchain]; omega
            step as ⟨c_gt0, hcgt⟩
            step as ⟨c_gt, hc_gt_cast⟩
            have hlbSpec : (if best_lt < best_gt then ok best_lt else ok best_gt) ⦃ _ => True ⦄ := by
              split <;> step*
            step as ⟨lb, _⟩
            have hmc := Cache.dir_cached_spec data p q lb limit skip (by scalar_tac) hlimit
            step as ⟨n, lower, _⟩
            split
            · step*
              all_goals (try simp only [WP.spec_ok])
              all_goals exact ⟨hchain, hlt, hgt, hcount1, by scalar_tac⟩
            · have hslotSpec : (if lower then ok lt else ok gt) ⦃ r => r.val < 65536 ⦄ := by
                split
                all_goals (try simp only [WP.spec_ok])
                all_goals omega
              step as ⟨slot, hslot⟩
              have hnltSpec : (if lower then ok highi else ok lt) ⦃ r => r.val < 65536 ⦄ := by
                split
                all_goals (try simp only [WP.spec_ok])
                all_goals omega
              step as ⟨next_lt, hnlt⟩
              have hngtSpec : (if lower then ok gt else ok lowi) ⦃ r => r.val < 65536 ⦄ := by
                split
                all_goals (try simp only [WP.spec_ok])
                all_goals omega
              step as ⟨next_gt, hngt⟩
              have hncurSpec : (if lower then ok c_gt else ok c_lt) ⦃ _ => True ⦄ := by
                split
                all_goals (try simp only [WP.spec_ok])
                all_goals trivial
              step as ⟨next_cur, _⟩
              have hnblSpec : (if lower then ok n else ok best_lt) ⦃ _ => True ⦄ := by
                split
                all_goals (try simp only [WP.spec_ok])
                all_goals trivial
              step as ⟨next_best_lt, _⟩
              have hnbgSpec : (if lower then ok best_gt else ok n) ⦃ _ => True ⦄ := by
                split
                all_goals (try simp only [WP.spec_ok])
                all_goals trivial
              step as ⟨next_best_gt, _⟩
              step
              step as ⟨cur32, hcur32⟩
              have hlen1 : (index_mut_back cur32).val.length = 65536 := by
                rw [index_mut_back_post]; exact set_length _ _ _ hchain
              all_goals (try simp only [WP.spec_ok])
              all_goals exact ⟨hlen1, hnlt, hngt, hcount1, by scalar_tac⟩
      · step*
        all_goals exact ⟨hchain, hlt, hgt⟩
    · step*
      all_goals exact ⟨hchain, hlt, hgt⟩

theorem insert_loop (data : Aeneas.Std.Slice U8)
    (p limit cur lt gt count depth best_lt best_gt tail_lt tail_gt skip : Usize)
    (go : Bool) (chain : alloc.vec.Vec U32)
    (hlimit : p.val + limit.val ≤ data.val.length)
    (hchain : chain.val.length = 65536) (hcount : count.val ≤ depth.val)
    (hlt : lt.val < 65536) (hgt : gt.val < 65536) :
    walk_insert_loop data p depth limit skip chain cur lt gt count go best_lt best_gt tail_lt
      tail_gt ⦃ r =>
      r.1.val.length = 65536 ∧ r.2.1.val < 65536 ∧ r.2.2.1.val < 65536 ⦄ := by
  unfold walk_insert_loop
  apply loop.spec_decr_nat (fun (_, _, _, _, cnt, _, _, _, _, _) => depth.val - cnt.val)
    (fun (c, _, lt', gt', cnt, _, _, _, _, _) =>
      c.val.length = 65536 ∧ lt'.val < 65536 ∧ gt'.val < 65536 ∧ cnt.val ≤ depth.val)
  · rintro ⟨c, cu, lt', gt', cnt, g, bl, bg, tl, tg⟩ ⟨hc, hlt', hgt', hcnt⟩
    refine WP.spec_mono (insert_body data p limit cu lt' gt' cnt depth bl bg tl tg skip g c
      hlimit hc hcnt hlt' hgt') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨c', cu', lt'', gt'', cnt', g', bl', bg', tl', tg'⟩ := state
        obtain ⟨hc', hlt'', hgt'', hcnt', hcnt''⟩ := hr
        exact ⟨⟨hc', hlt'', hgt'', hcnt''⟩,
          by change depth.val - cnt'.val < depth.val - cnt.val; omega⟩
  · exact ⟨hchain, hlt, hgt, hcount⟩

/-- An insertion-only walk keeps the link table's size. -/
theorem walk_insert_correct (data : Aeneas.Std.Slice U8)
    (p cur depth limit skip lt gt : Usize) (chain : alloc.vec.Vec U32)
    (hlimit : p.val + limit.val ≤ data.val.length)
    (hchain : chain.val.length = 65536)
    (hlt : lt.val < 65536) (hgt : gt.val < 65536) :
    walk_insert data p cur depth limit skip chain lt gt ⦃ r => r.val.length = 65536 ⦄ := by
  unfold walk_insert
  have hcl := insert_loop data p limit cur lt gt 0#usize depth 0#usize 0#usize 0#usize 0#usize
    skip true chain hlimit hchain (by simp) hlt hgt
  step as ⟨chain1, lt1, gt1, tail_lt, tail_gt, hchain1, hlt1, hgt1⟩
  step
  step as ⟨tail_lt32, htail_lt32⟩
  have hlen3 : (index_mut_back tail_lt32).val.length = 65536 := by
    rw [index_mut_back_post]; exact set_length _ _ _ hchain1
  have hgt1b : gt1.val < (index_mut_back tail_lt32).val.length := by rw [hlen3]; exact hgt1
  step
  step as ⟨tail_gt32, htail_gt32⟩
  have hlen4 : (index_mut_back1 tail_gt32).val.length = 65536 := by
    rw [index_mut_back1_post]; exact set_length _ _ _ hlen3
  try simp only [WP.spec_ok]
  exact hlen4

/-- `distance_code` is total: its tables cover every distance below the window, 29 above. -/
theorem distance_code_total (dist : Usize) : distance_code dist ⦃ _ => True ⦄ := by
  unfold distance_code
  split
  · have hlt' : dist.val < 257 := by scalar_tac
    step*
  · split
    · rename_i hge hlt
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      case hy => rcases System.Platform.numBits_eq with h | h <;> simp [h]
      have hk : i1.val = (dist.val - 1) / 128 := by
        rw [hi1, Nat.shiftRight_eq_div_pow, hi]
      have hk256 : i1.val < 256 := by rw [hk]; scalar_tac
      step*
    · step*

/-- The nearest copy of four bytes: whatever the table says, the matrix only changes through
`relax` with a verified match, a verified match joins the hints, the table keeps its size, and
the length returned is a match length (2 for none). -/
@[step]
theorem four_candidate_correct (data : Aeneas.Std.Slice U8) (start size : ℕ)
    (p stop i cur : Usize) (searching record : Bool)
    (head : alloc.vec.Vec U32) (lcost dcost : alloc.vec.Vec U32)
    (dp : alloc.vec.Vec U64)
    (hints : alloc.vec.Vec U64)
    (h : Matrix data.val start stop.val size (i.val + 1) dp.val)
    (hp : p.val = start + i.val) (hend : start + size = stop.val) (hdata : stop.val ≤ data.val.length)
    (hpe : p.val < stop.val) (hp4 : p.val + 4 ≤ data.val.length)
    (hprices : Prices lcost.val dcost.val) (hhead : 65536 ≤ head.val.length)
    (hh : Edges.Edges data.val start stop.val hints.val) :
    four_candidate data p stop i cur searching record head lcost dcost dp hints ⦃ r =>
      2 ≤ r.1.val ∧ r.1.val ≤ 258 ∧ r.2.1.val.length = head.val.length ∧
      Matrix data.val start stop.val size (i.val + 1) r.2.2.1.val ∧
      Edges.Edges data.val start stop.val r.2.2.2.val ⦄ := by
  have hsize := h.sizeBound
  unfold four_candidate
  step as ⟨i5, hi5⟩
  step as ⟨h4, hh4⟩
  have hh4b : h4.val < head.val.length := by omega
  step as ⟨c4_raw, hc4_raw⟩
  step as ⟨c4, hc4⟩
  step as ⟨next, hnext⟩
  step
  step as ⟨next32, hnext32⟩
  have hlen1 : (index_mut_back next32).val.length = head.val.length := by
    rw [index_mut_back_post]; simp only [alloc.vec.Vec.set_val_eq, List.length_set]
  split
  · split
    · split
      · step as ⟨q, hq⟩
        have hdcurSpec : (if cur = 0#usize then
              let head2 := index_mut_back next32
              ok (head2, 30#usize)
            else if cur > p then
              let head2 := index_mut_back next32
              ok (head2, 30#usize)
            else do
              let i6 ← next - cur
              let dcur1 ← distance_code i6
              let head2 := index_mut_back next32
              ok (head2, dcur1)) ⦃ r => r.1.val.length = head.val.length ⦄ := by
          split
          · step*
            all_goals (try simp only [WP.spec_ok])
            all_goals exact hlen1
          · split
            · step*
              all_goals (try simp only [WP.spec_ok])
              all_goals exact hlen1
            · step as ⟨i6, _⟩
              have hdc0 := distance_code_total i6
              step as ⟨dcur1, _⟩
              step*
              all_goals (try simp only [WP.spec_ok])
              all_goals exact hlen1
        step as ⟨head1, dcur, hhd⟩
        split
        · step as ⟨i7, hi7⟩
          split
          · have hdc := distance_code_total i7
            step as ⟨i8, _⟩
            split
            · step as ⟨m, hm0, hm1, hmEq⟩
              split
              · have hd : 0 < i7.val ∧ i7.val ≤ start + i.val ∧ i7.val ≤ 32768 := by
                  refine ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
                have hrun : EqualRun data.val (start + i.val) (start + i.val - i7.val) m.val := by
                  have hdiff : start + i.val - i7.val = q.val := by omega
                  rw [hdiff, ← hp]
                  exact hmEq
                have hrel := price_match_correct data.val start stop.val size i m i7 2#usize lcost
                  dcost dp hints record h hh hend hprices hm0 (by omega) (by simp) hd hrun
                step as ⟨dp2, hints2, hmat2, hh2⟩
                try simp only [WP.spec_ok]
                exact ⟨by scalar_tac, hm0, (by first | exact hhd | exact hlen1), hmat2, hh2⟩
              · step*
                all_goals (try simp only [WP.spec_ok])
                all_goals exact ⟨by simp, by simp, (by first | exact hhd | exact hlen1), h, hh⟩
            · step*
              all_goals (try simp only [WP.spec_ok])
              all_goals exact ⟨by simp, by simp, (by first | exact hhd | exact hlen1), h, hh⟩
          · step*
            all_goals (try simp only [WP.spec_ok])
            all_goals exact ⟨by simp, by simp, (by first | exact hhd | exact hlen1), h, hh⟩
        · step*
          all_goals (try simp only [WP.spec_ok])
          all_goals exact ⟨by simp, by simp, (by first | exact hhd | exact hlen1), h, hh⟩
      · step*
        all_goals (try simp only [WP.spec_ok])
        all_goals exact ⟨by simp, by simp, (by first | exact hhd | exact hlen1), h, hh⟩
    · step*
      all_goals (try simp only [WP.spec_ok])
      all_goals exact ⟨by simp, by simp, (by first | exact hhd | exact hlen1), h, hh⟩
  · step*
    all_goals (try simp only [WP.spec_ok])
    all_goals exact ⟨by simp, by simp, (by first | exact hhd | exact hlen1), h, hh⟩

/-- Whether a position enters its tree: a choice, with no bearing on the invariants. -/
@[step]
theorem entered_spec (searching : Bool) (depth : Usize) (p : Usize) :
    entered searching depth p ⦃ _ => True ⦄ := by
  unfold entered
  split
  · simp
  · split
    · step*
      all_goals simp
    · step*
      all_goals simp

theorem position_body (data : Aeneas.Std.Slice U8) (start stop : Usize) (size : ℕ)
    (lcost dcost : alloc.vec.Vec U32) (depth : Usize) (record five four : Bool)
    (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32) (dp : alloc.vec.Vec U64)
    (hints : alloc.vec.Vec U64) (p skip : Usize)
    (h : Matrix data.val start.val stop.val size (p.val - start.val) dp.val)
    (ht : Gzip.Proofs.Chains.Tables head.val chain.val p.val)
    (hp : start.val ≤ p.val ∧ p.val ≤ stop.val)
    (hend : start.val + size = stop.val) (hd : stop.val ≤ data.val.length)
    (hprices : Prices lcost.val dcost.val)
    (hh : Edges.Edges data.val start.val stop.val hints.val) :
    optimal_loop.body data start stop lcost dcost depth record five four head chain dp
      hints p skip ⦃ r =>
      match r with
      | .done (hh', ch, d, hints') => Gzip.Proofs.Chains.Tables hh'.val ch.val stop.val ∧
          Matrix data.val start.val stop.val size size d.val ∧
          Edges.Edges data.val start.val stop.val hints'.val
      | .cont (hh', ch, d, hints', next, _) =>
          Gzip.Proofs.Chains.Tables hh'.val ch.val next.val ∧
          Matrix data.val start.val stop.val size (next.val - start.val) d.val ∧
          next.val = p.val + 1 ∧ next.val ≤ stop.val ∧
          Edges.Edges data.val start.val stop.val hints'.val ⦄ := by
  have hhead := ht.1
  have hchain := ht.2
  have hsize := h.sizeBound
  have hlc := hprices.1
  have hlb := hprices.2.2.1
  unfold optimal_loop.body
  split
  · have hpe : p.val < stop.val := by scalar_tac
    have hpd : p.val ≤ data.val.length := by omega
    step as ⟨i, hi⟩
    have hmat : Matrix data.val start.val stop.val size i.val dp.val := by
      simpa only [hi] using h
    have hip : p.val = start.val + i.val := by omega
    clear hi
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3⟩
    have hi3b : i3.val < lcost.val.length := by rw [hlc]; scalar_tac
    step as ⟨i4, hi4⟩
    have hi4b : i4.val ≤ 15 := by
      rw [hi4, ← getElem!_pos lcost.val i3.val hi3b]
      exact hlb i3.val (by scalar_tac)
    clear hi2 hi3 hi4
    step as ⟨dp1, hintsL, hmat1, hhL⟩
    step as ⟨skip_count, hskip_count⟩
    have hskip_le : skip_count.val ≤ skip.val := by
      rw [hskip_count]
      exact Nat.mod_le _ _
    have hskipSpec : (if skip_count > 0#usize then skip - 1#usize else ok skip) ⦃ _ => True ⦄ := by
      split <;> step*
    step as ⟨skip1, _⟩
    step as ⟨enter, _⟩
    step as ⟨i5, hi5⟩
    -- The position's tables and row, before the shared step to the next position.
    apply WP.spec_bind (Pₘ := fun (r : alloc.vec.Vec U32 × alloc.vec.Vec U32 ×
        alloc.vec.Vec U64 × alloc.vec.Vec U64 × Usize) =>
        Gzip.Proofs.Chains.Tables r.1.val r.2.1.val (p.val + 1) ∧
        Matrix data.val start.val stop.val size (i.val + 1) r.2.2.1.val ∧
        Edges.Edges data.val start.val stop.val r.2.2.2.1.val)
    swap
    · rintro ⟨head1, chain1, dp2, hints2, skip2⟩ ⟨ht1, hm1, hh1⟩
      step as ⟨p1, hp1⟩
      refine ⟨ht1, ?_, hp1, by omega, hh1⟩
      have he : p1.val - start.val = i.val + 1 := by omega
      rw [he]
      exact hm1
    split
    · split
      swap
      · try simp only [WP.spec_ok]
        exact ⟨⟨hhead, hchain⟩, hmat1, hhL⟩
      have hp4 : p.val + 4 ≤ data.val.length := by scalar_tac
      have hbothSpec : ((if four then ok (decide (alloc.vec.Vec.len head ≥ 65536#usize))
          else ok false) : Result Bool) ⦃ b => b = true → 65536 ≤ head.val.length ⦄ := by
        split
        · step*
          all_goals (try simp only [WP.spec_ok])
          all_goals
            intro hb
            try simp only [decide_eq_true_eq, ge_iff_le, alloc.vec.Vec.len_val,
              alloc.vec.Vec.length] at hb
            scalar_tac
        · step*
          all_goals (try simp only [WP.spec_ok])
          all_goals simp
      step with hbothSpec as ⟨both, hboth⟩
      have htmaskSpec : (if both then ok 32767#usize
          else alloc.vec.Vec.len head - 1#usize) ⦃ m => m.val < head.val.length ⦄ := by
        split
        · rename_i hbt
          have hb65 := hboth hbt
          step*
          all_goals (try simp only [WP.spec_ok])
          all_goals omega
        · step as ⟨i7, hi7⟩
          all_goals (try simp only [WP.spec_ok])
          have hi7' : i7.val = head.val.length - 1 := by
            simpa only [alloc.vec.Vec.len_val, alloc.vec.Vec.length] using hi7
          omega
      step as ⟨tmask, htmask⟩
      step as ⟨hsh, hhsh⟩
      have hhb : hsh.val < head.val.length := by omega
      step as ⟨cur_raw, hcur_raw⟩
      step as ⟨cur, hcur⟩
      step as ⟨next, hnext⟩
      step
      step as ⟨next32, hnext32⟩
      step as ⟨slot, hslot, hslot1⟩
      have hslotb : slot.val ≤ 32767 := by
        have hmask : p.val &&& 32767 ≤ 32767 := Nat.and_le_right
        rw [hslot, UScalar.val_and]
        change p.val &&& 32767 ≤ 32767
        exact hmask
      step as ⟨lt, hlt⟩
      step as ⟨gt, hgt⟩
      have hhead1 : (index_mut_back next32).val.length = head.val.length := by
        rw [index_mut_back_post]; simp only [alloc.vec.Vec.set_val_eq, List.length_set]
      have hmat1' : Matrix data.val start.val stop.val size (i.val + 1) dp1.val := hmat1
      have hcandSpec : (if both then do
            let head2 := index_mut_back next32
            let (longest1, head3, dp3, hints2) ←
              four_candidate data p stop i cur (skip_count = 0#usize) record head2 lcost dcost dp1
                hintsL
            ok (head3, dp3, hints2, longest1)
          else
            let head2 := index_mut_back next32
            ok (head2, dp1, hintsL, 2#usize)) ⦃ r =>
          r.1.val.length = head.val.length ∧
          Matrix data.val start.val stop.val size (i.val + 1) r.2.1.val ∧
          Edges.Edges data.val start.val stop.val r.2.2.1.val ∧
          2 ≤ r.2.2.2.val ∧ r.2.2.2.val ≤ 258 ⦄ := by
        split
        · rename_i hbt
          have hfc := four_candidate_correct data start.val size p stop i cur (skip_count = 0#usize) record
            (index_mut_back next32) lcost dcost dp1 hintsL hmat1' hip hend hd hpe
            hp4 hprices (by rw [hhead1]; exact hboth hbt) hhL
          step as ⟨longest1, head3, dp3, hints2, hl0, hl1, hlen3, hmat3, hh3⟩
          step*
          all_goals (try simp only [WP.spec_ok])
          all_goals exact ⟨by rw [hlen3]; exact hhead1, hmat3, hh3, hl0, hl1⟩
        · step*
          all_goals (try simp only [WP.spec_ok])
          all_goals exact ⟨hhead1, hmat1', hhL, by simp, by simp⟩
      step as ⟨head1, dp2, hints1, longest0, hhead1', hmat2', hh2', hlo0, hlo1⟩
      have hfullSpec : (if i5 < 258#usize then ok i5 else ok 258#usize) ⦃ r =>
          r.val ≤ 258 ∧ p.val + r.val ≤ stop.val ⦄ := by
        split <;> step*
        all_goals (try simp only [WP.spec_ok])
        all_goals exact ⟨by scalar_tac, by scalar_tac⟩
      step as ⟨full, hfull1, hfull2⟩
      have hlimitSpec : (if depth > 32#usize then
          if skip_count = 0#usize then ok full
          else if full < 96#usize then ok full else ok 96#usize
          else if skip_count = 0#usize then ok full
          else if full < 32#usize then ok full else ok 32#usize) ⦃ limit =>
          limit.val ≤ 258 ∧ p.val + limit.val ≤ stop.val ⦄ := by
        split
        all_goals
          split
          · step*
            all_goals exact ⟨hfull1, hfull2⟩
          · split <;> step* <;> scalar_tac
      step as ⟨limit, hlimit1, hlimit2⟩
      apply WP.spec_bind (Pₘ := fun (r : alloc.vec.Vec U32 × alloc.vec.Vec U64 ×
          alloc.vec.Vec U64 × Usize) =>
          r.1.val.length = 65536 ∧
          Matrix data.val start.val stop.val size (i.val + 1) r.2.1.val ∧
          Edges.Edges data.val start.val stop.val r.2.2.1.val)
      swap
      · rintro ⟨chain1, dp3, hints2, skip2⟩ ⟨hc1, hm3, hh3⟩
        try simp only [WP.spec_ok]
        exact ⟨⟨by rw [hhead1']; exact hhead, hc1⟩, hm3, hh3⟩
      split
      · -- a searching position: its walk prices the matches it meets
        have hws := walk_search_correct data start.val size stop p i limit cur lt gt longest0 depth
          record chain lcost dcost dp2 hints1 hmat2' hip hend hd hprices ⟨hlimit1, hlimit2⟩
          ⟨hlo0, hlo1⟩ hchain (by omega) (by omega) hh2'
        step as ⟨longest, chain1, dp3, hints2, hchain1, hmat2, hh2⟩
        have hskip2Spec : (if longest >= 64#usize then cache_skip i longest dp3
            else ok skip1) ⦃ _ => True ⦄ := by
          split <;> step*
        step as ⟨skip2, _⟩
        try simp only [WP.spec_ok]
        exact ⟨hchain1, hmat2, hh2⟩
      · -- a position inside a long copy: only linked in
        have hwi := walk_insert_correct data p cur depth limit skip1 lt gt chain (by omega) hchain
          (by omega) (by omega)
        step as ⟨chain1, hchain1⟩
        try simp only [WP.spec_ok]
        exact ⟨hchain1, hmat2', hh2'⟩
    · try simp only [WP.spec_ok]
      exact ⟨⟨hhead, hchain⟩, hmat1, hhL⟩
  · have he : p.val = stop.val := by scalar_tac
    have hei : p.val - start.val = size := by omega
    try simp only [WP.spec_ok]
    refine ⟨ht, by rw [hei] at h; exact h, hh⟩

theorem position_loop (data : Aeneas.Std.Slice U8) (start stop : Usize) (size : ℕ)
    (lcost dcost : alloc.vec.Vec U32) (depth : Usize) (record five four : Bool)
    (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32) (dp : alloc.vec.Vec U64)
    (hints : alloc.vec.Vec U64) (p skip : Usize)
    (h : Matrix data.val start.val stop.val size (p.val - start.val) dp.val)
    (ht : Gzip.Proofs.Chains.Tables head.val chain.val p.val)
    (hp : start.val ≤ p.val ∧ p.val ≤ stop.val)
    (hend : start.val + size = stop.val) (hd : stop.val ≤ data.val.length)
    (hprices : Prices lcost.val dcost.val)
    (hh : Edges.Edges data.val start.val stop.val hints.val) :
    optimal_loop data start stop head chain lcost dcost depth record five four dp
      hints p skip ⦃ r =>
      Gzip.Proofs.Chains.Tables r.1.val r.2.1.val stop.val ∧
      Matrix data.val start.val stop.val size size r.2.2.1.val ∧
      Edges.Edges data.val start.val stop.val r.2.2.2.val ⦄ := by
  unfold optimal_loop
  apply loop.spec_decr_nat (fun (_, _, _, _, q, _) => stop.val - q.val)
    (fun (hh', ch, d, hints', q, _) => Gzip.Proofs.Chains.Tables hh'.val ch.val q.val ∧
      Matrix data.val start.val stop.val size (q.val - start.val) d.val ∧
      start.val ≤ q.val ∧ q.val ≤ stop.val ∧
      Edges.Edges data.val start.val stop.val hints'.val)
  · rintro ⟨hh', ch, d, hints', q, sk⟩ ⟨htq, hmq, hq0, hq1, hhq⟩
    refine WP.spec_mono (position_body data start stop size lcost dcost depth record five four hh' ch d
      hints' q sk hmq htq ⟨hq0, hq1⟩ hend hd hprices hhq) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨hh'', ch', d', hints'', q', sk'⟩ := state
        obtain ⟨ht', hm', he, hq', hh'''⟩ := hr
        exact ⟨⟨ht', hm', by omega, hq', hh'''⟩,
          by change stop.val - q'.val < stop.val - q.val; omega⟩
  · exact ⟨ht, h, hp.1, hp.2, hh⟩

-- ================================================================ the plan

@[step]
theorem trace_correct (data : List U8) (start stop size : ℕ) (sz : Usize)
    (dp : alloc.vec.Vec U64)
    (hsz : sz.val = size) (hsize : size ≤ 32768) (hend : start + size = stop)
    (hlens : dp.val.length = size + 1)
    (hpred : Predecessors data start stop dp.val) :
    trace sz dp ⦃ r => Runs data stop start stop r.lengths.val r.distances.val ⦄ := by
  unfold trace
  have hl := trace_loop data start stop size dp (alloc.vec.Vec.new U16)
    (alloc.vec.Vec.new U16) sz hsize hlens hpred (by omega)
    (by simp [alloc.vec.Vec.new]; omega) (by simp [alloc.vec.Vec.new])
    (by
      simp only [alloc.vec.Vec.new, alloc.vec.Vec.from, List.reverse_nil, hsz, hend]
      exact Runs.finish stop)
  step as ⟨v, v1, hv⟩
  have hvl := runs_lengths hv
  simp only [List.length_reverse] at hvl
  have hv0 := Gzip.Proofs.Reverse.swapped_initial v.val
  have hv10 := Gzip.Proofs.Reverse.swapped_initial v1.val
  step as ⟨v2, v3, hrev, hrev1⟩
  · exact v.val
  · exact v1.val
  · exact hvl.1.symm
  · exact hv0
  · exact hv10
  step*

@[step]
theorem optimal_correct (data : Aeneas.Std.Slice U8) (start stop : Usize)
    (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32) (lcost dcost : alloc.vec.Vec U32) (depth : Usize)
    (record five four : Bool)
    (ht : Gzip.Proofs.Chains.Tables head.val chain.val start.val)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length)
    (hsize : stop.val - start.val ≤ 32768) (hprices : Prices lcost.val dcost.val) :
    optimal data start stop head chain lcost dcost depth record five four ⦃ r =>
      Runs data.val stop.val start.val stop.val r.1.1.lengths.val r.1.1.distances.val ∧
      Gzip.Proofs.Chains.Tables r.2.1.val r.2.2.val stop.val ∧
      Edges.Edges data.val start.val stop.val r.1.2.val ⦄ := by
  unfold optimal
  step as ⟨size, hsz⟩
  step as ⟨dp, hc⟩
  have hmat : Matrix data.val start.val stop.val size.val 0 dp.val :=
    initial_matrix _ _ _ _ _ (by omega) hc
  have hmat' : Matrix data.val start.val stop.val size.val (start.val - start.val) dp.val := by
    simpa only [Nat.sub_self] using hmat
  -- The hints start empty, reserved or not.
  have hcap : (if record then do
        let i ← 8#usize * size
        ok (alloc.vec.Vec.with_capacity U64 i)
      else ok (alloc.vec.Vec.new U64)) ⦃ v => v.val = [] ⦄ := by
    split
    · step as ⟨i, hi⟩
      simp [alloc.vec.Vec.with_capacity]
    · simp only [WP.spec_ok]
      rfl
  step as ⟨hints0, hhints0⟩
  have hh0 : Edges.Edges data.val start.val stop.val hints0.val := by
    rw [hhints0]
    exact Edges.empty _ _ _
  have hpl := position_loop data start stop size.val lcost dcost depth record five four head chain dp
    hints0 start 0#usize hmat' ht ⟨Nat.le_refl _, hs⟩ (by omega)
    hd hprices hh0
  step as ⟨head1, chain1, dp1, hints, ht1, hmat1, hh1⟩
  have hlsize := hmat1.dpSize
  have hpred := full hmat1
  have htr := trace_correct data.val start.val stop.val size.val size dp1 rfl
    (by omega) (by omega) hlsize hpred
  step*
  all_goals (try simp only [WP.spec_ok])
  all_goals exact ⟨by assumption, ht1, hh1⟩

-- ================================================================ the later passes

/-- A cell changed to one that records a valid token ending at its position. -/
theorem pred_set {data : List U8} {start stop : ℕ} {dp : List U64}
    (h : Predecessors data start stop dp) (j : ℕ) (c : U64)
    (hc : 0 < j → Cells.len c ≤ j ∧
      StepN data (start + (j - Cells.len c)) stop (Cells.len c) (Cells.dist c)) :
    Predecessors data start stop (dp.set j c) := by
  intro k hk hkl
  have hkl' : k < dp.length := by simpa using hkl
  rw [get_set dp j k c hkl']
  split
  · rename_i hjk
    subst hjk
    exact hc hk
  · exact h k hk hkl'

/-- The row of a later pass starts with a literal in every cell but the first. -/
@[step]
theorem literal_row_correct (data : List U8) (start stop : ℕ) (size : Usize)
    (hs : size.val ≤ 32768) :
    literal_row size ⦃ c => c.val.length = size.val + 1 ∧ Predecessors data start stop c.val ⦄ := by
  unfold literal_row
  step as ⟨i, hi⟩
  have hr := alloc.vec.Vec.resize_spec core.clone.CloneU64 (alloc.vec.Vec.new U64) i
    4611686014132486144#u64 (by rfl)
  step as ⟨dp, hdp⟩
  have hval : dp.val = List.replicate (size.val + 1) 4611686014132486144#u64 := by
    rw [hdp, hi]
    unfold List.resize
    simp [alloc.vec.Vec.new]
  have hlen : dp.val.length = size.val + 1 := by rw [hval, List.length_replicate]
  step
  try simp only [WP.spec_ok]
  rw [index_mut_back_post, alloc.vec.Vec.set_val_eq]
  refine ⟨by simp [List.length_set, hlen], ?_⟩
  intro k hk hkl
  have hkl' : k < dp.val.length := by simpa using hkl
  have h0 : (0#usize).val = 0 := by simp
  rw [h0, get_set dp.val 0 k 0#u64 hkl', if_neg (by omega), hval,
    List.getElem!_replicate _ (by omega)]
  have hv : (4611686014132486144#u64).val = 4611686014132486144 := by rfl
  unfold Cells.len Cells.dist
  rw [hv]
  exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩

theorem edge_prices_loop0_spec (lcost t : alloc.vec.Vec U32) (c : Usize)
    (ht : t.val.length = c.val) (hc : c.val ≤ 256) :
    edge_prices_loop0 lcost t c ⦃ r => r.val.length ≤ 256 ⦄ := by
  unfold edge_prices_loop0
  apply loop.spec_decr_nat (fun (_, k) => 256 - k.val)
    (fun (t', k) => t'.val.length = k.val ∧ k.val ≤ 256)
  · rintro ⟨t', k⟩ ⟨htk, hk⟩
    dsimp only
    unfold edge_prices_loop0.body
    split
    · try dsimp only
      split
      · step as ⟨x, hx⟩
        have hcap : t'.val.length < Usize.max := by scalar_tac
        step as ⟨t1, ht1⟩
        step as ⟨k1, hk1⟩
        try simp only [WP.spec_ok]
        refine ⟨by rw [ht1]; simp [htk, hk1], by scalar_tac, by scalar_tac⟩
      · simp only [WP.spec_ok]
        omega
    · simp only [WP.spec_ok]
      omega
  · exact ⟨ht, hc⟩

theorem edge_prices_inner_spec (lcost t : alloc.vec.Vec U32) (dp : U64) (len : Usize)
    (ht : t.val.length ≤ 7936) (hl : len.val = 3)
    (hdp : dp.val < 8589934592) :
    edge_prices_loop1_loop0 lcost t dp len ⦃ r => r.val.length ≤ t.val.length + 256 ⦄ := by
  unfold edge_prices_loop1_loop0
  apply loop.spec_decr_nat (fun (_, k) => 259 - k.val)
    (fun (t', k) => t'.val.length + 3 ≤ t.val.length + k.val ∧ 3 ≤ k.val ∧ k.val ≤ 259)
  · rintro ⟨t', k⟩ ⟨htk, hk0, hk1⟩
    dsimp only
    unfold edge_prices_loop1_loop0.body
    split
    · step as ⟨i, hi⟩
      try dsimp only
      split
      · step as ⟨x, hx⟩
        step as ⟨x1, hx1⟩
        have hx1v : x1.val = x.val := by rw [hx1]; exact cast_u32_u64 x
        have hxb : x.val < 4294967296 := by scalar_tac
        step as ⟨y, hy⟩
        step as ⟨y1, hy1⟩
        have hcap : t'.val.length < Usize.max := by scalar_tac
        step as ⟨t1, ht1⟩
        step as ⟨k1, hk1'⟩
        try simp only [WP.spec_ok]
        refine ⟨by rw [ht1]; simp only [List.length_append, List.length_singleton]; omega,
          by omega, by scalar_tac, by scalar_tac⟩
      · simp only [WP.spec_ok]
        omega
    · simp only [WP.spec_ok]
      omega
  · exact ⟨by omega, by omega, by omega⟩

theorem edge_prices_outer_spec (lcost dcost t : alloc.vec.Vec U32) (d : Usize)
    (ht : t.val.length ≤ 256 + 256 * d.val) (hd : d.val ≤ 30) :
    edge_prices_loop1 lcost dcost t d ⦃ r => r.val.length ≤ 7936 ⦄ := by
  unfold edge_prices_loop1
  apply loop.spec_decr_nat (fun (_, k) => 30 - k.val)
    (fun (t', k) => t'.val.length ≤ 256 + 256 * k.val ∧ k.val ≤ 30)
  · rintro ⟨t', k⟩ ⟨htk, hk⟩
    dsimp only
    unfold edge_prices_loop1.body
    split
    · try dsimp only
      split
      · step as ⟨x, hx⟩
        step as ⟨x1, hx1⟩
        have hx1v : x1.val = x.val := by rw [hx1]; exact cast_u32_u64 x
        step as ⟨y, hy⟩
        step as ⟨y1, hy1⟩
        have hy1v : y1.val = y.val := by rw [hy1]; exact cast_u32_u64 y
        have hxb : x.val < 4294967296 := by scalar_tac
        have hyb : y.val < 4294967296 := by scalar_tac
        step as ⟨dp, hdp⟩
        have hin := edge_prices_inner_spec lcost t' dp 3#usize (by omega) (by simp) (by omega)
        step as ⟨t1, ht1⟩
        step as ⟨k1, hk1⟩
        try simp only [WP.spec_ok]
        refine ⟨by omega, by scalar_tac, by scalar_tac⟩
      · simp only [WP.spec_ok]
        omega
    · simp only [WP.spec_ok]
      omega
  · exact ⟨ht, hd⟩

/-- The price table of a later pass: any table will do, its entries are only prices. -/
@[step]
theorem edge_prices_spec (lcost dcost : alloc.vec.Vec U32) :
    edge_prices lcost dcost ⦃ _ => True ⦄ := by
  unfold edge_prices
  have h0 := edge_prices_loop0_spec lcost (alloc.vec.Vec.with_capacity U32 7936#usize) 0#usize
    (by simp [alloc.vec.Vec.with_capacity]) (by simp)
  step as ⟨t1, ht1⟩
  have h1 := edge_prices_outer_spec lcost dcost t1 0#usize (by simp; omega) (by simp)
  step*

theorem u64_lt (x : U64) : x.val < 18446744073709551616 := by scalar_tac

theorem u32_lt (x : U32) : x.val < 4294967296 := by scalar_tac

theorem usize_succ (e : Usize) (n : ℕ) (he : e.val < n) (hn : n ≤ Usize.max) :
    e.val + 1 ≤ Usize.max := by omega

theorem hinted_body (data : List U8) (start stop size : ℕ)
    (hints : alloc.vec.Vec U64) (prices : alloc.vec.Vec U32) (dp : alloc.vec.Vec U64) (e : Usize)
    (hlen : dp.val.length = size + 1) (hpred : Predecessors data start stop dp.val)
    (hh : Edges.Edges data start stop hints.val) :
    optimal_hinted_loop.body hints prices dp e ⦃ r =>
      match r with
      | .done d => d.val.length = size + 1 ∧ Predecessors data start stop d.val
      | .cont (d, e') => (d.val.length = size + 1 ∧ Predecessors data start stop d.val) ∧
          e'.val = e.val + 1 ∧ e.val < hints.val.length ⦄ := by
  unfold optimal_hinted_loop.body
  try dsimp only
  split
  · rename_i hel'
    have hel : e.val < hints.val.length := by
      have := (UScalar.lt_equiv _ _).mp hel'
      simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length] at this
      exact this
    step as ⟨x, hx⟩
    have hok := Edges.lookup hh e.val hel
    have hxe : x = hints.val[e.val]! := by rw [hx, getElem!_pos hints.val e.val hel]
    rw [← hxe] at hok
    have hxb : x.val < 18446744073709551616 := by scalar_tac
    have hidx := Edges.index_lt x
    have hlow := Edges.low_lt x
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    have hi2v : i2.val = Edges.index x := by
      rw [hi2, Hints.cast_usize _ (by unfold Edges.index at hidx; omega), hi1]
      rfl
    step as ⟨i3, hi3⟩
    step as ⟨i4, hi4⟩
    step as ⟨c, hc⟩
    step as ⟨low, hlowv⟩
    have hlowE : low.val = Edges.low x := by rw [hlowv]; rfl
    step as ⟨i5, hi5⟩
    step as ⟨i6, hi6⟩
    have hi6v : i6.val = low.val / 65536 := by
      rw [hi6, Hints.cast_usize _ (by rw [hi5]; omega), hi5]
    step as ⟨j, hj⟩
    have hhl : hints.val.length ≤ Usize.max := by scalar_tac
    have he1b : e.val + 1 ≤ Usize.max := usize_succ e _ hel hhl
    clear hi1 hi2 hi3 hi4 hlowv hi5 hi6 hxe hx
    split
    · rename_i hjl'
      have hjl : j.val < dp.val.length := by
        have := (UScalar.lt_equiv _ _).mp hjl'
        simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length] at this
        exact this
      split
      · step as ⟨i9, hi9⟩
        step as ⟨i10, hi10⟩
        step as ⟨i11, hi11⟩
        step as ⟨i12, hi12⟩
        have hi12v : i12.val = i11.val := by rw [hi12]; exact cast_u32_u64 i11
        have hi10b : i10.val < 4294967296 := by
          have := u64_lt i9
          rw [hi10]; unfold Cells.cost; omega
        have hi11b : i11.val < 4294967296 := u32_lt i11
        step as ⟨cost, hcost⟩
        have hjb : j.val < dp.val.length := hjl
        step as ⟨old, hold⟩
        have holdE : old = dp.val[j.val]! := by rw [hold, getElem!_pos dp.val j.val hjb]
        step as ⟨i13, hi13⟩
        have hi13b : i13.val < 4294967296 := by
          have := u64_lt old
          omega
        split
        · rename_i hlt'
          have hlt : cost.val < i13.val := (UScalar.lt_equiv _ _).mp hlt'
          step as ⟨i14, hi14⟩
          step as ⟨v, hv⟩
          have hvv : v.val = cost.val * 4294967296 + low.val := by omega
          step
          have hxb := x_post1
          obtain ⟨xa, xb⟩ := x
          simp only at hxb
          step as ⟨e1, he1⟩
          try simp only [WP.spec_ok]
          refine ⟨by rw [hxb]; simp [hlen], ?_, he1, hel⟩
          rw [hxb, alloc.vec.Vec.set_val_eq]
          apply pred_set hpred j.val v
          intro _
          have hcl : Cells.len v = low.val / 65536 := by
            unfold Cells.len; rw [hvv]; omega
          have hcd : Cells.dist v = low.val % 65536 := by
            unfold Cells.dist; rw [hvv]; omega
          rw [hcl, hcd]
          have hji : j.val - low.val / 65536 = Edges.index x := by omega
          refine ⟨by omega, ?_⟩
          rw [hji, hlowE]
          unfold Edges.EdgeOk at hok
          exact hok
        · step
          have hxb := x_post1
          obtain ⟨xa, xb⟩ := x
          simp only at hxb
          step as ⟨e1, he1⟩
          try simp only [WP.spec_ok]
          refine ⟨by rw [hxb]; simp [hlen], ?_, he1, hel⟩
          rw [hxb, alloc.vec.Vec.set_val_eq]
          apply pred_set hpred j.val old
          intro hj0
          rw [holdE]
          exact hpred j.val hj0 hjb
      · step as ⟨e1, he1⟩
        try simp only [WP.spec_ok]
        exact ⟨hlen, hpred, he1, hel⟩
    · step as ⟨e1, he1⟩
      try simp only [WP.spec_ok]
      exact ⟨hlen, hpred, he1, hel⟩
  · simp only [WP.spec_ok]
    exact ⟨hlen, hpred⟩

theorem hinted_loop (data : List U8) (start stop size : ℕ)
    (hints : alloc.vec.Vec U64) (prices : alloc.vec.Vec U32) (dp : alloc.vec.Vec U64) (e : Usize)
    (hlen : dp.val.length = size + 1) (hpred : Predecessors data start stop dp.val)
    (hh : Edges.Edges data start stop hints.val) :
    optimal_hinted_loop hints dp prices e ⦃ r =>
      r.val.length = size + 1 ∧ Predecessors data start stop r.val ⦄ := by
  unfold optimal_hinted_loop
  apply loop.spec_decr_nat (fun (_, k) => hints.val.length - k.val)
    (fun (d, _) => d.val.length = size + 1 ∧ Predecessors data start stop d.val)
  · rintro ⟨d, k⟩ ⟨hl, hp⟩
    refine WP.spec_mono (hinted_body data start stop size hints prices d k hl hp hh) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨d', k'⟩ := state
        obtain ⟨hinv, hk, hkl⟩ := hr
        exact ⟨hinv, by change hints.val.length - k'.val < hints.val.length - k.val; omega⟩
  · exact ⟨hlen, hpred⟩

@[step]
theorem optimal_hinted_correct (data : Aeneas.Std.Slice U8) (start stop : Usize)
    (hints : alloc.vec.Vec U64) (lcost dcost : alloc.vec.Vec U32)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length)
    (hsize : stop.val - start.val ≤ 32768) (hprices : Prices lcost.val dcost.val)
    (hh : Edges.Edges data.val start.val stop.val hints.val) :
    optimal_hinted data start stop hints lcost dcost ⦃ r =>
      Runs data.val stop.val start.val stop.val r.lengths.val r.distances.val ⦄ := by
  unfold optimal_hinted
  step as ⟨size, hsz⟩
  have hrow := literal_row_correct data.val start.val stop.val size (by omega)
  step as ⟨dp, hlen, hpred⟩
  step as ⟨prices⟩
  have hl := hinted_loop data.val start.val stop.val size.val hints prices dp 0#usize hlen hpred hh
  step as ⟨dp1, hlen1, hpred1⟩
  have htr := trace_correct data.val start.val stop.val size.val size dp1 rfl
    (by omega) (by omega) hlen1 hpred1
  step*

end Gzip.Proofs.Dp
