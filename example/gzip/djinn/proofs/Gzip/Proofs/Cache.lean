import Gzip.Proofs.Matches
import Gzip.Proofs.Cells

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Matches

namespace Gzip.Proofs.Cache

/-- The byte swap never fails (the walk only uses its result as a guide). -/
@[step]
theorem swap8_spec (x : U64) : swap8 x ⦃ _ => True ⦄ := by
  unfold swap8
  step*

@[step]
theorem word_below_spec (x y : U64) : word_below x y ⦃ _ => True ⦄ := by
  unfold word_below
  step*

@[step]
theorem byte_below_spec (a b : Aeneas.Std.Slice U8) (m limit : Usize) :
    byte_below a b m limit ⦃ _ => True ⦄ := by
  unfold byte_below
  split
  · dsimp only
    split
    · split
      · step*
      · simp
    · simp
  · simp

/-- The comparison's main loop with the walk's direction: eight bytes per step; the length is
the agreeing run as for `match_from`, the direction is unconstrained. -/
theorem dir_body (a b : Aeneas.Std.Slice U8) (limit n : Usize) (lo : ℕ)
    (hla : limit.val ≤ a.val.length) (hlb : limit.val ≤ b.val.length)
    (hf : lo ≤ n.val) (hn : n.val ≤ limit.val) (hr : SRun a.val b.val lo n.val) :
    match_dir_loop.body limit a b n ⦃ r =>
      match r with
      | .done m => lo ≤ m.1.val ∧ m.1.val ≤ limit.val ∧ SRun a.val b.val lo m.1.val
      | .cont m => m.val = n.val + 8 ∧ lo ≤ m.val ∧ m.val ≤ limit.val ∧
          SRun a.val b.val lo m.val ⦄ := by
  unfold match_dir_loop.body
  step as ⟨rem, hrem⟩
  split
  · rename_i h8
    have h8' : n.val + 8 ≤ limit.val := by scalar_tac
    step as ⟨x, hx⟩
    step as ⟨y, hy⟩
    split
    · have hp7 := prefix7_run a.val b.val lo n.val x y hr hx hy
      step as ⟨pv, hpv3, hpv⟩
      step as ⟨m, hm⟩
      step as ⟨w, _⟩
      try simp only [WP.spec_ok]
      refine ⟨by omega, by omega, ?_⟩
      rw [hm]
      exact hpv
    · rename_i hne
      have hv : x.val = y.val := by simpa using hne
      rw [hx, hy] at hv
      have hl := W4_lt a.val n.val
      have hl' := W4_lt b.val n.val
      have hw0 : W4 a.val n.val = W4 b.val n.val := by omega
      have hw4 : W4 a.val (n.val + 4) = W4 b.val (n.val + 4) := by omega
      have hr4 := srun_word hr hw0
      have hr8 := srun_word hr4 hw4
      step as ⟨n1, hn1⟩
      refine ⟨hn1, by omega, by omega, ?_⟩
      rw [hn1]
      simpa only [Nat.add_assoc] using hr8
  · have ht := tail_spec a b n limit lo hla hlb hf hn hr
    step as ⟨m, hm1, hm2, hm3⟩
    step as ⟨w, _⟩
    try simp only [WP.spec_ok]
    exact ⟨hm1, hm2, hm3⟩

theorem dir_loop (a b : Aeneas.Std.Slice U8) (limit n : Usize) (lo : ℕ)
    (hla : limit.val ≤ a.val.length) (hlb : limit.val ≤ b.val.length)
    (hf : lo ≤ n.val) (hn : n.val ≤ limit.val) (hr : SRun a.val b.val lo n.val) :
    match_dir_loop limit a b n ⦃ m =>
      lo ≤ m.1.val ∧ m.1.val ≤ limit.val ∧ SRun a.val b.val lo m.1.val ⦄ := by
  unfold match_dir_loop
  apply loop.spec_decr_nat (fun m => limit.val - m.val)
    (fun m => lo ≤ m.val ∧ m.val ≤ limit.val ∧ SRun a.val b.val lo m.val)
  · intro m hm
    refine WP.spec_mono (dir_body a b limit m lo hla hlb hm.1 hm.2.1 hm.2.2) ?_
    intro r hr'
    cases r with
    | done m => exact hr'
    | cont m' =>
        obtain ⟨heq, hf', hb', hrun⟩ := hr'
        exact ⟨⟨hf', hb', hrun⟩, by omega⟩
  · exact ⟨hf, hn, hr⟩

/-- The walk's comparison from `lb` on, with its direction: at least `lb`, and the bytes from
`lb` on agree (as `Matches.from_spec`). -/
@[step]
theorem match_dir_spec (data : Aeneas.Std.Slice U8) (p q lb limit : Usize)
    (hq : q.val ≤ p.val) (hl : p.val + limit.val ≤ data.val.length) :
    match_dir data p q lb limit ⦃ r =>
      lb.val ≤ r.1.val ∧ RunFrom data.val p.val q.val lb.val r.1.val ⦄ := by
  unfold match_dir
  step as ⟨i, hi⟩
  have hsub := core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    ({ start := p, «end» := i } : core.ops.range.Range Usize) data (by simp; scalar_tac) (by simp; scalar_tac)
  step as ⟨a, ha1, ha2⟩
  have halen : limit.val ≤ a.val.length := by
    have h := ha2
    simp only [Slice.length] at h
    omega
  have hap : ∀ k, k < limit.val → a.val[k]! = data.val[p.val + k]! := by
    intro k hk
    rw [ha1]
    exact Gzip.Proofs.Crc.slice_getElem! data.val p.val i.val k (by omega) (by omega)
  step as ⟨j, hj⟩
  have hsub' := core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    ({ start := q, «end» := j } : core.ops.range.Range Usize) data (by simp; scalar_tac) (by simp; scalar_tac)
  step as ⟨b, hb1, hb2⟩
  have hblen : limit.val ≤ b.val.length := by
    have h := hb2
    simp only [Slice.length] at h
    omega
  have hbp : ∀ k, k < limit.val → b.val[k]! = data.val[q.val + k]! := by
    intro k hk
    rw [hb1]
    exact Gzip.Proofs.Crc.slice_getElem! data.val q.val j.val k (by omega) (by omega)
  split
  · simp only [WP.spec_ok]
    exact ⟨Nat.le_refl _, by intro k h1 h2; omega⟩
  · rename_i hlt
    have hlt' : lb.val < limit.val := by scalar_tac
    have hfl := dir_loop a b limit lb lb.val halen hblen (Nat.le_refl _) (by omega)
      (by intro k h1 h2; omega)
    refine WP.spec_mono hfl ?_
    rintro ⟨m, w⟩ ⟨hm1, hm2, hm3⟩
    refine ⟨hm1, ?_⟩
    intro k hk0 hk
    rw [← hap k (by omega), ← hbp k (by omega)]
    exact hm3 k hk0 hk

/-- The insertion-only walk's comparison: at least `lb` (its value is only a guide). -/
@[step]
theorem dir_cached_spec (data : Aeneas.Std.Slice U8) (p q lb limit skip : Usize)
    (hq : q.val ≤ p.val) (hl : p.val + limit.val ≤ data.val.length) :
    dir_cached data p q lb limit skip ⦃ r => lb.val ≤ r.1.val ⦄ := by
  unfold dir_cached
  have hm := match_dir_spec data p q lb limit hq hl
  have hm' : match_dir data p q lb limit ⦃ r => lb.val ≤ r.1.val ⦄ :=
    WP.spec_mono hm (fun r h => h.1)
  split
  · step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    split
    · step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      split
      · simp only [WP.spec_ok]
        scalar_tac
      · exact hm'
    · exact hm'
  · exact hm'

@[step]
theorem cache_skip_spec (i len : Usize) (dp : alloc.vec.Vec U64) :
    cache_skip i len dp ⦃ _ => True ⦄ := by
  unfold cache_skip
  have hr : (if len > 0#usize then
      if len <= 258#usize then len - 1#usize else ok 0#usize
      else ok 0#usize) ⦃ remaining => remaining.val ≤ 257 ⦄ := by
    split
    · split
      · step*
      · simp
    · simp
  step as ⟨remaining, hremaining⟩
  split
  · step as ⟨i3, hi3⟩
    split
    · step as ⟨i4, hi4⟩
      have hi4b : i4.val < dp.val.length := by
        simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length] at hi3
        scalar_tac
      step as ⟨cell, hcell⟩
      step as ⟨i5, hi5⟩
      split
      · step as ⟨dist, hdist⟩
        split
        · step as ⟨i6, hi6⟩
          step*
        · step*
      · step*
    · step*
  · step*

end Gzip.Proofs.Cache
