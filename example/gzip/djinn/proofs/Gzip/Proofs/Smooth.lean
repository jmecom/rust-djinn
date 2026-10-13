import Gzip.Proofs.Chains

open Aeneas Std Result
open Gzip.solution

set_option maxHeartbeats 2000000

namespace Gzip.Proofs.Smooth

/-! The smoothed frequencies `fit_tables` may fit its codes to: only termination and the
    length of the result matter, since a code fitted to them is checked against the true
    frequencies like any other. -/

@[step]
theorem long_run_spec (symbol stride : Usize) : long_run symbol stride ⦃ _ => True ⦄ := by
  unfold long_run
  split <;> simp

@[step]
theorem collapsing_spec (stride sum : Usize) :
    collapsing stride sum ⦃ r => r = true → 3 ≤ stride.val ⦄ := by
  unfold collapsing
  split
  · try simp only [WP.spec_ok]
    intro _
    scalar_tac
  · split
    · try simp only [WP.spec_ok]
      intro _
      scalar_tac
    · simp

@[step]
theorem capped_at_spec (c : alloc.vec.Vec Usize) (i : Usize) :
    capped_at c i ⦃ r => r.val ≤ 1048576 ⦄ := by
  unfold capped_at
  try dsimp only
  repeat' (first | step | split | simp only [WP.spec_ok])
  all_goals (try simp_all)
  all_goals scalar_tac

@[step]
theorem run_ends_spec (c : alloc.vec.Vec Usize) (i length symbol : Usize) :
    run_ends c i length symbol ⦃ _ => True ⦄ := by
  unfold run_ends
  try dsimp only
  repeat' (first | step | split | simp only [WP.spec_ok])

@[step]
theorem stretch_ends_spec (c : alloc.vec.Vec Usize) (good : alloc.vec.Vec Bool) (i length limit : Usize) :
    stretch_ends c good i length limit ⦃ _ => True ⦄ := by
  unfold stretch_ends
  try dsimp only
  repeat' (first | step | split | simp only [WP.spec_ok])

/-! ### Writing a run of entries -/

theorem mark_good_body (i stride : Usize) (out : alloc.vec.Vec Bool) (k : Usize) :
    mark_good_loop.body i stride out k ⦃ r =>
      match r with
      | .done out' => out'.val.length = out.val.length
      | .cont (out', k') => out'.val.length = out.val.length ∧ k'.val = k.val + 1 ∧
          k'.val ≤ stride.val ⦄ := by
  unfold mark_good_loop.body
  try dsimp only
  repeat' (first | step | split | simp only [WP.spec_ok])
  all_goals (try obtain ⟨_, back⟩ := out1)
  all_goals (try dsimp only at *)
  repeat' (first | step | split | simp only [WP.spec_ok])
  all_goals (try simp_all [alloc.vec.Vec.set_val_eq, List.length_set])
  all_goals scalar_tac

@[step]
theorem mark_good_loop_spec (i stride : Usize) (out : alloc.vec.Vec Bool) (k : Usize)
    (hk : k.val ≤ stride.val) :
    mark_good_loop i stride out k ⦃ r => r.val.length = out.val.length ⦄ := by
  unfold mark_good_loop
  apply loop.spec_decr_nat (fun (_, k') => stride.val - k'.val)
    (fun (out', k') => out'.val.length = out.val.length ∧ k'.val ≤ stride.val)
  · rintro ⟨out', k'⟩ ⟨hl, hk'⟩
    refine WP.spec_mono (mark_good_body i stride out' k') ?_
    intro r hr
    cases r with
    | done o => exact hr.trans hl
    | cont state =>
        obtain ⟨o, j⟩ := state
        obtain ⟨h1, h2, h3⟩ := hr
        exact ⟨⟨h1.trans hl, h3⟩, by change stride.val - j.val < stride.val - k'.val; omega⟩
  · exact ⟨rfl, hk⟩

@[step]
theorem mark_good_spec (good : alloc.vec.Vec Bool) (i stride : Usize) :
    mark_good good i stride ⦃ r => r.val.length = good.val.length ⦄ := by
  unfold mark_good
  exact mark_good_loop_spec i stride good 0#usize (by simp)

theorem fill_stretch_body (i stride value : Usize) (out : alloc.vec.Vec Usize) (k : Usize) :
    fill_stretch_loop.body i stride value out k ⦃ r =>
      match r with
      | .done out' => out'.val.length = out.val.length
      | .cont (out', k') => out'.val.length = out.val.length ∧ k'.val = k.val + 1 ∧
          k'.val ≤ stride.val ⦄ := by
  unfold fill_stretch_loop.body
  try dsimp only
  repeat' (first | step | split | simp only [WP.spec_ok])
  all_goals (try obtain ⟨_, back⟩ := out1)
  all_goals (try dsimp only at *)
  repeat' (first | step | split | simp only [WP.spec_ok])
  all_goals (try simp_all [alloc.vec.Vec.set_val_eq, List.length_set])
  all_goals scalar_tac

@[step]
theorem fill_stretch_loop_spec (i stride value : Usize) (out : alloc.vec.Vec Usize) (k : Usize)
    (hk : k.val ≤ stride.val) :
    fill_stretch_loop i stride value out k ⦃ r => r.val.length = out.val.length ⦄ := by
  unfold fill_stretch_loop
  apply loop.spec_decr_nat (fun (_, k') => stride.val - k'.val)
    (fun (out', k') => out'.val.length = out.val.length ∧ k'.val ≤ stride.val)
  · rintro ⟨out', k'⟩ ⟨hl, hk'⟩
    refine WP.spec_mono (fill_stretch_body i stride value out' k') ?_
    intro r hr
    cases r with
    | done o => exact hr.trans hl
    | cont state =>
        obtain ⟨o, j⟩ := state
        obtain ⟨h1, h2, h3⟩ := hr
        exact ⟨⟨h1.trans hl, h3⟩, by change stride.val - j.val < stride.val - k'.val; omega⟩
  · exact ⟨rfl, hk⟩

@[step]
theorem fill_stretch_spec (c : alloc.vec.Vec Usize) (i stride value : Usize) :
    fill_stretch c i stride value ⦃ r => r.val.length = c.val.length ⦄ := by
  unfold fill_stretch
  exact fill_stretch_loop_spec i stride value c 0#usize (by simp)

/-! ### The capped copy and its trailing zeros -/

theorem copy_body (freq : alloc.vec.Vec Usize) (n : Usize) (c : alloc.vec.Vec Usize) (i : Usize)
    (hn : n.val = freq.val.length) (hc : c.val.length = i.val) (hi : i.val ≤ n.val) :
    smoothed_loop0.body freq n c i ⦃ r =>
      match r with
      | .done c' => c'.val.length = n.val
      | .cont (c', i') => c'.val.length = i'.val ∧ i'.val ≤ n.val ∧ i'.val = i.val + 1 ⦄ := by
  unfold smoothed_loop0.body
  try dsimp only
  repeat' (first | step | split | simp only [WP.spec_ok])
  all_goals (try simp_all)
  all_goals scalar_tac

@[step]
theorem copy_loop (freq : alloc.vec.Vec Usize) (n : Usize) (c : alloc.vec.Vec Usize) (i : Usize)
    (hn : n.val = freq.val.length) (hc : c.val.length = i.val) (hi : i.val ≤ n.val) :
    smoothed_loop0 freq n c i ⦃ r => r.val.length = n.val ⦄ := by
  unfold smoothed_loop0
  apply loop.spec_decr_nat (fun (_, i') => n.val - i'.val)
    (fun (c', i') => c'.val.length = i'.val ∧ i'.val ≤ n.val)
  · rintro ⟨c', i'⟩ ⟨hc', hi'⟩
    refine WP.spec_mono (copy_body freq n c' i' hn hc' hi') ?_
    intro r hr
    cases r with
    | done o => exact hr
    | cont state =>
        obtain ⟨o, j⟩ := state
        obtain ⟨h1, h2, h3⟩ := hr
        exact ⟨⟨h1, h2⟩, by change n.val - j.val < n.val - i'.val; omega⟩
  · exact ⟨hc, hi⟩

theorem trailing_body (c : alloc.vec.Vec Usize) (length : Usize) (hl : length.val ≤ c.val.length) :
    smoothed_loop1.body c length ⦃ r =>
      match r with
      | .done l => l.val ≤ c.val.length
      | .cont l => l.val < length.val ⦄ := by
  unfold smoothed_loop1.body
  try dsimp only
  repeat' (first | step | split | simp only [WP.spec_ok])
  all_goals (try simp_all)
  all_goals scalar_tac

@[step]
theorem trailing_loop (c : alloc.vec.Vec Usize) (length : Usize) (hl : length.val ≤ c.val.length) :
    smoothed_loop1 c length ⦃ r => r.val ≤ c.val.length ⦄ := by
  unfold smoothed_loop1
  apply loop.spec_decr_nat (fun l => l.val) (fun l => l.val ≤ c.val.length)
  · intro l hl'
    refine WP.spec_mono (trailing_body c l hl') ?_
    intro r hr
    cases r with
    | done o => exact hr
    | cont l' => exact ⟨by omega, hr⟩
  · exact hl

/-! ### Marking the runs already cheap to send -/

theorem mark_body (c : alloc.vec.Vec Usize) (length i : Usize) (good : alloc.vec.Vec Bool)
    (symbol stride : Usize)
    (hlen : length.val ≤ 1024) (hg : good.val.length = length.val) (hs : stride.val ≤ i.val)
    (hi : i.val ≤ length.val + 1) :
    smoothed_loop2.body c length i good symbol stride ⦃ r =>
      match r with
      | .done g => g.val.length = length.val
      | .cont (i', g, _, s') => g.val.length = length.val ∧ s'.val ≤ i'.val ∧
          i'.val ≤ length.val + 1 ∧ i'.val = i.val + 1 ⦄ := by
  unfold smoothed_loop2.body
  try dsimp only
  repeat' (first | step | split | simp only [WP.spec_ok])
  all_goals (try simp_all)
  all_goals scalar_tac

@[step]
theorem mark_loop (c : alloc.vec.Vec Usize) (i length : Usize) (good : alloc.vec.Vec Bool)
    (symbol stride : Usize)
    (hlen : length.val ≤ 1024) (hg : good.val.length = length.val) (hs : stride.val ≤ i.val)
    (hi : i.val ≤ length.val + 1) :
    smoothed_loop2 c i length good symbol stride ⦃ r => r.val.length = length.val ⦄ := by
  unfold smoothed_loop2
  apply loop.spec_decr_nat (fun (i', _, _, _) => length.val + 1 - i'.val)
    (fun (i', g, _, s') => g.val.length = length.val ∧ s'.val ≤ i'.val ∧ i'.val ≤ length.val + 1)
  · rintro ⟨i', g, sy, s'⟩ ⟨hg', hs', hi'⟩
    refine WP.spec_mono (mark_body c length i' g sy s' hlen hg' hs' hi') ?_
    intro r hr
    cases r with
    | done o => exact hr
    | cont state =>
        obtain ⟨j, g2, sy2, s2⟩ := state
        obtain ⟨h1, h2, h3, h4⟩ := hr
        exact ⟨⟨h1, h2, h3⟩, by change length.val + 1 - j.val < length.val + 1 - i'.val; omega⟩
  · exact ⟨hg, hs, hi⟩

/-! ### Collapsing the stretches between them -/

theorem collapse_body (length : Usize) (good : alloc.vec.Vec Bool) (c : alloc.vec.Vec Usize)
    (i stride limit sum : Usize) (n : ℕ)
    (hlen : length.val ≤ 1024) (hc : c.val.length = n) (hs : stride.val ≤ i.val)
    (hsum : sum.val ≤ i.val * 1048576) (hi : i.val ≤ length.val + 1) :
    smoothed_loop3.body length good c i stride limit sum ⦃ r =>
      match r with
      | .done c' => c'.val.length = n
      | .cont (c', i', s', _, sum') => c'.val.length = n ∧ s'.val ≤ i'.val ∧
          sum'.val ≤ i'.val * 1048576 ∧ i'.val ≤ length.val + 1 ∧ i'.val = i.val + 1 ⦄ := by
  unfold smoothed_loop3.body
  try dsimp only
  repeat' (first | step | split | simp only [WP.spec_ok])
  all_goals (try simp_all)
  all_goals (first | scalar_tac | (exfalso; scalar_tac))

@[step]
theorem collapse_loop (c : alloc.vec.Vec Usize) (i length : Usize) (good : alloc.vec.Vec Bool)
    (stride limit sum : Usize)
    (hlen : length.val ≤ 1024) (hs : stride.val ≤ i.val)
    (hsum : sum.val ≤ i.val * 1048576) (hi : i.val ≤ length.val + 1) :
    smoothed_loop3 c i length good stride limit sum ⦃ r => r.val.length = c.val.length ⦄ := by
  unfold smoothed_loop3
  apply loop.spec_decr_nat (fun (_, i', _, _, _) => length.val + 1 - i'.val)
    (fun (c', i', s', _, sum') => c'.val.length = c.val.length ∧ s'.val ≤ i'.val ∧
      sum'.val ≤ i'.val * 1048576 ∧ i'.val ≤ length.val + 1)
  · rintro ⟨c', i', s', l', sum'⟩ ⟨hc', hs', hsum', hi'⟩
    refine WP.spec_mono (collapse_body length good c' i' s' l' sum' c.val.length hlen hc' hs' hsum' hi') ?_
    intro r hr
    cases r with
    | done o => exact hr
    | cont state =>
        obtain ⟨c2, j, s2, l2, sum2⟩ := state
        obtain ⟨h1, h2, h3, h4, h5⟩ := hr
        exact ⟨⟨h1, h2, h3, h4⟩, by change length.val + 1 - j.val < length.val + 1 - i'.val; omega⟩
  · exact ⟨rfl, hs, hsum, hi⟩

/-! ### The smoothed frequencies -/

@[step]
theorem smoothed_spec (freq : alloc.vec.Vec Usize) :
    smoothed freq ⦃ r => r.val.length = freq.val.length ⦄ := by
  unfold smoothed
  have h0 := copy_loop freq (alloc.vec.Vec.len freq) (alloc.vec.Vec.with_capacity Usize (alloc.vec.Vec.len freq))
    0#usize (by simp) (by simp [alloc.vec.Vec.with_capacity]) (by simp)
  step as ⟨c1, hc1⟩
  have hc1' : c1.val.length = freq.val.length := by rw [hc1]; simp
  have h1 := trailing_loop c1 (alloc.vec.Vec.len freq) (by rw [hc1']; simp)
  step as ⟨length, hlength⟩
  split
  · try simp only [WP.spec_ok]
    exact hc1'
  · split
    · try simp only [WP.spec_ok]
      exact hc1'
    · rename_i h0 hbig
      have hlen : length.val ≤ 1024 := by scalar_tac
      have hr := alloc.vec.Vec.resize_spec core.clone.CloneBool (alloc.vec.Vec.new Bool) length false
        (by rfl)
      step as ⟨good, hgood⟩
      have hgl : good.val.length = length.val := by
        rw [hgood]
        unfold List.resize
        simp [alloc.vec.Vec.new]
      step as ⟨symbol, _⟩
      have h2 := mark_loop c1 0#usize length good symbol 0#usize hlen hgl (by simp) (by simp)
      step as ⟨good1, hgood1⟩
      step as ⟨limit, _⟩
      have h3 := collapse_loop c1 0#usize length good1 0#usize limit 0#usize hlen (by simp) (by simp) (by simp)
      refine WP.spec_mono h3 ?_
      intro r hr
      rw [hr, hc1']

end Gzip.Proofs.Smooth
