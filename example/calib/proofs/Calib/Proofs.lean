/-  Proofs.lean — the implementer's file (LLM-owned in the real pipeline).
    Written by hand here to calibrate proof effort on Aeneas. -/
import Aeneas
import Calib.Spec
import Calib.Code.Funs

open Aeneas Std Result
open Calib.Spec

namespace Calib.Proofs

/-! ## perm -/

theorem perm.exists :
    ∀ (list : List I32), perm_pre list → ∃ t, perm_spec list t := by
  intro list _
  exact ⟨list, trivial, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- The count-based relation is `List.Perm`. -/
theorem perm_of_spec (l t : List I32) (h : perm_spec l t) : t.Perm l := by
  obtain ⟨_, _, h1, h2⟩ := h
  rw [List.perm_iff_count]
  intro x
  by_cases hx : x ∈ l
  · have := h1 x hx; omega
  · by_cases ht : x ∈ t
    · have := h2 x ht; omega
    · simp [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr ht]

theorem spec_of_perm (l t : List I32) (h : t.Perm l) : perm_spec l t := by
  refine ⟨trivial, ?_, ?_, ?_⟩
  · simp [h.length_eq]
  · intro x _; simp [h.count_eq]
  · intro x _; simp [h.count_eq]

/-! ## sorted-ness helpers -/

/-- `l` is sorted on positions `[0, n)`. -/
def SortedBelow (l : List I32) (n : Nat) : Prop :=
  ∀ a b, a < b → b < n → (l[a]!).val ≤ (l[b]!).val

/-- The adjacent-comparison form used by the spec implies pairwise order. -/
theorem le_of_adj (v : List I32)
    (h : ∀ i : ℤ, 0 ≤ i → i < (v.length : ℤ) - 1 →
           (v[i.toNat]!).val ≤ (v[(i + 1).toNat]!).val) :
    ∀ k i, i + k < v.length → (v[i]!).val ≤ (v[i + k]!).val := by
  intro k
  induction k with
  | zero => intro i _; simp
  | succ k ih =>
    intro i hi
    have h1 := ih i (by omega)
    have h2 := h (i + k) (by omega) (by omega)
    have e1 : ((i : ℤ) + (k : ℤ)).toNat = i + k := by omega
    have e2 : ((i : ℤ) + (k : ℤ) + 1).toNat = i + k + 1 := by omega
    rw [e1, e2] at h2
    have : i + (k + 1) = i + k + 1 := by omega
    rw [this]
    omega

theorem sortedLE_of_adj (v : List I32)
    (h : ∀ i : ℤ, 0 ≤ i → i < (v.length : ℤ) - 1 →
           (v[i.toNat]!).val ≤ (v[(i + 1).toNat]!).val) :
    v.SortedLE := by
  rw [List.sortedLE_iff_getElem_le_getElem_of_le]
  intro i j hi hj hij
  have := le_of_adj v h (j - i) i (by omega)
  have e : i + (j - i) = j := by omega
  rw [e] at this
  rw [IScalar.le_equiv]
  simp only [getElem!_pos, hi, hj] at this
  exact this

theorem adj_of_sortedBelow (v : List I32) (h : SortedBelow v v.length) :
    ∀ i : ℤ, 0 ≤ i → i < (v.length : ℤ) - 1 →
      (v[i.toNat]!).val ≤ (v[(i + 1).toNat]!).val := by
  intro i h0 h1
  have e : (i + 1).toNat = i.toNat + 1 := by omega
  rw [e]
  exact h i.toNat (i.toNat + 1) (by omega) (by omega)

/-! ## sort: the specification-level obligations -/

theorem sort.unambiguous :
    ∀ (v_old o₁ o₂ : List I32),
      sort_spec v_old o₁ → sort_spec v_old o₂ → o₁ = o₂ := by
  intro v_old o₁ o₂ ⟨_, hp₁, hs₁⟩ ⟨_, hp₂, hs₂⟩
  have p₁ := perm_of_spec _ _ hp₁
  have p₂ := perm_of_spec _ _ hp₂
  exact List.Perm.eq_of_sortedLE (sortedLE_of_adj _ hs₁) (sortedLE_of_adj _ hs₂)
    (p₁.trans p₂.symm)

theorem sort.wf :
    ∀ (v_old v : List I32), sort_spec v_old v →
      ∀ i : ℤ, 0 ≤ i → i < (v.length : ℤ) - 1 →
        (0 ≤ i ∧ i < (v.length : ℤ)) ∧ (0 ≤ i + 1 ∧ i + 1 < (v.length : ℤ)) := by
  intro _ _ _ i h0 h1
  omega

/-! ## sort: the implementation -/

/-- Sorted on `[0, i]` except that position `j` is skipped. -/
def SortedExcept (l : List I32) (i j : Nat) : Prop :=
  ∀ a b, a < b → b ≤ i → a ≠ j → b ≠ j → (l[a]!).val ≤ (l[b]!).val

/-- Position `j` is at most every position in `(j, i]`. -/
def AboveJ (l : List I32) (i j : Nat) : Prop :=
  ∀ b, j < b → b ≤ i → (l[j]!).val ≤ (l[b]!).val

/-- Invariant of the inner (insertion) loop, relative to the vector `v0`
    at loop entry and the outer index `i`. -/
def InnerInv (v0 : alloc.vec.Vec I32) (io : Nat) (v : alloc.vec.Vec I32) (j : Usize) : Prop :=
  v.length = v0.length ∧ j.val ≤ io ∧ io < v.length ∧ v.val.Perm v0.val ∧
  SortedExcept v.val io j.val ∧ AboveJ v.val io j.val

theorem swap_perm (l : List I32) (i j : Nat) (hi : i < l.length) (hj : j < l.length) :
    ((l.set i (l[j]'hj)).set j (l[i]'hi)).Perm l := by
  have := Array.perm_iff_toList_perm.mp
    (Array.swap_perm (xs := l.toArray) (i := i) (j := j) (by simpa) (by simpa))
  simpa using this

theorem val_getElem! (l : List I32) (k : Nat) (hk : k < l.length) :
    (l[k]!).val = (l[k]'hk).val := by
  rw [getElem!_pos l k hk]

theorem getElem!_swap (l : List I32) (i j k : Nat) (x y : I32) (hk : k < l.length) :
    ((l.set i x).set j y)[k]! = if k = j then y else if k = i then x else l[k]! := by
  have hk1 : k < ((l.set i x).set j y).length := by simpa
  rw [getElem!_pos _ k hk1, getElem!_pos l k hk]
  split_ifs with h1 h2
  · subst h1; simp
  · subst h2; rw [List.getElem_set_ne (Ne.symm h1)]; simp
  · rw [List.getElem_set_ne (Ne.symm h1), List.getElem_set_ne (Ne.symm h2)]

theorem inner_body_spec (v0 : alloc.vec.Vec I32) (io : Nat)
    (v : alloc.vec.Vec I32) (j : Usize) (hinv : InnerInv v0 io v j) :
    sort_loop0_loop0.body v j ⦃ r =>
      match r with
      | .done v' => v'.length = v0.length ∧ v'.val.Perm v0.val ∧ SortedBelow v'.val (io + 1)
      | .cont x' => InnerInv v0 io x'.1 x'.2 ∧ x'.2.val < j.val ⦄ := by
  obtain ⟨hlen, hji, hio, hperm, hse, hab⟩ := hinv
  have hj : j.val < v.length := by omega
  unfold sort_loop0_loop0.body
  step*
  · -- bounds side-goal: the length of `v.set i i2`
    subst index_mut_back_post; simp; omega
  · -- cont: swap positions i = j-1 and j, continue with j-1
    have hgt : i1 > i2 := by assumption
    have hi : i.val < v.length := by omega
    subst i1_post i2_post t_post index_mut_back_post index_mut_back1_post
    have ei := val_getElem! v.val i.val hi
    have ej := val_getElem! v.val j.val hj
    have hij : i.val ≠ j.val := by omega
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hlen]
    · omega
    · simp; omega
    · simp only [alloc.vec.Vec.set_val_eq]
      exact (swap_perm v.val i.val j.val hi hj).trans hperm
    · intro a b hab' hb hane hbne
      have ha : a < v.length := by omega
      have hb' : b < v.length := by omega
      simp only [alloc.vec.Vec.set_val_eq, getElem!_swap _ _ _ _ _ _ ha, getElem!_swap _ _ _ _ _ _ hb']
      by_cases haj : a = j.val
      · subst haj
        have hbj : b ≠ j.val := by omega
        simp only [ite_true, if_neg hbj, if_neg hbne]
        have := hse i.val b (by omega) hb (by omega) hbj
        omega
      · simp only [if_neg haj, if_neg hane]
        by_cases hbj : b = j.val
        · subst hbj
          simp only [ite_true]
          have := hse a i.val (by omega) (by omega) haj hij
          omega
        · simp only [if_neg hbj, if_neg hbne]
          exact hse a b hab' hb haj hbj
    · intro b hb hbio
      have hb' : b < v.length := by omega
      simp only [alloc.vec.Vec.set_val_eq, getElem!_swap _ _ _ _ _ _ hi, getElem!_swap _ _ _ _ _ _ hb']
      simp only [if_neg hij, ite_true]
      by_cases hbj : b = j.val
      · subst hbj
        simp only [ite_true, IScalar.lt_equiv] at hgt ⊢
        omega
      · simp only [if_neg hbj, if_neg (Nat.ne_of_gt hb)]
        have := hab b (by omega) hbio
        omega
    · omega
  · -- done: v[j-1] ≤ v[j]; the prefix [0, io] is sorted
    have hle : ¬ i1 > i2 := by assumption
    have hi : i.val < v.length := by omega
    subst i1_post i2_post
    have ei := val_getElem! v.val i.val hi
    have ej := val_getElem! v.val j.val hj
    simp only [gt_iff_lt, _root_.not_lt, IScalar.le_equiv] at hle
    refine ⟨hlen, hperm, ?_⟩
    intro a b hab' hb
    by_cases haj : a = j.val
    · subst haj
      exact hab b hab' (by omega)
    · by_cases hbj : b = j.val
      · subst hbj
        by_cases hai : a = i.val
        · subst hai; omega
        · have := hse a i.val (by omega) (by omega) haj (by omega)
          omega
      · exact hse a b hab' (by omega) haj hbj
  · -- done: j = 0
    have h0 : ¬ j > 0#usize := by assumption
    have hj0 : j.val = 0 := by scalar_tac
    refine ⟨hlen, hperm, ?_⟩
    intro a b hab' hb
    by_cases ha0 : a = j.val
    · subst ha0
      exact hab b hab' (by omega)
    · exact hse a b hab' (by omega) ha0 (by omega)

@[step]
theorem sort_loop0_loop0_spec (v : alloc.vec.Vec I32) (i : Usize)
    (hi : i.val < v.length) (hs : SortedBelow v.val i.val) :
    sort_loop0_loop0 v i ⦃ v' =>
      v'.length = v.length ∧ v'.val.Perm v.val ∧ SortedBelow v'.val (i.val + 1) ⦄ := by
  unfold sort_loop0_loop0
  apply loop.spec_decr_nat (fun (_, j) => j.val) (fun (v', j) => InnerInv v i.val v' j)
  · rintro ⟨v', j⟩ hinv
    simp only at hinv ⊢
    refine Aeneas.Std.WP.spec_mono (inner_body_spec v i.val v' j hinv) ?_
    intro r hr
    cases r <;> exact hr
  · refine ⟨rfl, Nat.le_refl _, hi, List.Perm.refl _, ?_, ?_⟩
    · intro a b hab hb _ hbne
      exact hs a b hab (by omega)
    · intro b hb hbi; omega

/-- Invariant of the outer loop relative to the original vector `v0`. -/
def OuterInv (v0 : alloc.vec.Vec I32) (v : alloc.vec.Vec I32) (i : Usize) : Prop :=
  v.length = v0.length ∧ v.val.Perm v0.val ∧ SortedBelow v.val i.val

@[step]
theorem sort_loop0_spec (v : alloc.vec.Vec I32) (n i : Usize)
    (hn : n.val = v.length) (hs : SortedBelow v.val i.val) :
    sort_loop0 v n i ⦃ v' =>
      v'.length = v.length ∧ v'.val.Perm v.val ∧ SortedBelow v'.val v.length ⦄ := by
  unfold sort_loop0
  apply loop.spec_decr_nat (fun (_, i') => v.length - i'.val) (fun (v', i') => OuterInv v v' i')
  · rintro ⟨v', i'⟩ ⟨hlen, hperm, hs'⟩
    unfold sort_loop0.body
    step*
    · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · omega
      · exact v1_post1.trans hperm
      · rw [i1_post]; exact v1_post2
      · scalar_tac
    · have hge : n.val ≤ i'.val := by scalar_tac
      refine ⟨hlen, hperm, ?_⟩
      intro a b hab hb
      exact hs' a b hab (by omega)
  · exact ⟨rfl, List.Perm.refl _, hs⟩

theorem sort.impl_correct :
    ∀ (v : alloc.vec.Vec I32), sort_pre v.val →
      Calib.sort v ⦃ v' => sort_spec v.val v'.val ⦄ := by
  intro v _
  unfold Calib.sort
  step as ⟨ v', hlen, hperm, hs ⟩
  · intro a b hab hb; simp at hb; omega
  · refine ⟨trivial, spec_of_perm _ _ hperm, ?_⟩
    rw [← hlen] at hs
    exact adj_of_sortedBelow _ hs

/-! ## max -/

theorem max.unambiguous :
    ∀ (list : List I32) (r₁ r₂ : I32),
      max_spec list r₁ → max_spec list r₂ → r₁ = r₂ := by
  intro list r₁ r₂ ⟨_, h₁, hle₁⟩ ⟨_, h₂, hle₂⟩
  have a := hle₁ r₂ h₂
  have b := hle₂ r₁ h₁
  rw [IScalar.eq_equiv]
  omega

theorem max.ens_0 :
    ∀ (list : List I32) (r : I32), max_spec list r → r ∈ list := by
  intro _ _ h
  exact h.2.1

def MaxBelow (l : List I32) (r : I32) (n : Nat) : Prop :=
  ∀ k, k < n → (l[k]!).val ≤ r.val

@[step]
theorem max_loop_spec (list : Aeneas.Std.Slice I32) (r : I32) (i : Usize)
    (hr : r ∈ list.val) (hm : MaxBelow list.val r i.val) :
    max_loop list r i ⦃ r' => r' ∈ list.val ∧ ∀ x, x ∈ list.val → x.val ≤ r'.val ⦄ := by
  unfold max_loop
  apply loop.spec_decr_nat (fun (_, i') => list.length - i'.val)
    (fun (r', i') => r' ∈ list.val ∧ MaxBelow list.val r' i'.val)
  · rintro ⟨r', i'⟩ ⟨hr', hm'⟩
    unfold max_loop.body
    step*
    · have hlt : i' < list.len := by assumption
      rw [UScalar.lt_equiv, Slice.len_val] at hlt
      split
      · step*
        have hgt : i2 > r' := by assumption
        simp only [gt_iff_lt, IScalar.lt_equiv] at hgt
        refine ⟨?_, ?_, ?_⟩
        · subst i2_post; exact List.getElem_mem _
        · intro k hk
          by_cases hki : k = i'.val
          · subst hki; rw [val_getElem! _ _ hlt]; subst i2_post; omega
          · have := hm' k (by omega); omega
        · scalar_tac
      · step*
        have hle : ¬ i2 > r' := by assumption
        simp only [gt_iff_lt, _root_.not_lt, IScalar.le_equiv] at hle
        refine ⟨hr', ?_, ?_⟩
        · intro k hk
          by_cases hki : k = i'.val
          · subst hki; rw [val_getElem! _ _ hlt]; subst i2_post; omega
          · exact hm' k (by omega)
        · scalar_tac
    · have hge : ¬ i' < list.len := by assumption
      rw [UScalar.lt_equiv, Slice.len_val] at hge
      refine ⟨hr', ?_⟩
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
      simp only [Slice.length] at hge
      have := hm' k (by omega)
      rw [val_getElem! _ _ hk] at this
      exact this
  · exact ⟨hr, hm⟩

theorem max.impl_correct :
    ∀ (list : Aeneas.Std.Slice I32), max_pre list.val →
      Calib.max list ⦃ r => max_spec list.val r ⦄ := by
  intro list hpre
  unfold Calib.max
  unfold max_pre at hpre
  step as ⟨ r, hr ⟩
  step as ⟨ r', hmem, hmax ⟩
  · subst hr; exact List.getElem_mem _
  · intro k hk
    simp at hk
    have : k = 0 := by omega
    subst this
    rw [val_getElem! _ _ (by omega)]
    subst hr; omega
  · exact ⟨hpre, hmem, hmax⟩

end Calib.Proofs
