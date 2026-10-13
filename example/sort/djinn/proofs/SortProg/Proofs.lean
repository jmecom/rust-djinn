/-  Proofs.lean — the implementer's file. Written once by `cargo djinn
    translate`, never overwritten. Replace every `sorry`; add any helper
    lemmas you need (loop invariants, bridging lemmas) in this file. -/
import Aeneas
import SortProg.Spec
import SortProg.Vocab
import SortProg.Code.Funs

open Aeneas Std Result
open SortProg.Spec
open Djinn.Vocab

namespace SortProg.Proofs

theorem perm_iff (a b : List I32) : perm_spec a b ↔ b.Perm a := by
  constructor
  · rintro ⟨_, _, h, h'⟩
    apply List.perm_iff_count.mpr
    intro x
    by_cases hx : x ∈ a
    · exact_mod_cast h x hx
    · by_cases hy : x ∈ b
      · exact_mod_cast h' x hy
      · simp [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr hy]
  · intro h
    exact ⟨trivial, by rw [h.length_eq], fun x _ => by rw [h.count_eq],
      fun x _ => by rw [h.count_eq]⟩

theorem ascending_iff (v : List I32) :
    (∀ i : ℤ, 0 ≤ i → i < (v.length : ℤ) - 1 →
      (v[i.toNat]!).val ≤ (v[(i+1).toNat]!).val) ↔ v.SortedLE := by
  rw [List.sortedLE_iff_isChain, List.isChain_iff_getElem]
  constructor
  · intro h i hi
    have hh := h (i : ℤ) (by omega) (by omega)
    simpa only [Int.toNat_natCast, show ((i : ℤ) + 1).toNat = i+1 by omega,
      getElem!_pos v i (by omega), getElem!_pos v (i+1) hi, IScalar.le_equiv] using hh
  · intro h i hi hb
    have h1 : i.toNat + 1 < v.length := by omega
    have hh := h i.toNat h1
    simpa only [show (i+1).toNat = i.toNat+1 by omega,
      getElem!_pos v i.toNat (by omega), getElem!_pos v (i.toNat+1) h1,
      IScalar.le_equiv] using hh

/-! ## perm -/

theorem perm.exists :
    ∀ (list : List I32), perm_pre list → ∃ t, perm_spec list t := by
  intro list _
  exact ⟨list, (perm_iff _ _).mpr (.refl _)⟩

/-! ## permsuperset -/

theorem permsuperset.exists :
    ∀ (list : List I32), permsuperset_pre list → ∃ t, permsuperset_spec list t := by
  intro list _
  exact ⟨list, trivial, _root_.le_refl _, fun _ _ => rfl⟩

/-! ## sort -/

theorem sort.unambiguous :
    ∀ (v_old : List I32) (o₁ : List I32) (o₂ : List I32),
      sort_spec v_old o₁ → sort_spec v_old o₂ → o₁ = o₂ := by
  intro v a b ha hb
  exact ((perm_iff _ _).mp ha.2.1 |>.trans ((perm_iff _ _).mp hb.2.1).symm).eq_of_sortedLE
    ((ascending_iff _).mp ha.2.2) ((ascending_iff _).mp hb.2.2)

theorem sort.wf :
    ∀ (v_old : List I32) (v : List I32),
      sort_spec v_old v →
      ∀ i : ℤ, 0 ≤ i → i < ((v.length : ℤ) - 1) → (0 ≤ i ∧ i < (v.length : ℤ)) ∧ (0 ≤ (i + 1) ∧ (i + 1) < (v.length : ℤ)) := by
  intros; omega

/-! ## max -/

theorem max.unambiguous :
    ∀ (list : List I32) (o₁ : I32) (o₂ : I32),
      max_spec list o₁ → max_spec list o₂ → o₁ = o₂ := by
  intro list a b ha hb
  apply (IScalar.eq_equiv _ _).mpr
  have := ha.2.2 b hb.2.1
  have := hb.2.2 a ha.2.1
  omega

theorem max.ens_0 :
    ∀ (list : List I32) (r : I32),
      max_spec list r → r ∈ list := by
  intro list r h
  exact h.2.1

@[step]
theorem insert_correct (list : Aeneas.Std.Slice I32) (n : Usize) (x : I32)
    (hb : n.val ≤ list.val.length) (hcap : n.val < Usize.max)
    (hs : (list.val.take n.val).Pairwise (fun a b => a.val ≤ b.val)) :
    solution.insert list n x ⦃ v =>
      v.val.Perm (list.val.take n.val ++ [x]) ∧
      v.val.Pairwise (fun a b => a.val ≤ b.val) ⦄ := by
  generalize he : n.val = size
  induction size using Nat.strong_induction_on generalizing n x with
  | h size ih =>
    unfold solution.insert
    step*
    · have hz : size = 0 := by scalar_tac
      simp [v_post, hz, alloc.vec.Vec.new]
    · have ht : list.val.take size = list.val.take k.val ++ [y] := by
        rw [show size = k.val + 1 by omega, List.take_succ_eq_append_getElem (by omega)]
        rw [y_post]
      rw [he, ht, List.pairwise_append] at hs
      have hsmall := hs.1
      have hlast : ∀ z ∈ list.val.take k.val, z.val ≤ y.val := by
        intro z hz; exact hs.2.2 z hz y (by simp)
      split
      · step*
        · have hl := out_post.length_eq
          simp only [List.length_append, List.length_take, List.length_singleton] at hl
          omega
        · rw [v_post, ht]
          constructor
          · simpa only [k_post] using out_post.append_right [x]
          · rw [List.pairwise_append]
            refine ⟨out_post1, by simp, ?_⟩
            intro z hz b hb
            simp only [List.mem_singleton] at hb
            subst b
            have hz := out_post.mem_iff.mp hz
            simp only [List.mem_append, List.mem_singleton] at hz
            rcases hz with hz | rfl
            · have := hlast z (by simpa [k_post] using hz)
              scalar_tac
            · scalar_tac
      · step*
        · have hl := out_post.length_eq
          simp only [List.length_append, List.length_take, List.length_singleton] at hl
          omega
        · rw [v_post, ht]
          constructor
          · apply (out_post.append_right [y]).trans
            simp only [← k_post, List.append_assoc]
            exact List.Perm.append_left _ (List.Perm.swap _ _ [])
          · rw [List.pairwise_append]
            refine ⟨out_post1, by simp, ?_⟩
            intro z hz b hb
            simp only [List.mem_singleton] at hb
            subst b
            have hz := out_post.mem_iff.mp hz
            simp only [List.mem_append, List.mem_singleton] at hz
            rcases hz with hz | rfl
            · exact hlast z (by simpa [k_post] using hz)
            · scalar_tac

@[step]
theorem sort_prefix_correct (list : Aeneas.Std.Slice I32) (n : Usize)
    (hb : n.val ≤ list.val.length) :
    solution.sort_prefix list n ⦃ v =>
      v.val.Perm (list.val.take n.val) ∧
      v.val.Pairwise (fun a b => a.val ≤ b.val) ⦄ := by
  generalize he : n.val = size
  induction size using Nat.strong_induction_on generalizing n with
  | h size ih =>
    unfold solution.sort_prefix
    step*
    · have hz : size = 0 := by scalar_tac
      simp [hz, alloc.vec.Vec.new]
    · have hl := sorted_post.length_eq
      simp only [List.length_take] at hl
      simp [alloc.vec.Vec.deref] 
      omega
    · simp [alloc.vec.Vec.deref]
      exact sorted_post1.sublist (List.take_sublist _ _)
    · have hl : k.val = sorted.val.length := by
        have hh := sorted_post.length_eq
        simp only [List.length_take] at hh
        omega
      simp [alloc.vec.Vec.deref] at v_post
      change v.val.Perm (sorted.val.take k.val ++ [x]) at v_post
      rw [hl, List.take_length] at v_post
      refine ⟨?_, v_post1⟩
      have ht : list.val.take size = list.val.take (n.val - 1) ++ [x] := by
        rw [show size = k.val + 1 by omega, List.take_succ_eq_append_getElem (by omega)]
        simp_all
      rw [ht]
      exact v_post.trans (sorted_post.append_right [x])

theorem sort.impl_correct :
    ∀ (v : alloc.vec.Vec I32), sort_pre v.val →
      SortProg.spec.sort v ⦃ v2 => sort_spec v.val v2.val ⦄ := by
  intro v _
  unfold spec.sort solution.sort
  step*
  · simp [alloc.vec.Vec.deref]
  · simp only [alloc.vec.Vec.len_val] at v2_post
    simp [alloc.vec.Vec.deref] at v2_post
    refine ⟨trivial, (perm_iff _ _).mpr v2_post, (ascending_iff _).mpr ?_⟩
    apply List.sortedLE_iff_pairwise.mpr
    simpa only [IScalar.le_equiv] using v2_post1

@[step]
theorem max_prefix_correct (list : Aeneas.Std.Slice I32) (n : Usize)
    (hn : 0 < n.val) (hb : n.val ≤ list.val.length) :
    solution.max_prefix list n ⦃ r => r ∈ list.val.take n.val ∧
      ∀ x ∈ list.val.take n.val, x.val ≤ r.val ⦄ := by
  generalize he : n.val = size
  induction size using Nat.strong_induction_on generalizing n with
  | h size ih =>
    unfold solution.max_prefix
    step*
    · have hm : size = 1 := by scalar_tac
      rw [hm]
      subst r
      rw [List.take_succ_eq_append_getElem (by omega : 0 < list.val.length)]
      simp
    · have ht : list.val.take size = list.val.take (n.val - 1) ++ [x] := by
        rw [show size = k.val + 1 by omega, List.take_succ_eq_append_getElem (by omega)]
        simp_all
      rw [ht]
      simp only [List.mem_append, List.mem_singleton]
      refine ⟨Or.inr trivial, ?_⟩
      intro z hz
      rcases hz with hz | rfl
      · have := m_post1 z hz; scalar_tac
      · omega
    · have ht : list.val.take size = list.val.take (n.val - 1) ++ [x] := by
        rw [show size = k.val + 1 by omega, List.take_succ_eq_append_getElem (by omega)]
        simp_all
      rw [ht]
      simp only [List.mem_append, List.mem_singleton]
      refine ⟨Or.inl m_post, ?_⟩
      intro z hz
      rcases hz with hz | rfl
      · exact m_post1 z hz
      · scalar_tac

theorem max.impl_correct :
    ∀ (list : Aeneas.Std.Slice I32), max_pre list.val →
      SortProg.spec.max list ⦃ r => max_spec list.val r ⦄ := by
  intro list h
  unfold spec.max solution.max
  have hn : 0 < list.val.length := by unfold max_pre at h; omega
  step*
  simp only [Slice.len_val, List.take_length] at *
  exact ⟨h, r_post, r_post1⟩

end SortProg.Proofs
