import Gzip.Proofs.Chains

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Chains

namespace Gzip.Proofs.Reverse

theorem get_set16 (xs : List U16) (i k : ℕ) (x : U16) (hk : k < xs.length) :
    (xs.set i x)[k]! = if i = k then x else xs[k]! := by
  rw [getElem!_pos (xs.set i x) k (by simpa using hk), List.getElem_set,
    getElem!_pos xs k hk]

def Swapped (original current : List U16) (i : ℕ) : Prop :=
  current.length = original.length ∧ ∀ k < original.length,
    current[k]! = if k < i ∨ original.length - 1 - k < i
      then original[original.length - 1 - k]! else original[k]!

theorem swapped_initial (original : List U16) : Swapped original original 0 := by
  refine ⟨rfl, ?_⟩
  intro k hk
  simp

theorem swapped_next (original current : List U16) (i : ℕ)
    (h : Swapped original current i) (hi : i < original.length / 2) :
    Swapped original
      ((current.set i current[original.length - 1 - i]!).set (original.length - 1 - i) current[i]!) (i + 1) := by
  let j := original.length - 1 - i
  have hil : i < original.length := by omega
  have hjl : j < original.length := by dsimp [j]; omega
  have hij : i < j := by dsimp [j]; omega
  have hjrev : original.length - 1 - j = i := by dsimp [j]; omega
  have hci : current[i]! = original[i]! := by
    have hv := h.2 i hil
    rw [if_neg (by dsimp [j] at hij; omega)] at hv
    exact hv
  have hcj : current[j]! = original[j]! := by
    have hv := h.2 j hjl
    rw [hjrev, if_neg (by omega)] at hv
    exact hv
  refine ⟨by simpa using h.1, ?_⟩
  intro k hk
  have hkc : k < current.length := by rw [h.1]; exact hk
  change ((current.set i current[j]!).set j current[i]!)[k]! = _
  rw [get_set16 (current.set i current[j]!) j k current[i]! (by simpa using hkc)]
  by_cases hkj : k = j
  · subst k
    rw [if_pos rfl, hci, hjrev, if_pos (by omega)]
  · rw [if_neg (by omega), get_set16 current i k current[j]! hkc]
    by_cases hki : k = i
    · subst k
      rw [if_pos rfl, hcj, if_pos (by omega)]
    · rw [if_neg (by omega), h.2 k hk]
      have he : (k < i ∨ original.length - 1 - k < i) ↔
          (k < i + 1 ∨ original.length - 1 - k < i + 1) := by dsimp [j] at hkj; omega
      simp only [he]

theorem swapped_done (original current : List U16) (i : ℕ)
    (h : Swapped original current i) (hi : original.length / 2 ≤ i) : current = original.reverse := by
  apply List.ext_getElem (by simp [h.1])
  intro k hk hk'
  have hko : k < original.length := by simpa using hk'
  rw [← getElem!_pos current k hk, List.getElem_reverse hk',
    ← getElem!_pos original (original.length - 1 - k) (by omega), h.2 k hko]
  split
  · rfl
  · have he : original.length - 1 - k = k := by omega
    rw [he]

theorem body (originalL originalD : List U16) (v distances : alloc.vec.Vec U16) (i : Usize)
    (heq : originalD.length = originalL.length)
    (hv : Swapped originalL v.val i.val) (hd : Swapped originalD distances.val i.val)
    (hi : i.val ≤ originalL.length / 2) :
    trace_loop1.body v distances i ⦃ r =>
      match r with
      | .done (v', d') => v'.val = originalL.reverse ∧ d'.val = originalD.reverse
      | .cont (v', d', j) => Swapped originalL v'.val j.val ∧ Swapped originalD d'.val j.val ∧
          j.val = i.val + 1 ∧ j.val ≤ originalL.length / 2 ⦄ := by
  have hvl : v.len.val = originalL.length := by
    rw [alloc.vec.Vec.len_val, alloc.vec.Vec.length, hv.1]
  have hdl : distances.val.length = originalL.length := hd.1.trans heq
  unfold trace_loop1.body
  step*
  · rw [index_mut_back_post, alloc.vec.Vec.set_length]
    change j.val < v.val.length
    rw [hv.1]
    scalar_tac
  · rw [index_mut_back1_post, alloc.vec.Vec.set_length]
    change j.val < distances.val.length
    rw [hdl]
    scalar_tac
  · have hj : j.val = originalL.length - 1 - i.val := by rw [j_post, i4_post, hvl]
    have hil : i.val < v.val.length := by rw [hv.1]; scalar_tac
    have hjl : j.val < v.val.length := by rw [hv.1]; scalar_tac
    have hid : i.val < distances.val.length := by rw [hdl]; scalar_tac
    have hjd : j.val < distances.val.length := by rw [hdl]; scalar_tac
    have hlold : l = v.val[i.val]! := by rw [l_post, getElem!_pos v.val i.val hil]
    have hlj : i5 = v.val[j.val]! := by rw [i5_post, getElem!_pos v.val j.val hjl]
    have hdold : d = distances.val[i.val]! := by rw [d_post, getElem!_pos distances.val i.val hid]
    have hdj : i6 = distances.val[j.val]! := by rw [i6_post, getElem!_pos distances.val j.val hjd]
    have hnewL : (index_mut_back2 l).val = (v.val.set i.val v.val[j.val]!).set j.val v.val[i.val]! := by
      simp only [index_mut_back2_post, index_mut_back_post, alloc.vec.Vec.set_val_eq, hlold, hlj]
    have hnewD : (index_mut_back3 d).val =
        (distances.val.set i.val distances.val[j.val]!).set j.val distances.val[i.val]! := by
      simp only [index_mut_back3_post, index_mut_back1_post, alloc.vec.Vec.set_val_eq, hdold, hdj]
    refine ⟨?_, ?_, i7_post, by scalar_tac⟩
    · rw [hnewL, hj, i7_post]
      exact swapped_next originalL v.val i.val hv (by scalar_tac)
    · rw [hnewD, hj, i7_post]
      simpa only [heq] using swapped_next originalD distances.val i.val hd (by rw [heq]; scalar_tac)
  · exact ⟨swapped_done originalL v.val i.val hv (by scalar_tac),
      swapped_done originalD distances.val i.val hd (by rw [heq]; scalar_tac)⟩

@[step]
theorem reverse_loop (originalL originalD : List U16) (v distances : alloc.vec.Vec U16) (i : Usize)
    (heq : originalD.length = originalL.length)
    (hv : Swapped originalL v.val i.val) (hd : Swapped originalD distances.val i.val)
    (hi : i.val ≤ originalL.length / 2) :
    trace_loop1 v distances i ⦃ r => r.1.val = originalL.reverse ∧ r.2.val = originalD.reverse ⦄ := by
  unfold trace_loop1
  apply loop.spec_decr_nat (fun (_, _, j) => originalL.length / 2 - j.val)
    (fun (v', d', j) => Swapped originalL v'.val j.val ∧ Swapped originalD d'.val j.val ∧
      j.val ≤ originalL.length / 2)
  · rintro ⟨v', d', j⟩ ⟨hv', hd', hj⟩
    refine WP.spec_mono (body originalL originalD v' d' j heq hv' hd' hj) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨v'', d'', j'⟩ := state
        obtain ⟨hv'', hd'', he, hj'⟩ := hr
        exact ⟨⟨hv'', hd'', hj'⟩, by change originalL.length / 2 - j'.val < originalL.length / 2 - j.val; omega⟩
  · exact ⟨hv, hd, hi⟩

end Gzip.Proofs.Reverse
