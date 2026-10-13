import Gzip.Proofs.WordPrefix
import Mathlib.Tactic.IntervalCases

open Aeneas Std

namespace Gzip.Proofs.DeBruijn

theorem isolated64 (x : BitVec 64) (hne : x ≠ 0) :
    ∃ k, k < 64 ∧ x &&& -x = BitVec.ofNat 64 (2 ^ k) ∧
      x.toNat.testBit k = true ∧ ∀ j < k, x.toNat.testBit j = false := by
  classical
  have hex : ∃ k, k < 64 ∧ x.getLsbD k = true := by
    by_contra hn
    apply hne
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.ofNat_eq_ofNat, BitVec.getLsbD_ofNat]
    simp only [Nat.zero_testBit, Bool.and_false]
    have ht : x.getLsbD i ≠ true := by
      intro ht
      exact hn ⟨i, hi, ht⟩
    cases hb : x.getLsbD i with
    | false => rfl
    | true => exact False.elim (ht hb)
  let k := Nat.find hex
  have hk : k < 64 ∧ x.getLsbD k = true := Nat.find_spec hex
  have hp : ∀ j < k, x.getLsbD j = false := by
    intro j hj
    have hn := Nat.find_min hex hj
    have hj64 : j < 64 := by omega
    cases hb : x.getLsbD j with
    | false => rfl
    | true => exact False.elim (hn ⟨hj64, hb⟩)
  refine ⟨k, hk.1, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_neg, BitVec.getLsbD_ofNat]
    simp only [hi, decide_true, Bool.true_and, Nat.testBit_two_pow]
    by_cases hil : i < k
    · rw [hp i hil]
      simp only [Bool.false_and]
      have hn : k ≠ i := by omega
      simp [hn]
    · by_cases hie : i = k
      · subst i
        have he : ¬ ∃ j < k, x.getLsbD j = true := by
          rintro ⟨j, hj, hjt⟩
          rw [hp j hj] at hjt
          contradiction
        simp [hk.2, he]
      · have he : ∃ j < i, x.getLsbD j = true := ⟨k, by omega, hk.2⟩
        simp only [he, decide_true, Bool.true_and]
        have hn : k ≠ i := by omega
        simp only [hn, decide_false]
        cases hb : x.getLsbD i <;> decide
  · exact hk.2
  · intro j hj
    exact hp j hj

end Gzip.Proofs.DeBruijn
