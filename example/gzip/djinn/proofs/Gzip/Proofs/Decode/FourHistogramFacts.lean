import Gzip.Proofs.Decode.CodewordImpl
import Gzip.Vocab

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.CodewordImpl

namespace Gzip.Proofs.Decode.FourHistogramFacts

/-- The combined value of one bin of four independent scalar histograms. -/
def total4 (a b c d : List U32) (m : Nat) : Nat :=
  (a[m]!).val + (b[m]!).val + (c[m]!).val + (d[m]!).val

/-- Only the combined bins need a semantic invariant. The individual counters are bounded
by their sum, so this also supplies the bounds for each increment. -/
def SummedSeen (lens : List U8) (a b c d : List U32) (i : Nat) : Prop :=
  i ≤ lens.length ∧ ∀ m : Nat, m < 16 →
    earlier_spec lens i m (total4 a b c d m) ∧ total4 a b c d m ≤ i

def MergeSeen (lens : List U8) (a b c d : List U32) (n : Nat) : Prop :=
  ∀ m : Nat, m < 16 → if m < n then
    earlier_spec lens lens.length m (a[m]!).val ∧ (a[m]!).val ≤ lens.length
  else
    earlier_spec lens lens.length m (total4 a b c d m) ∧ total4 a b c d m ≤ lens.length

theorem summed_zero (lens : List U8) :
    SummedSeen lens (List.replicate 16 0#u32) (List.replicate 16 0#u32)
      (List.replicate 16 0#u32) (List.replicate 16 0#u32) 0 := by
  refine ⟨by omega, ?_⟩
  intro m hm
  simp only [total4, List.getElem!_replicate _ hm]
  exact ⟨earlier_zero _ _, by decide⟩

theorem individual_bounds (a b c d : List U32) (m i : Nat) (h : total4 a b c d m ≤ i) :
    (a[m]!).val ≤ i ∧ (b[m]!).val ≤ i ∧ (c[m]!).val ≤ i ∧ (d[m]!).val ≤ i := by
  unfold total4 at h
  omega

def delta (lens : List U8) (i n : Nat) : Nat :=
  if (lens[i]!).val = n then 1 else 0

theorem earlier_next_nat (lens : List U8) (i n v : Nat)
    (hi : i < lens.length) (h : earlier_spec lens i n v) :
    earlier_spec lens ((i + 1 : Nat) : Int) n ((v + delta lens i n : Nat) : Int) := by
  have hnext := earlier_next lens i n v hi h
  by_cases he : (lens[i]!).val = n
  · simpa [delta, he] using hnext
  · simpa [delta, he] using hnext

theorem earlier_four (lens : List U8) (i n v : Nat)
    (hi : i + 4 ≤ lens.length) (h : earlier_spec lens i n v) :
    earlier_spec lens ((i + 4 : Nat) : Int) n
      ((v + delta lens i n + delta lens (i + 1) n +
        delta lens (i + 2) n + delta lens (i + 3) n : Nat) : Int) := by
  have h1 := earlier_next_nat lens i n v (by omega) h
  have h2 := earlier_next_nat lens (i + 1) n (v + delta lens i n) (by omega) h1
  have h3 := earlier_next_nat lens (i + 2) n
    (v + delta lens i n + delta lens (i + 1) n) (by omega) (by simpa [Nat.add_assoc] using h2)
  have h4 := earlier_next_nat lens (i + 3) n
    (v + delta lens i n + delta lens (i + 1) n + delta lens (i + 2) n)
    (by omega) (by simpa [Nat.add_assoc] using h3)
  simpa [Nat.add_assoc] using h4

theorem total4_increment_first (a b c d : List U32) (idx m : Nat) (v : U32)
    (hm : m < a.length) (hv : v.val = (a[idx]!).val + 1) :
    total4 (a.set idx v) b c d m = total4 a b c d m +
      (if idx = m then 1 else 0) := by
  unfold total4
  rw [Djinn.Vocab.getElem!_set _ _ _ _ hm]
  by_cases he : m = idx
  · subst m
    simp only [ite_true]
    rw [hv]
    omega
  · simp only [if_neg he, if_neg (Ne.symm he), Nat.add_zero]

theorem total4_increment_second (a b c d : List U32) (idx m : Nat) (v : U32)
    (hm : m < b.length) (hv : v.val = (b[idx]!).val + 1) :
    total4 a (b.set idx v) c d m = total4 a b c d m +
      (if idx = m then 1 else 0) := by
  unfold total4
  rw [Djinn.Vocab.getElem!_set _ _ _ _ hm]
  by_cases he : m = idx
  · subst m
    simp only [ite_true]
    rw [hv]
    omega
  · simp only [if_neg he, if_neg (Ne.symm he), Nat.add_zero]

theorem total4_increment_third (a b c d : List U32) (idx m : Nat) (v : U32)
    (hm : m < c.length) (hv : v.val = (c[idx]!).val + 1) :
    total4 a b (c.set idx v) d m = total4 a b c d m +
      (if idx = m then 1 else 0) := by
  unfold total4
  rw [Djinn.Vocab.getElem!_set _ _ _ _ hm]
  by_cases he : m = idx
  · subst m
    simp only [ite_true]
    rw [hv]
    omega
  · simp only [if_neg he, if_neg (Ne.symm he), Nat.add_zero]

theorem total4_increment_fourth (a b c d : List U32) (idx m : Nat) (v : U32)
    (hm : m < d.length) (hv : v.val = (d[idx]!).val + 1) :
    total4 a b c (d.set idx v) m = total4 a b c d m +
      (if idx = m then 1 else 0) := by
  unfold total4
  rw [Djinn.Vocab.getElem!_set _ _ _ _ hm]
  by_cases he : m = idx
  · subst m
    simp only [ite_true]
    rw [hv]
    omega
  · simp only [if_neg he, if_neg (Ne.symm he), Nat.add_zero]

end Gzip.Proofs.Decode.FourHistogramFacts
