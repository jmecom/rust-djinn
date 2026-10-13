import Gzip.Proofs.Tables
import Gzip.Proofs.Tokens

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Indices Gzip.Proofs.Plans Gzip.Proofs.Matches

namespace Gzip.Proofs.Symbolize

def widen8 (x : U8) : Usize := UScalar.cast .Usize x

@[simp] theorem widen8_val (x : U8) : (widen8 x).val = x.val := by
  unfold widen8
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]

theorem narrow8_val (x : Usize) (hx : x.val < 256) :
    (UScalar.cast .U8 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  simpa only [UScalarTy.numBits, Nat.reducePow] using Nat.mod_eq_of_lt hx

/-- What a plan's tokens look like, index by index. -/
def ValidPlan (ls ds : List U16) : Prop :=
  ds.length = ls.length ∧ ∀ t < ls.length,
    ((ds[t]!).val = 0 → (ls[t]!).val = 1) ∧
    ((ds[t]!).val ≠ 0 → 3 ≤ (ls[t]!).val ∧ (ls[t]!).val ≤ 258 ∧ 1 ≤ (ds[t]!).val ∧ (ds[t]!).val ≤ 32768)

theorem runs_valid {data : List U8} {stop p q : ℕ} {ls ds : List U16}
    (h : Runs data stop p q ls ds) : ValidPlan ls ds := by
  induction h with
  | finish => exact ⟨rfl, fun t ht => by simp at ht⟩
  | next p q l d ls ds hv ht ih =>
      refine ⟨by simp [ih.1], ?_⟩
      intro t htl
      cases t with
      | zero =>
          simp only [List.getElem!_cons_zero]
          rcases hv with ⟨hl, hd⟩ | ⟨hm, hd⟩
          · exact ⟨fun _ => hl, fun hn => absurd hd hn⟩
          · rcases hm with hm | hm
            · omega
            · exact ⟨fun hz => by omega, fun _ => ⟨hm.1, hm.2.1, by omega, hm.2.2.2.2.2.1⟩⟩
      | succ t =>
          simp only [List.getElem!_cons_succ]
          exact ih.2 t (by simp at htl; omega)

/-- The symbol indices of a plan's copies. -/
def Symbolized (ls ds : List U16) (lsym dsym : List U8) : Prop :=
  lsym.length = ls.length ∧ dsym.length = ls.length ∧
  ∀ t < ls.length, (ds[t]!).val ≠ 0 →
    (lsym[t]!).val ≤ 28 ∧ (dsym[t]!).val ≤ 29 ∧
    lb (lsym[t]!).val ≤ (ls[t]!).val ∧ (ls[t]!).val - lb (lsym[t]!).val < 2 ^ le (lsym[t]!).val ∧
    db (dsym[t]!).val ≤ (ds[t]!).val ∧ (ds[t]!).val - db (dsym[t]!).val < 2 ^ de (dsym[t]!).val

theorem symbolized_extend {ls ds : List U16} {lsym dsym : List U8} {t : ℕ} (l d : U8)
    (hl : lsym.length = t) (hd : dsym.length = t) (ht : t < ls.length)
    (hprev : ∀ t' < t, (ds[t']!).val ≠ 0 →
      (lsym[t']!).val ≤ 28 ∧ (dsym[t']!).val ≤ 29 ∧
      lb (lsym[t']!).val ≤ (ls[t']!).val ∧ (ls[t']!).val - lb (lsym[t']!).val < 2 ^ le (lsym[t']!).val ∧
      db (dsym[t']!).val ≤ (ds[t']!).val ∧ (ds[t']!).val - db (dsym[t']!).val < 2 ^ de (dsym[t']!).val)
    (hnew : (ds[t]!).val ≠ 0 →
      l.val ≤ 28 ∧ d.val ≤ 29 ∧ lb l.val ≤ (ls[t]!).val ∧ (ls[t]!).val - lb l.val < 2 ^ le l.val ∧
      db d.val ≤ (ds[t]!).val ∧ (ds[t]!).val - db d.val < 2 ^ de d.val) :
    ∀ t' < t + 1, (ds[t']!).val ≠ 0 →
      ((lsym ++ [l])[t']!).val ≤ 28 ∧ ((dsym ++ [d])[t']!).val ≤ 29 ∧
      lb ((lsym ++ [l])[t']!).val ≤ (ls[t']!).val ∧
      (ls[t']!).val - lb ((lsym ++ [l])[t']!).val < 2 ^ le ((lsym ++ [l])[t']!).val ∧
      db ((dsym ++ [d])[t']!).val ≤ (ds[t']!).val ∧
      (ds[t']!).val - db ((dsym ++ [d])[t']!).val < 2 ^ de ((dsym ++ [d])[t']!).val := by
  intro t' ht' hnz
  by_cases hlt : t' < t
  · rw [List.getElem!_append_left lsym [l] t' (by omega), List.getElem!_append_left dsym [d] t' (by omega)]
    exact hprev t' hlt hnz
  · have he : t' = t := by omega
    subst he
    rw [List.getElem!_append_right lsym [l] t' (by omega), List.getElem!_append_right dsym [d] t' (by omega)]
    simp only [hl, hd, Nat.sub_self, List.getElem!_cons_zero]
    exact hnew hnz

end Gzip.Proofs.Symbolize
