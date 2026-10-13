import Gzip.Proofs.Encoding

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Plans Gzip.Proofs.Encoding Gzip.Proofs.Writer

namespace Gzip.Proofs.Tokens

def Emitted (data : List U8) (start p : ℕ) (bits : List Bool) : Prop :=
  ∀ q tail, Encodes data p q tail → Encodes data start q (bits ++ tail)

theorem emitted_nil (data : List U8) (p : ℕ) : Emitted data p p [] := by
  intro q tail h
  exact h

theorem emitted_literal {data : List U8} {start p : ℕ} {bits : List Bool}
    (h : Emitted data start p bits) (hp : p < data.length) :
    Emitted data start (p + 1) (bits ++ Symbols.encode data[p]!.val) := by
  intro q tail ht
  simpa only [List.append_assoc] using h q _ (Encodes.literal p q tail hp ht)

theorem emitted_copy {data : List U8} {start p len dist l d : ℕ} {bits : List Bool}
    (h : Emitted data start p bits)
    (hm : 3 ≤ len ∧ len ≤ 258 ∧ p + len ≤ data.length ∧
      0 < dist ∧ dist ≤ p ∧ dist ≤ 32768 ∧ Matches.EqualRun data p (p - dist) len)
    (hi : l ≤ 28 ∧ d ≤ 29 ∧ Indices.lb l ≤ len ∧ Indices.db d ≤ dist ∧
      len - Indices.lb l < 2 ^ Indices.le l ∧ dist - Indices.db d < 2 ^ Indices.de d) :
    Emitted data start (p + len) (bits ++ Copies.encode len dist l d) := by
  intro q tail ht
  simpa only [List.append_assoc] using h q _ (Encodes.copy p q len dist l d tail hm hi ht)

theorem drop_head {xs : List U16} {t : ℕ} {x : U16} {ys : List U16}
    (ht : t < xs.length) (he : xs.drop t = x :: ys) :
    xs[t]! = x ∧ xs.drop (t + 1) = ys := by
  have hget := congrArg (fun a : List U16 => a[0]!) he
  rw [getElem!_pos (xs.drop t) 0 (by simp only [List.length_drop]; omega), List.getElem_drop] at hget
  simp only [Nat.add_zero, Nat.zero_add, List.getElem!_cons_zero] at hget
  refine ⟨by rw [getElem!_pos xs t ht]; exact hget, ?_⟩
  have htail := congrArg (fun a : List U16 => a.drop 1) he
  simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero] using htail

theorem runs_head {data : List U8} {stop p t : ℕ} {ls ds : List U16}
    (h : Runs data stop p stop (ls.drop t) (ds.drop t))
    (ht : t < ls.length) (hlen : ls.length = ds.length) :
    Step data p stop ls[t]! ds[t]! ∧
      Runs data stop (p + ls[t]!.val) stop (ls.drop (t + 1)) (ds.drop (t + 1)) := by
  generalize heL : ls.drop t = remainingL at h
  generalize heD : ds.drop t = remainingD at h
  cases h with
  | finish p =>
      have hzero : (ls.drop t).length = 0 := by simp_all
      simp only [List.length_drop] at hzero
      omega
  | next p endpoint l d ls' ds' hv hr =>
      have heL : ls.drop t = l :: ls' := by assumption
      have heD : ds.drop t = d :: ds' := by assumption
      obtain ⟨hL, hLs⟩ := drop_head ht heL
      obtain ⟨hD, hDs⟩ := drop_head (by omega) heD
      rw [hL, hD, hLs, hDs]
      exact ⟨hv, hr⟩

end Gzip.Proofs.Tokens
