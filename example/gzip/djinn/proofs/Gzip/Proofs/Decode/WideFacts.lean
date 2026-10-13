import Gzip.Proofs.Decode.PeekFacts

open Aeneas Std Result
open Gzip.Spec
open Gzip.Proofs.Decode.PeekFacts

namespace Gzip.Proofs.Decode.WideFacts

/-- Bytes as a little-endian number. -/
def le : List Nat → Nat
  | [] => 0
  | a :: t => a + 256 * le t

theorem le_bit (l : List Nat) (hl : ∀ x ∈ l, x < 256) (q m : Nat) (hq : q < l.length)
    (hm : m < 8) : le l / 2 ^ (8 * q + m) % 2 = l[q]! / 2 ^ m % 2 := by
  induction l generalizing q with
  | nil => simp at hq
  | cons a t ih =>
    have ha : a < 256 := hl a (by simp)
    cases q with
    | zero =>
      simp only [le, Nat.mul_zero, Nat.zero_add, List.getElem!_cons_zero]
      interval_cases m <;> norm_num <;> omega
    | succ q =>
      have hp : 2 ^ (8 * (q + 1) + m) = 256 * 2 ^ (8 * q + m) := by
        rw [show 8 * (q + 1) + m = 8 + (8 * q + m) by ring, pow_add]
        norm_num
      have hd : (a + 256 * le t) / 256 = le t := by omega
      simp only [le, List.getElem!_cons_succ]
      rw [hp, ← Nat.div_div_eq_div_mul, hd]
      exact ih (fun x hx => hl x (by simp [hx])) q (by simpa using hq)

/-- The eight bytes from byte `b`, as a little-endian number, hold the stream's bits from
bit `8 * b` on. -/
theorem peek_bit8 (s : List U8) (b j : Nat) (hb : b + 8 ≤ s.length) (hj : j < 64) :
    bit_spec s (8 * (b : ℤ) + j)
      ((le [(s[b]!).val, (s[b + 1]!).val, (s[b + 2]!).val, (s[b + 3]!).val, (s[b + 4]!).val,
        (s[b + 5]!).val, (s[b + 6]!).val, (s[b + 7]!).val] / 2 ^ j % 2 : Nat) : ℤ) := by
  have hdiv : (8 * (b : ℤ) + j) / 8 = ((b + j / 8 : Nat) : ℤ) := by push_cast; omega
  have hmod : (8 * (b : ℤ) + j) % 8 = ((j % 8 : Nat) : ℤ) := by push_cast; omega
  refine ⟨trivial, ⟨by omega, by omega⟩, ?_⟩
  rw [hdiv, hmod, Int.toNat_natCast, Int.toNat_natCast]
  have hw := le_bit [(s[b]!).val, (s[b + 1]!).val, (s[b + 2]!).val, (s[b + 3]!).val,
    (s[b + 4]!).val, (s[b + 5]!).val, (s[b + 6]!).val, (s[b + 7]!).val]
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx | hx | hx | hx | hx | hx <;> rw [hx] <;> scalar_tac)
    (j / 8) (j % 8) (by simp only [List.length_cons, List.length_nil]; omega) (by omega)
  rw [Nat.div_add_mod] at hw
  rw [hw]
  have hq : j / 8 = 0 ∨ j / 8 = 1 ∨ j / 8 = 2 ∨ j / 8 = 3 ∨ j / 8 = 4 ∨ j / 8 = 5 ∨
      j / 8 = 6 ∨ j / 8 = 7 := by omega
  rcases hq with hq | hq | hq | hq | hq | hq | hq | hq <;> simp [hq]

/-- A bit of a shifted number. -/
theorem shift_bit (p a k : Nat) : p / 2 ^ a / 2 ^ k % 2 = p / 2 ^ (a + k) % 2 := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]

/-- A window on the stream at `i`, shifted by `a`, is a window at `i + a`. -/
theorem window_shift (s : List U8) (i : ℤ) (p a m : Nat)
    (h : ∀ k : Nat, k < a + m → bit_spec s (i + k) ((p / 2 ^ k % 2 : Nat) : ℤ)) :
    ∀ k : Nat, k < m → bit_spec s (i + a + k) ((p / 2 ^ a / 2 ^ k % 2 : Nat) : ℤ) := by
  intro k hk
  have hb := h (a + k) (by omega)
  rw [shift_bit]
  have he : i + (a : ℤ) + (k : ℤ) = i + ((a + k : Nat) : ℤ) := by push_cast; ring
  rw [he]
  exact hb

end Gzip.Proofs.Decode.WideFacts
