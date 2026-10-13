import Gzip.Spec
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases

open Aeneas Std Result
open Gzip.Spec

namespace Gzip.Proofs.Decode.PeekFacts

/-- The low `n` bits of `p`, read in the opposite order: bit 0 of `p` becomes the highest. -/
def rev (p : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 * rev p n + p / 2 ^ n % 2

theorem rev_lt (p n : Nat) : rev p n < 2 ^ n := by
  induction n with
  | zero => simp [rev]
  | succ n ih =>
    simp only [rev]
    rw [pow_succ]
    omega

theorem bit_mod (p m k : Nat) (h : k < m) : p % 2 ^ m / 2 ^ k % 2 = p / 2 ^ k % 2 := by
  rw [← Nat.toNat_testBit, ← Nat.toNat_testBit, Nat.testBit_mod_two_pow]
  simp [h]

theorem rev_mod (p m n : Nat) (h : n ≤ m) : rev (p % 2 ^ m) n = rev p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rev]
    rw [ih (by omega), bit_mod p m n (by omega)]

/-- A number whose bits are the bits of the stream from `i` on: its first `n` bits reversed
are the `n`-bit code at `i`. -/
theorem code_of_bits (s : List U8) (i : ℤ) (p n : Nat)
    (h : ∀ k : Nat, k < n → bit_spec s (i + k) ((p / 2 ^ k % 2 : Nat) : ℤ)) :
    code_spec s i n (rev p n : Nat) := by
  induction n with
  | zero =>
    rw [code_spec]
    simp [code_pre, rev]
  | succ n ih =>
    rw [code_spec]
    refine ⟨show (0 : ℤ) ≤ ((n + 1 : Nat) : ℤ) by omega, fun _ => ⟨fun hz => by omega, fun _ => ?_⟩⟩
    refine ⟨(rev p n : Nat), ?_, ((p / 2 ^ n % 2 : Nat) : ℤ), ?_, ?_⟩
    · have hrec := ih (fun k hk => h k (by omega))
      have he : ((n + 1 : Nat) : ℤ) - 1 = (n : ℤ) := by omega
      rw [he]
      exact hrec
    · have hb := h n (by omega)
      have he : i + ((n + 1 : Nat) : ℤ) - 1 = i + (n : ℤ) := by omega
      rw [he]
      exact hb
    · simp only [rev]
      push_cast
      ring

/-- And its first `n` bits as they are make the `n`-bit field at `i`. -/
theorem field_of_bits (s : List U8) (n : Nat) : ∀ (i : ℤ) (p : Nat),
    (∀ k : Nat, k < n → bit_spec s (i + k) ((p / 2 ^ k % 2 : Nat) : ℤ)) →
    field_spec s i n ((p % 2 ^ n : Nat) : ℤ) := by
  induction n with
  | zero =>
    intro i p _
    rw [field_spec]
    simp [field_pre, Nat.mod_one]
  | succ n ih =>
    intro i p h
    rw [field_spec]
    refine ⟨show (0 : ℤ) ≤ ((n + 1 : Nat) : ℤ) by omega, fun _ => ⟨fun hz => by omega, fun _ => ?_⟩⟩
    refine ⟨((p % 2 : Nat) : ℤ), ?_, fun _ => ⟨((p / 2 % 2 ^ n : Nat) : ℤ), ?_, ?_⟩⟩
    · have hb := h 0 (by omega)
      simpa using hb
    · have hrec := ih (i + 1) (p / 2) (fun k hk => by
        have hb := h (k + 1) (by omega)
        have hd : p / 2 / 2 ^ k = p / 2 ^ (k + 1) := by
          rw [Nat.div_div_eq_div_mul, ← pow_succ']
        have hi : i + 1 + (k : ℤ) = i + ((k + 1 : Nat) : ℤ) := by push_cast; ring
        rw [hd, hi]
        exact hb)
      have he : ((n + 1 : Nat) : ℤ) - 1 = (n : ℤ) := by omega
      rw [he]
      exact hrec
    · have he : p % 2 ^ (n + 1) = p % 2 + 2 * (p / 2 % 2 ^ n) := by
        rw [pow_succ', Nat.mod_mul]
      exact_mod_cast he

theorem word_bit (a0 a1 a2 q m : Nat) (h0 : a0 < 256) (h1 : a1 < 256) (h2 : a2 < 256)
    (hq : q < 3) (hm : m < 8) :
    (a0 + 256 * a1 + 65536 * a2) / 2 ^ (8 * q + m) % 2 =
      (if q = 0 then a0 else if q = 1 then a1 else a2) / 2 ^ m % 2 := by
  interval_cases q <;> interval_cases m <;> norm_num <;> omega

/-- The three bytes from byte `b`, as a little-endian number, hold the stream's bits from
bit `8 * b` on. -/
theorem peek_bit (s : List U8) (b j : Nat) (hb : b + 3 ≤ s.length) (hj : j < 24) :
    bit_spec s (8 * (b : ℤ) + j)
      ((((s[b]!).val + 256 * (s[b + 1]!).val + 65536 * (s[b + 2]!).val) / 2 ^ j % 2 : Nat) : ℤ) := by
  have hdiv : (8 * (b : ℤ) + j) / 8 = ((b + j / 8 : Nat) : ℤ) := by push_cast; omega
  have hmod : (8 * (b : ℤ) + j) % 8 = ((j % 8 : Nat) : ℤ) := by push_cast; omega
  refine ⟨trivial, ⟨by omega, by omega⟩, ?_⟩
  rw [hdiv, hmod, Int.toNat_natCast, Int.toNat_natCast]
  have hw := word_bit (s[b]!).val (s[b + 1]!).val (s[b + 2]!).val (j / 8) (j % 8)
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by omega) (by omega)
  rw [Nat.div_add_mod] at hw
  rw [hw]
  have hq : j / 8 = 0 ∨ j / 8 = 1 ∨ j / 8 = 2 := by omega
  rcases hq with hq | hq | hq <;> simp [hq]

end Gzip.Proofs.Decode.PeekFacts
