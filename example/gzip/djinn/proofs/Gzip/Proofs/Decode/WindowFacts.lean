import Gzip.Proofs.Decode.WideFacts
import Gzip.Proofs.Decode.Decoding

open Aeneas Std Result
open Gzip.Spec
open Gzip.Proofs.Decode.PeekFacts Gzip.Proofs.Decode.WideFacts Gzip.Proofs.Decode.Decoding

namespace Gzip.Proofs.Decode.WindowFacts

/-- A bit window on the stream at `P`: bits `0..nbits` of `buf` are the stream's bits from `P`
on, and every bit above is zero or also the stream's bit at its place (so that oring the
stream's bits in above `nbits` changes nothing there). -/
def Window (s : List U8) (buf nbits : Nat) (P : ℤ) : Prop :=
  ∀ k : Nat, k < 64 →
    bit_spec s (P + k) ((buf / 2 ^ k % 2 : Nat) : ℤ) ∨ (nbits ≤ k ∧ buf / 2 ^ k % 2 = 0)

theorem window_bits (s : List U8) (buf nbits : Nat) (P : ℤ) (h : Window s buf nbits P) :
    ∀ k : Nat, k < 64 → k < nbits → bit_spec s (P + k) ((buf / 2 ^ k % 2 : Nat) : ℤ) := by
  intro k hk hn
  rcases h k hk with hb | ⟨hle, _⟩
  · exact hb
  · omega

theorem bit_eq_toNat (x k : Nat) : x / 2 ^ k % 2 = (x.testBit k).toNat :=
  (Nat.toNat_testBit x k).symm

/-- The empty window, anywhere. -/
theorem window_empty (s : List U8) (P : ℤ) : Window s 0 0 P := by
  intro k _
  right
  simp

/-- One byte of the stream from bit `bit` on, as a window at that position. -/
theorem window_byte (s : List U8) (b bit : Nat) (hb : b < s.length) (hbit : bit < 8) :
    Window s ((s[b]!).val / 2 ^ bit) (8 - bit) (8 * (b : ℤ) + bit) := by
  intro k hk
  rw [shift_bit]
  by_cases hlt : bit + k < 8
  · left
    have hdiv : (8 * (b : ℤ) + bit + k) / 8 = ((b : Nat) : ℤ) := by omega
    have hmod : (8 * (b : ℤ) + bit + k) % 8 = ((bit + k : Nat) : ℤ) := by push_cast; omega
    refine ⟨trivial, ⟨by omega, by omega⟩, ?_⟩
    rw [hdiv, hmod, Int.toNat_natCast, Int.toNat_natCast]
    push_cast
    rfl
  · right
    refine ⟨by omega, ?_⟩
    have hlt256 : (s[b]!).val < 2 ^ (bit + k) := by
      have h8 : (2 : Nat) ^ 8 ≤ 2 ^ (bit + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := (s[b]!).hBounds
      scalar_tac
    rw [Nat.div_eq_of_lt hlt256]

/-- Consuming `bits` bits of a window: the rest is a window `bits` further on. -/
theorem window_skip (s : List U8) (buf nbits bits : Nat) (P : ℤ) (h : Window s buf nbits P)
    (hbuf : buf < 2 ^ 64) (hn : nbits ≤ 64) (hbits : bits ≤ nbits) :
    Window s (buf >>> bits) (nbits - bits) (P + bits) := by
  intro k hk
  rw [Nat.shiftRight_eq_div_pow, shift_bit]
  by_cases hlt : bits + k < 64
  · rcases h (bits + k) hlt with hb | ⟨hle, hz⟩
    · left
      have he : P + (bits : ℤ) + (k : ℤ) = P + ((bits + k : Nat) : ℤ) := by push_cast; ring
      rw [he]
      exact hb
    · right
      exact ⟨by omega, hz⟩
  · right
    refine ⟨by omega, ?_⟩
    have hlt2 : buf < 2 ^ (bits + k) := by
      have h64 : (2 : Nat) ^ 64 ≤ 2 ^ (bits + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [Nat.div_eq_of_lt hlt2]

/-- Oring the stream's bits from `P + nbits` on in above the window's bits gives a window
whose 64 bits are all the stream's. -/
theorem window_refill (s : List U8) (buf nbits w y : Nat) (P : ℤ) (h : Window s buf nbits P)
    (hw : ∀ j : Nat, j < 64 → bit_spec s (P + nbits + j) ((w / 2 ^ j % 2 : Nat) : ℤ))
    (hn : nbits < 64) (hy : y = (w <<< nbits) % 2 ^ 64) :
    ∀ k : Nat, k < 64 → bit_spec s (P + k) (((buf ||| y) / 2 ^ k % 2 : Nat) : ℤ) := by
  intro k hk
  rw [bit_eq_toNat, Nat.testBit_or, hy, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  by_cases hlt : k < nbits
  · have hd : decide (k ≥ nbits) = false := by simp; omega
    rw [hd]
    simp only [Bool.false_and, Bool.and_false, Bool.or_false]
    rcases h k hk with hb | ⟨hle, _⟩
    · rw [bit_eq_toNat] at hb
      exact hb
    · omega
  · have hd : decide (k ≥ nbits) = true := by simp; omega
    have hd2 : decide (k < 64) = true := by simp; omega
    rw [hd, hd2]
    simp only [Bool.true_and]
    have hwb := hw (k - nbits) (by omega)
    have he : P + (nbits : ℤ) + ((k - nbits : Nat) : ℤ) = P + k := by
      rw [Nat.cast_sub (by omega)]; ring
    rw [he, bit_eq_toNat] at hwb
    rcases h k hk with hb | ⟨_, hz⟩
    · rw [bit_eq_toNat] at hb
      have heq := bit_unique _ _ _ _ hb hwb
      have heq2 : buf.testBit k = w.testBit (k - nbits) := by
        cases hb' : buf.testBit k <;> cases hw' : w.testBit (k - nbits) <;> simp_all
      rw [heq2, Bool.or_self]
      exact hwb
    · rw [bit_eq_toNat] at hz
      have hz2 : buf.testBit k = false := by
        cases hb' : buf.testBit k <;> simp_all
      rw [hz2, Bool.false_or]
      exact hwb

end Gzip.Proofs.Decode.WindowFacts
