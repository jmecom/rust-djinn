import Gzip.Proofs.Bits
import Gzip.Proofs.Huffman

open Aeneas Std Result
open Gzip.Spec Gzip.Proofs.Writer Gzip.Proofs.Huffman

namespace Gzip.Proofs.Codes

/-- What the decoder needs of a code table: for every used symbol, a length within the limit
    and the canonical codeword, below 2^length. -/
def TableOk (lens : List U8) (words : List Usize) (limit : ℕ) : Prop :=
  words.length = lens.length ∧
  ∀ sym, sym < lens.length → 1 ≤ (lens[sym]!).val →
    (lens[sym]!).val ≤ limit ∧ (words[sym]!).val = canonical lens sym ∧
    (words[sym]!).val < 2 ^ (lens[sym]!).val

/-- Not oversubscribed: every length within the limit and the Kraft sum within one. -/
def Kraft (lens : List U8) (limit : ℕ) : Prop :=
  (∀ sym, sym < lens.length → (lens[sym]!).val ≤ limit) ∧
  shorter lens (limit + 1) lens.length ≤ 2 ^ (limit + 1)

theorem kraft_valid (lens : List U8) (limit : ℕ) (h : Kraft lens limit) :
    valid_spec lens limit true := by
  refine ⟨by unfold valid_pre; omega, ?_⟩
  constructor
  · intro _
    refine ⟨?_, (shorter lens (limit + 1) lens.length : ℕ), ?_, ?_⟩
    · intro l hl
      obtain ⟨k, hk, hlk⟩ := List.getElem_of_mem hl
      have hb := h.1 k hk
      rw [getElem!_pos lens k hk, hlk] at hb
      exact_mod_cast hb
    · have hc := shorter_correct lens (limit + 1) lens.length (Nat.le_refl _)
      have he : ((limit : ℤ) + 1) = ((limit + 1 : ℕ) : ℤ) := by push_cast; rfl
      rw [he]
      exact hc
    · rw [show ((limit : ℤ) + 1).toNat = limit + 1 by omega]
      exact_mod_cast h.2
  · intro _
    rfl

/-- A symbol's bits as the writer emits them: the codeword, most significant bit first. -/
def encodeSym (lens : List U8) (words : List Usize) (sym : ℕ) : List Bool :=
  (lowBits (words[sym]!).val (lens[sym]!).val).reverse

@[simp] theorem encodeSym_length (lens : List U8) (words : List Usize) (sym : ℕ) :
    (encodeSym lens words sym).length = (lens[sym]!).val := by
  simp [encodeSym]

theorem symbol_decode (s : List U8) (front tail : List Bool) (lens : List U8) (words : List Usize)
    (limit sym : ℕ) (ht : TableOk lens words limit) (hs : sym < lens.length)
    (hpos : 1 ≤ (lens[sym]!).val)
    (hstream : byteBits s = front ++ encodeSym lens words sym ++ tail) :
    symbol_spec s front.length lens sym := by
  obtain ⟨_, hw, hb⟩ := ht.2 sym hs hpos
  refine ⟨trivial, ⟨by omega, by omega⟩, by simp only [Int.toNat_natCast]; omega,
    canonical lens sym, canonical_correct lens sym hs, ?_⟩
  simp only [Int.toNat_natCast]
  rw [← hw]
  exact code_at_prefix s front tail _ _ hstream hb

/-- The reversed codewords the writer emits with `bits`. -/
def RevOk (lens : List U8) (words : List Usize) (rev : List U32) : Prop :=
  rev.length = lens.length ∧
  ∀ sym, sym < lens.length → 1 ≤ (lens[sym]!).val → (lens[sym]!).val ≤ 16 →
    (rev[sym]!).val = reverse16 (words[sym]!).val / 2 ^ (16 - (lens[sym]!).val)

theorem rev_bits (lens : List U8) (words : List Usize) (rev : List U32) (sym : ℕ)
    (h : RevOk lens words rev) (hs : sym < lens.length) (hpos : 1 ≤ (lens[sym]!).val)
    (hlim : (lens[sym]!).val ≤ 16) :
    lowBits (rev[sym]!).val (lens[sym]!).val = encodeSym lens words sym := by
  rw [encodeSym, h.2 sym hs hpos hlim]
  exact reverse16_partial _ _ hlim

theorem rev_bound (lens : List U8) (words : List Usize) (rev : List U32) (sym : ℕ)
    (h : RevOk lens words rev) (hs : sym < lens.length) (hpos : 1 ≤ (lens[sym]!).val)
    (hlim : (lens[sym]!).val ≤ 16) :
    (rev[sym]!).val < 2 ^ (lens[sym]!).val := by
  rw [h.2 sym hs hpos hlim]
  exact reverse16_partial_bound _ _ hlim

end Gzip.Proofs.Codes
