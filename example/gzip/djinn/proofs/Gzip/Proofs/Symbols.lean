import Gzip.Proofs.Bits
import Gzip.Proofs.Huffman

open Aeneas Std Result
open Gzip.solution Gzip.Spec Gzip.Proofs.Huffman Gzip.Proofs.Writer

set_option maxRecDepth 2000

namespace Gzip.Proofs.Symbols

attribute [local step] code_stream

def distanceLengths : List U8 := List.replicate 32 5#u8

theorem distance_canonical : ∀ sym : Fin 32, canonical distanceLengths sym.val = sym.val := by decide

theorem distance_codeword (sym : ℕ) (hs : sym < 32) : codeword_spec distanceLengths sym sym := by
  have h := canonical_correct distanceLengths sym (by simpa only [distanceLengths, List.length_replicate] using hs)
  rw [distance_canonical ⟨sym, hs⟩] at h
  exact h

theorem distance_lengths : fixeddist_spec distanceLengths := by
  refine ⟨trivial, by simp [distanceLengths], ?_⟩
  intro l hl
  have he : l = 5#u8 := List.eq_of_mem_replicate hl
  subst l
  scalar_tac

def width (sym : ℕ) : ℕ :=
  if sym < 144 then 8 else if sym < 256 then 9 else if sym < 280 then 7 else 8

def encode (sym : ℕ) : List Bool := (lowBits (fixedWord sym) (width sym)).reverse

theorem width_eq (sym : ℕ) (hsym : sym < 288) :
    (fixedLengths[sym]!).val = width sym := by
  rw [getElem!_pos fixedLengths sym (by simpa only [fixedLengths, List.length_ofFn] using hsym)]
  simp only [fixedLengths, List.getElem_ofFn, width]
  split_ifs <;> scalar_tac

theorem word_bound (sym : ℕ) (hsym : sym < 288) : fixedWord sym < 2 ^ width sym := by
  unfold fixedWord width
  split_ifs <;> omega

theorem decode (s : List U8) (front tail : List Bool) (sym : ℕ) (hsym : sym < 288)
    (hstream : byteBits s = front ++ encode sym ++ tail) :
    symbol_spec s front.length fixedLengths sym := by
  refine ⟨trivial, ⟨by omega, by simp only [fixedLengths, List.length_ofFn]; omega⟩,
    ?_, fixedWord sym, fixed_codeword sym hsym, ?_⟩
  · simp only [Int.toNat_natCast, width_eq sym hsym]
    unfold width
    split_ifs <;> norm_num
  simp only [Int.toNat_natCast, width_eq sym hsym]
  exact code_at_prefix s front tail (fixedWord sym) (width sym) hstream (word_bound sym hsym)

@[step]
theorem symbol_stream (self : Gzip.solution.Writer) (sym : Usize)
    (hsym : sym.val < 288) (hs : self.count.val < 32)
    (hw : self.bits.val < 2 ^ self.count.val)
    (hb : self.out.val.length + 8 ≤ Usize.max) :
    Gzip.solution.Writer.symbol self sym ⦃ r =>
      byteBits r.out.val ++ lowBits r.bits.val r.count.val =
        (byteBits self.out.val ++ lowBits self.bits.val self.count.val) ++ encode sym.val ∧
      r.count.val < 32 ∧ r.bits.val < 2 ^ r.count.val ⦄ := by
  unfold Gzip.solution.Writer.symbol
  step*
  all_goals refine ⟨?_, r_post1, r_post2⟩
  all_goals rw [r_post]
  all_goals apply congrArg (fun bits => (byteBits self.out.val ++ lowBits self.bits.val self.count.val) ++ bits)
  all_goals unfold encode
  all_goals congr 2 <;> simp only [fixedWord, width] <;> split_ifs <;> scalar_tac

end Gzip.Proofs.Symbols
