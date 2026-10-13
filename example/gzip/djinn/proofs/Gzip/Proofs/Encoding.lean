import Gzip.Proofs.Copies
import Gzip.Proofs.Plans

open Aeneas Std Result
open Gzip.Spec Gzip.Proofs.Writer Gzip.Proofs.Huffman Gzip.Proofs.Symbols Gzip.Proofs.Matches Gzip.Proofs.Indices

namespace Gzip.Proofs.Encoding

inductive Encodes (data : List U8) : ℕ → ℕ → List Bool → Prop
  | finish (p : ℕ) : Encodes data p p (Symbols.encode 256)
  | literal (p q : ℕ) (bits : List Bool) (hp : p < data.length)
      (tail : Encodes data (p + 1) q bits) :
      Encodes data p q (Symbols.encode data[p]!.val ++ bits)
  | copy (p q len dist l d : ℕ) (bits : List Bool)
      (valid : 3 ≤ len ∧ len ≤ 258 ∧ p + len ≤ data.length ∧
        0 < dist ∧ dist ≤ p ∧ dist ≤ 32768 ∧ EqualRun data p (p - dist) len)
      (indices : l ≤ 28 ∧ d ≤ 29 ∧ lb l ≤ len ∧ db d ≤ dist ∧
        len - lb l < 2 ^ le l ∧ dist - db d < 2 ^ de d)
      (tail : Encodes data (p + len) q bits) :
      Encodes data p q (Copies.encode len dist l d ++ bits)

theorem append_take (data : List U8) (p : ℕ) (hp : p < data.length) :
    append_spec (data.take p) data[p]!.val (data.take (p + 1)) := by
  have hplen : (data.take p).length = p := List.length_take_of_le (by omega)
  have hnlen : (data.take (p + 1)).length = p + 1 := List.length_take_of_le (by omega)
  refine ⟨trivial, by rw [hplen, hnlen]; omega, ?_, ?_⟩
  · simp only [List.drop_zero, Int.toNat_natCast, hplen, List.take_take,
      Nat.min_eq_left (show p ≤ p + 1 by omega)]
  · simp only [Int.toNat_natCast, hplen]
    rw [getElem!_pos (data.take (p + 1)) p (by rw [hnlen]; omega), List.getElem_take,
      getElem!_pos data p hp]

theorem decode {data : List U8} {p q : ℕ} {bits : List Bool} (h : Encodes data p q bits)
    (s : List U8) (front tail : List Bool)
    (hs : byteBits s = front ++ bits ++ tail) :
    ∃ tokens : List Gzip.Proofs.Encoder.Token,
      Gzip.Proofs.Encoder.Writes s fixedLengths distanceLengths front.length (data.take p)
        tokens (data.take q) (front.length + bits.length) := by
  induction h generalizing front with
  | finish p =>
      have hsym := Symbols.decode s front tail 256 (by omega) hs
      have hwidth := width_eq 256 (by omega)
      have hn : (Symbols.encode 256).length = 7 := by norm_num [Symbols.encode, Symbols.width]
      have hw : (fixedLengths[256]!).val = 7 := by norm_num [Symbols.width] at hwidth; exact hwidth
      have hsz := congrArg List.length hs
      simp only [byteBits_length, List.length_append, hn] at hsz
      refine ⟨[], Gzip.Proofs.Encoder.Writes.finish front.length (front.length + 7) (data.take p)
        hsym ?_ ⟨by omega, by omega⟩⟩
      change (front.length : ℤ) + 7 = (front.length : ℤ) + (fixedLengths[256]!).val
      rw [hw]
  | literal p q bits hp ht ih =>
      have hsym := Symbols.decode s front (bits ++ tail) data[p]!.val (by scalar_tac)
        (by simpa only [List.append_assoc] using hs)
      have hsz := congrArg List.length hs
      simp only [byteBits_length, Symbols.encode, List.length_append, List.length_reverse,
        lowBits_length] at hsz
      have hw := width_eq data[p]!.val (by scalar_tac)
      have hwpos : 0 < Symbols.width data[p]!.val := by unfold Symbols.width; split_ifs <;> omega
      obtain ⟨tokens, htail⟩ := ih (front ++ Symbols.encode data[p]!.val)
        (by simpa only [List.append_assoc] using hs)
      refine ⟨.literal data[p]! :: tokens, ?_⟩
      apply Gzip.Proofs.Encoder.Writes.literal
        (a := front.length + (Symbols.encode data[p]!.val).length)
        (mid := data.take (p + 1))
      · exact hsym
      · simp only [Symbols.encode, List.length_reverse, lowBits_length, hw]
      · simp only [Symbols.encode, List.length_reverse, lowBits_length]
        constructor <;> omega
      · exact append_take data p hp
      · simpa only [List.length_append, Nat.cast_add, List.append_assoc, Int.add_assoc] using htail
  | copy p q len dist l d bits hm hi ht ih =>
      obtain ⟨tokens, htail⟩ := ih (front ++ Copies.encode len dist l d)
        (by simpa only [List.append_assoc] using hs)
      have hcopy := copy_of_equal_run data p (p - dist) len (by omega) (by omega) hm.2.2.2.2.2.2
      have he : p - (p - dist) = dist := by omega
      rw [he] at hcopy
      refine ⟨.copy dist len :: tokens, ?_⟩
      exact Copies.decode s (data.take p) (data.take (p + len)) (data.take q) front (bits ++ tail)
        len dist l d tokens _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2
        (by simpa only [List.append_assoc] using hs) hcopy
        (by simpa only [List.length_append, Nat.cast_add, List.append_assoc, Int.add_assoc] using htail)

end Gzip.Proofs.Encoding
