import Gzip.Proofs.Codes
import Gzip.Proofs.Encoding

open Aeneas Std Result
open Gzip.Spec Gzip.Proofs.Writer Gzip.Proofs.Codes Gzip.Proofs.Indices Gzip.Proofs.Matches

namespace Gzip.Proofs.Dyn

/-- A code table as the block's tables carry it. -/
structure Tab where
  lens : List U8
  words : List Usize

def encodeCopy (lit dist : Tab) (len d l dc : ℕ) : List Bool :=
  encodeSym lit.lens lit.words (257 + l) ++ lowBits (len - lb l) (le l) ++
    encodeSym dist.lens dist.words dc ++ lowBits (d - db dc) (de dc)

/-- The bits a plan writes under two tables, with the facts the decoder needs about every
    symbol used: within the table and of nonzero length. -/
inductive Encodes (lit dist : Tab) (data : List U8) : ℕ → ℕ → List Bool → Prop
  | finish (p : ℕ) (h : 256 < lit.lens.length ∧ 1 ≤ (lit.lens[256]!).val) :
      Encodes lit dist data p p (encodeSym lit.lens lit.words 256)
  | literal (p q : ℕ) (bits : List Bool) (hp : p < data.length)
      (hs : (data[p]!).val < lit.lens.length ∧ 1 ≤ (lit.lens[(data[p]!).val]!).val)
      (tail : Encodes lit dist data (p + 1) q bits) :
      Encodes lit dist data p q (encodeSym lit.lens lit.words (data[p]!).val ++ bits)
  | copy (p q len d l dc : ℕ) (bits : List Bool)
      (valid : 3 ≤ len ∧ len ≤ 258 ∧ p + len ≤ data.length ∧
        0 < d ∧ d ≤ p ∧ d ≤ 32768 ∧ EqualRun data p (p - d) len)
      (indices : l ≤ 28 ∧ dc ≤ 29 ∧ lb l ≤ len ∧ db dc ≤ d ∧
        len - lb l < 2 ^ le l ∧ d - db dc < 2 ^ de dc)
      (hs : 257 + l < lit.lens.length ∧ 1 ≤ (lit.lens[257 + l]!).val ∧
        dc < dist.lens.length ∧ 1 ≤ (dist.lens[dc]!).val)
      (tail : Encodes lit dist data (p + len) q bits) :
      Encodes lit dist data p q (encodeCopy lit dist len d l dc ++ bits)

theorem decode {lit dist : Tab} {data : List U8} {p q : ℕ} {bits : List Bool}
    (hlit : TableOk lit.lens lit.words 15) (hdist : TableOk dist.lens dist.words 15)
    (h : Encodes lit dist data p q bits) (s : List U8) (front tail : List Bool)
    (hs : byteBits s = front ++ bits ++ tail) :
    ∃ tokens : List Encoder.Token,
      Encoder.Writes s lit.lens dist.lens front.length (data.take p) tokens (data.take q)
        (front.length + bits.length) := by
  induction h generalizing front with
  | finish p h256 =>
      have hsym := symbol_decode s front tail lit.lens lit.words 15 256 hlit h256.1 h256.2 hs
      have hsz := congrArg List.length hs
      simp only [byteBits_length, List.length_append, encodeSym_length] at hsz
      refine ⟨[], Encoder.Writes.finish front.length
        (front.length + (encodeSym lit.lens lit.words 256).length) (data.take p) hsym ?_
        ⟨by simp only [encodeSym_length]; omega, by simp only [encodeSym_length]; omega⟩⟩
      simp only [encodeSym_length, Nat.cast_add]
  | literal p q bits hp hsy ht ih =>
      have hsym := symbol_decode s front (bits ++ tail) lit.lens lit.words 15 (data[p]!).val hlit
        hsy.1 hsy.2 (by simpa only [List.append_assoc] using hs)
      have hsz := congrArg List.length hs
      simp only [byteBits_length, List.length_append, encodeSym_length] at hsz
      obtain ⟨tokens, htail⟩ := ih (front ++ encodeSym lit.lens lit.words (data[p]!).val)
        (by simpa only [List.append_assoc] using hs)
      refine ⟨.literal data[p]! :: tokens, ?_⟩
      apply Encoder.Writes.literal
        (a := front.length + (lit.lens[(data[p]!).val]!).val) (mid := data.take (p + 1))
      · exact hsym
      · simp only [Int.toNat_natCast, Nat.cast_add]
      · constructor <;> omega
      · exact Encoding.append_take data p hp
      · simpa only [List.length_append, encodeSym_length, Nat.cast_add, List.append_assoc,
          Int.add_assoc] using htail
  | copy p q len d l dc bits hm hi hsy ht ih =>
      obtain ⟨tokens, htail⟩ := ih (front ++ encodeCopy lit dist len d l dc)
        (by simpa only [List.append_assoc] using hs)
      have hcopy := copy_of_equal_run data p (p - d) len (by omega) (by omega) hm.2.2.2.2.2.2
      have he : p - (p - d) = d := by omega
      rw [he] at hcopy
      refine ⟨.copy d len :: tokens, ?_⟩
      have hsbits := symbol_decode s front
        (lowBits (len - lb l) (le l) ++ encodeSym dist.lens dist.words dc ++
          lowBits (d - db dc) (de dc) ++ bits ++ tail)
        lit.lens lit.words 15 (257 + l) hlit hsy.1 hsy.2.1
        (by simpa only [encodeCopy, List.append_assoc] using hs)
      have hlfield := field_at_prefix s (front ++ encodeSym lit.lens lit.words (257 + l))
        (encodeSym dist.lens dist.words dc ++ lowBits (d - db dc) (de dc) ++ bits ++ tail)
        (len - lb l) (le l) (by simpa only [encodeCopy, List.append_assoc] using hs) hi.2.2.2.2.1
      have hdsymbol := symbol_decode s
        (front ++ encodeSym lit.lens lit.words (257 + l) ++ lowBits (len - lb l) (le l))
        (lowBits (d - db dc) (de dc) ++ bits ++ tail) dist.lens dist.words 15 dc hdist
        hsy.2.2.1 hsy.2.2.2 (by simpa only [encodeCopy, List.append_assoc] using hs)
      have hdfield := field_at_prefix s
        (front ++ encodeSym lit.lens lit.words (257 + l) ++ lowBits (len - lb l) (le l) ++
          encodeSym dist.lens dist.words dc)
        (bits ++ tail) (d - db dc) (de dc) (by simpa only [encodeCopy, List.append_assoc] using hs)
        hi.2.2.2.2.2
      have hsz := congrArg List.length hs
      simp only [encodeCopy, List.length_append, byteBits_length, encodeSym_length,
        lowBits_length] at hsz
      simp only [List.length_append, encodeSym_length, lowBits_length, Nat.cast_add]
        at hlfield hdsymbol hdfield
      have hidx : (257 + (l : ℤ)).toNat = 257 + l := by omega
      have hwpos := hsy.2.1
      have hdpos := hsy.2.2.2
      apply Encoder.Writes.copy
        (i := front.length) (a := front.length + (lit.lens[257 + l]!).val)
        (b := front.length + (lit.lens[257 + l]!).val + le l)
        (c := front.length + (encodeCopy lit dist len d l dc).length)
        (k := l) (dc := dc) (lb := lb l) (le := le l) (lx := ((len - lb l : ℕ) : ℤ))
        (db := db dc) (de := de dc) (dx := ((d - db dc : ℕ) : ℤ))
      · exact hsbits
      · rw [hidx]
      · constructor <;> omega
      · exact lbase_correct l (by omega)
      · exact lextra_correct l (by omega)
      · exact hlfield
      · omega
      · rfl
      · exact hdsymbol
      · exact dbase_correct dc (by omega)
      · exact dextra_correct dc (by omega)
      · simpa only [Int.toNat_natCast] using hdfield
      · omega
      · simp only [encodeCopy, List.length_append, encodeSym_length, lowBits_length,
          Nat.cast_add, Int.toNat_natCast]
        omega
      · simp only [encodeCopy, List.length_append, encodeSym_length, lowBits_length]
        constructor <;> omega
      · exact hcopy
      · simpa only [List.length_append, Nat.cast_add, List.append_assoc, Int.add_assoc] using htail

/-- Bits already written for the tokens from `start` to `p`: whatever encodes the rest
    extends them to an encoding from `start`. -/
def Emitted (lit dist : Tab) (data : List U8) (start p : ℕ) (bits : List Bool) : Prop :=
  ∀ q tail, Encodes lit dist data p q tail → Encodes lit dist data start q (bits ++ tail)

theorem emitted_nil (lit dist : Tab) (data : List U8) (p : ℕ) : Emitted lit dist data p p [] := by
  intro q tail h
  exact h

theorem emitted_literal {lit dist : Tab} {data : List U8} {start p : ℕ} {bits : List Bool}
    (h : Emitted lit dist data start p bits) (hp : p < data.length)
    (hs : (data[p]!).val < lit.lens.length ∧ 1 ≤ (lit.lens[(data[p]!).val]!).val) :
    Emitted lit dist data start (p + 1) (bits ++ encodeSym lit.lens lit.words (data[p]!).val) := by
  intro q tail ht
  simpa only [List.append_assoc] using h q _ (Encodes.literal p q tail hp hs ht)

theorem emitted_copy {lit dist : Tab} {data : List U8} {start p len d l dc : ℕ} {bits : List Bool}
    (h : Emitted lit dist data start p bits)
    (hm : 3 ≤ len ∧ len ≤ 258 ∧ p + len ≤ data.length ∧
      0 < d ∧ d ≤ p ∧ d ≤ 32768 ∧ EqualRun data p (p - d) len)
    (hi : l ≤ 28 ∧ dc ≤ 29 ∧ lb l ≤ len ∧ db dc ≤ d ∧
      len - lb l < 2 ^ le l ∧ d - db dc < 2 ^ de dc)
    (hs : 257 + l < lit.lens.length ∧ 1 ≤ (lit.lens[257 + l]!).val ∧
      dc < dist.lens.length ∧ 1 ≤ (dist.lens[dc]!).val) :
    Emitted lit dist data start (p + len) (bits ++ encodeCopy lit dist len d l dc) := by
  intro q tail ht
  simpa only [List.append_assoc] using h q _ (Encodes.copy p q len d l dc tail hm hi hs ht)

/-- A dynamic block decodes like a fixed one: the tables, then the symbols. -/
theorem block_decode {s prev out lit dist : List U8} {i j k : ℤ} {plan : List Encoder.Token}
    (hzero : ¬ field_spec s i 2 0) (hone : ¬ field_spec s i 2 1) (htwo : field_spec s i 2 2)
    (ht : tables_spec s (i + 2) lit dist k) (hw : Encoder.Writes s lit dist k prev plan out j) :
    block_spec s i prev out j := by
  refine ⟨trivial, fun h => False.elim (hzero h), fun _ => ⟨fun h => False.elim (hone h), fun _ => ?_⟩⟩
  exact ⟨htwo, lit, dist, k, ht, Encoder.writes_decode hw⟩

end Gzip.Proofs.Dyn
