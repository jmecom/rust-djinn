import Gzip.Proofs.Symbols
import Gzip.Proofs.Indices
import Gzip.Proofs.Tables
import Gzip.Proofs.Encoder

open Aeneas Std Result
open Gzip.solution Gzip.Spec Gzip.Proofs.Writer Gzip.Proofs.Symbols Gzip.Proofs.Indices Gzip.Proofs.Huffman

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

namespace Gzip.Proofs.Copies

attribute [local step] bits_stream code_stream

def encode (len dist l d : ℕ) : List Bool :=
  Symbols.encode (257 + l) ++ lowBits (len - lb l) (le l) ++
    (lowBits d 5).reverse ++ lowBits (dist - db d) (de d)

theorem copy_stream (self : Gzip.solution.Writer) (len dist : Usize)
    (hl0 : 3 ≤ len.val) (hl1 : len.val ≤ 258) (hd0 : 1 ≤ dist.val) (hd1 : dist.val ≤ 32768)
    (hs : self.count.val < 32) (hw : self.bits.val < 2 ^ self.count.val)
    (hb : self.out.val.length + 24 ≤ Usize.max) :
    Gzip.solution.Writer.copy self len dist ⦃ r =>
      ∃ l d : ℕ, l ≤ 28 ∧ d ≤ 29 ∧ lb l ≤ len.val ∧ db d ≤ dist.val ∧
        len.val - lb l < 2 ^ le l ∧ dist.val - db d < 2 ^ de d ∧
        byteBits r.out.val ++ lowBits r.bits.val r.count.val =
          (byteBits self.out.val ++ lowBits self.bits.val self.count.val) ++ encode len.val dist.val l d ∧
        r.count.val < 32 ∧ r.bits.val < 2 ^ r.count.val ⦄ := by
  unfold Gzip.solution.Writer.copy
  have hlSpec := Gzip.Proofs.Tables.length_code_spec len hl0 hl1
  step as ⟨l, hl, hlb, hlf⟩
  have hdSpec := Gzip.Proofs.Tables.distance_code_spec dist hd0 hd1
  step as ⟨d, hd, hdb, hdf⟩
  have hlget := lb_get l (by omega)
  have hdget := db_get d (by omega)
  have hle := Gzip.Proofs.Costs.length_extra_bound l.val (by omega)
  have hde := Gzip.Proofs.Costs.distance_extra_bound d.val (by omega)
  have hlen : l.val < LENGTH_EXTRA.val.length := by simp [LENGTH_EXTRA, Array.make]; omega
  have hdist : d.val < DIST_EXTRA.val.length := by simp [DIST_EXTRA, Array.make]; omega
  rw [getElem!_pos LENGTH_EXTRA.val l.val hlen] at hle
  rw [getElem!_pos DIST_EXTRA.val d.val hdist] at hde
  step as ⟨i, hi⟩
  step as ⟨self1, hstream1, hcount1, hword1⟩
  have hwidth : Symbols.width i.val ≤ 9 := by
    unfold Symbols.width
    split_ifs <;> omega
  have hsz1 := congrArg List.length hstream1
  simp only [List.length_append, byteBits_length, lowBits_length, Symbols.encode,
    List.length_reverse] at hsz1
  have hout1 : self1.out.val.length ≤ self.out.val.length + 6 := by omega
  step as ⟨i1, hi1⟩
  have hlval : i1.val = lb l.val := by rw [hi1, hlget]
  step as ⟨i2, hi2, _⟩
  step as ⟨i3, hi3⟩
  step as ⟨i4, hi4⟩
  have hleval : i4.val = le l.val := by
    rw [hi4]
    unfold le
    rw [getElem!_pos LENGTH_EXTRA.val l.val hlen]
  have hi3val : i3.val = len.val - lb l.val := by scalar_tac
  step as ⟨self2, hstream2, hcount2, hword2⟩
  have hsz2 := congrArg List.length hstream2
  simp only [List.length_append, byteBits_length, lowBits_length] at hsz2
  have hout2 : self2.out.val.length ≤ self.out.val.length + 11 := by scalar_tac
  step as ⟨i5, hi5⟩
  step as ⟨self3, hstream3, hcount3, hword3⟩
  have hsz3 := congrArg List.length hstream3
  simp only [List.length_append, byteBits_length, lowBits_length, List.length_reverse] at hsz3
  have hout3 : self3.out.val.length ≤ self.out.val.length + 16 := by scalar_tac
  step as ⟨i6, hi6⟩
  have hdval : i6.val = db d.val := by rw [hi6, hdget]
  step as ⟨i7, hi7, _⟩
  step as ⟨i8, hi8⟩
  step as ⟨i9, hi9⟩
  have hdeval : i9.val = de d.val := by
    rw [hi9]
    unfold de
    rw [getElem!_pos DIST_EXTRA.val d.val hdist]
  have hi8val : i8.val = dist.val - db d.val := by scalar_tac
  step*
  refine ⟨l.val, d.val, hl, hd, hlb, hdb, hlf, hdf, ?_, r_post1, r_post2⟩
  rw [r_post, hstream3, hstream2, hstream1]
  have hi5val : i5.val = d.val := by scalar_tac
  simp only [encode, hi, hi3val, hleval, hi5val, hi8val, hdeval, List.append_assoc,
    Nat.add_comm l.val 257]

theorem distance_decode (s : List U8) (front tail : List Bool) (d : ℕ) (hd : d < 32)
    (hstream : byteBits s = front ++ (lowBits d 5).reverse ++ tail) :
    symbol_spec s front.length distanceLengths d := by
  have hwidth : (distanceLengths[d]!).val = 5 := by
    rw [getElem!_pos distanceLengths d (by simp only [distanceLengths, List.length_replicate]; omega)]
    simp only [distanceLengths, List.getElem_replicate]
    scalar_tac
  refine ⟨trivial, ⟨by omega, by simp only [distanceLengths, List.length_replicate]; omega⟩,
    ?_, d, distance_codeword d hd, ?_⟩
  · simp only [Int.toNat_natCast, hwidth]
    norm_num
  · simp only [Int.toNat_natCast, hwidth]
    exact code_at_prefix s front tail d 5 hstream (by omega)

theorem decode (s prev mid out : List U8) (front tail : List Bool)
    (len dist l d : ℕ) (rest : List Gzip.Proofs.Encoder.Token) (endBit : ℤ)
    (hl : l ≤ 28) (hd : d ≤ 29) (hlb : lb l ≤ len) (hdb : db d ≤ dist)
    (hlf : len - lb l < 2 ^ le l) (hdf : dist - db d < 2 ^ de d)
    (hstream : byteBits s = front ++ encode len dist l d ++ tail)
    (hcopy : copy_spec prev dist len mid)
    (hrest : Gzip.Proofs.Encoder.Writes s fixedLengths distanceLengths
      (front.length + (encode len dist l d).length) mid rest out endBit) :
    Gzip.Proofs.Encoder.Writes s fixedLengths distanceLengths front.length prev
      (.copy dist len :: rest) out endBit := by
  let sym := 257 + l
  have hsym : sym < 288 := by dsimp [sym]; omega
  have hsbits := Symbols.decode s front
    (lowBits (len - lb l) (le l) ++ (lowBits d 5).reverse ++ lowBits (dist - db d) (de d) ++ tail)
    sym hsym (by simpa only [sym, encode, List.append_assoc] using hstream)
  have hlfield := field_at_prefix s (front ++ Symbols.encode sym)
    ((lowBits d 5).reverse ++ lowBits (dist - db d) (de d) ++ tail)
    (len - lb l) (le l) (by simpa only [sym, encode, List.append_assoc] using hstream) hlf
  have hdsymbol := distance_decode s (front ++ Symbols.encode sym ++ lowBits (len - lb l) (le l))
    (lowBits (dist - db d) (de d) ++ tail) d (by omega)
    (by simpa only [sym, encode, List.append_assoc] using hstream)
  have hdfield := field_at_prefix s
    (front ++ Symbols.encode sym ++ lowBits (len - lb l) (le l) ++ (lowBits d 5).reverse)
    tail (dist - db d) (de d) (by simpa only [sym, encode, List.append_assoc] using hstream) hdf
  have hwidth := width_eq sym hsym
  have hdwidth : (distanceLengths[d]!).val = 5 := by
    rw [getElem!_pos distanceLengths d (by simp only [distanceLengths, List.length_replicate]; omega)]
    simp only [distanceLengths, List.getElem_replicate]
    scalar_tac
  have hwpos : 0 < Symbols.width sym := by unfold Symbols.width; split_ifs <;> omega
  have hsz := congrArg List.length hstream
  simp only [encode, Symbols.encode, List.length_append, byteBits_length,
    List.length_reverse, lowBits_length] at hsz
  simp only [Symbols.encode, List.length_append, List.length_reverse, lowBits_length,
    Nat.cast_add] at hlfield hdsymbol hdfield
  dsimp only [sym] at *
  have hidx : (257 + (l : ℤ)).toNat = 257 + l := by omega
  apply Gzip.Proofs.Encoder.Writes.copy
    (i := front.length) (a := front.length + Symbols.width (257 + l))
    (b := front.length + Symbols.width (257 + l) + le l)
    (c := front.length + (encode len dist l d).length)
    (k := l) (dc := d) (lb := lb l) (le := le l) (lx := ((len - lb l : ℕ) : ℤ))
    (db := db d) (de := de d) (dx := ((dist - db d : ℕ) : ℤ))
  · exact hsbits
  · rw [hidx, hwidth]
  · constructor <;> omega
  · exact lbase_correct l (by omega)
  · exact lextra_correct l (by omega)
  · exact hlfield
  · omega
  · rfl
  · exact hdsymbol
  · exact dbase_correct d (by omega)
  · exact dextra_correct d (by omega)
  · simpa only [Int.toNat_natCast, hdwidth] using hdfield
  · omega
  · simp only [encode, Symbols.encode, List.length_append, List.length_reverse,
      lowBits_length, Nat.cast_add, sym, Int.toNat_natCast, hdwidth]
    omega
  · simp only [encode, Symbols.encode, List.length_append, List.length_reverse,
      lowBits_length]
    constructor <;> omega
  · exact hcopy
  · exact hrest

end Gzip.Proofs.Copies
