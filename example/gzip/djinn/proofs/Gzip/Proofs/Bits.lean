import Gzip.Proofs.Writer
import Gzip.Spec
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases

open Aeneas Std Result

namespace Gzip.Proofs.Writer

def lowBits (word count : ℕ) : List Bool := List.ofFn fun i : Fin count => word.testBit i.val

@[simp] theorem lowBits_length (word count : ℕ) : (lowBits word count).length = count := by
  simp [lowBits]

theorem lowBits_split (word n m : ℕ) :
    lowBits word (n + m) = lowBits word n ++ lowBits (word / 2 ^ n) m := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  by_cases hn : i < n
  · rw [List.getElem_append_left (by simpa using hn)]
    simp [lowBits]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [lowBits, List.getElem_ofFn, List.length_ofFn, Nat.testBit_div_two_pow]
    congr 1
    omega

theorem lowBits_mod (word n : ℕ) : lowBits (word % 2 ^ n) n = lowBits word n := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hin : i < n := by simpa using hi
  simp only [lowBits, List.getElem_ofFn, Nat.testBit_mod_two_pow]
  simp [hin]

def byteBits (out : List U8) : List Bool := out.flatMap fun b => lowBits b.val 8

@[simp] theorem byteBits_append (out tail : List U8) :
    byteBits (out ++ tail) = byteBits out ++ byteBits tail := by
  simp [byteBits]

@[simp] theorem byteBits_singleton (b : U8) : byteBits [b] = lowBits b.val 8 := by
  simp [byteBits]

@[simp] theorem byte_lowBits (word : ℕ) : lowBits (byte word).val 8 = lowBits word 8 := by
  change lowBits (word % 256) 8 = lowBits word 8
  exact lowBits_mod word 8

/-- Flushing changes byte boundaries, but preserves the exact bit sequence. -/
theorem flush_bits (out : List U8) (word count : ℕ) :
    byteBits (flush out word count).1 ++
      lowBits (flush out word count).2.1 (flush out word count).2.2 =
    byteBits out ++ lowBits word count := by
  induction count using Nat.strong_induction_on generalizing out word with
  | h count ih =>
      rw [flush]
      split
      · rfl
      · rw [ih (count - 8) (by omega) (out ++ [byte word]) (word / 256)]
        simp only [byteBits_append, byteBits_singleton, byte_lowBits, List.append_assoc]
        have hc : count = 8 + (count - 8) := by omega
        conv_rhs => rw [hc, lowBits_split]
        rfl

/-- Four bytes leaving at once: the same bits. -/
theorem bytes4_bits (word : ℕ) :
    byteBits [byte word, byte (word / 256), byte (word / 65536), byte (word / 16777216)] =
      lowBits word 32 := by
  have h1 : lowBits word 32 = lowBits word 8 ++ lowBits (word / 2 ^ 8) 24 := lowBits_split word 8 24
  have h2 : lowBits (word / 2 ^ 8) 24 = lowBits (word / 2 ^ 8) 8 ++ lowBits (word / 2 ^ 8 / 2 ^ 8) 16 :=
    lowBits_split (word / 2 ^ 8) 8 16
  have h3 : lowBits (word / 2 ^ 8 / 2 ^ 8) 16 =
      lowBits (word / 2 ^ 8 / 2 ^ 8) 8 ++ lowBits (word / 2 ^ 8 / 2 ^ 8 / 2 ^ 8) 8 :=
    lowBits_split (word / 2 ^ 8 / 2 ^ 8) 8 8
  rw [h1, h2, h3]
  simp [byteBits, Nat.div_div_eq_div_mul, List.append_assoc]

theorem flush4_bits (out : List U8) (word count : ℕ) :
    byteBits (flush4 out word count).1 ++
      lowBits (flush4 out word count).2.1 (flush4 out word count).2.2 =
    byteBits out ++ lowBits word count := by
  unfold flush4
  split
  · rfl
  · rename_i hc
    simp only [byteBits_append, bytes4_bits, List.append_assoc]
    have hc' : count = 32 + (count - 32) := by omega
    conv_rhs => rw [hc', lowBits_split]
    rfl

theorem lowBits_put (word count value width : ℕ) (hw : word < 2 ^ count)
    (hc : count + width ≤ 32) :
    lowBits (word ||| ((value * 2 ^ count) % 4294967296)) (count + width) =
      lowBits word count ++ lowBits value width := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hib : i < count + width := by simpa using hi
  have hi32 : i < 32 := by omega
  have ht : ((value * 2 ^ count) % 4294967296).testBit i =
      (decide (i ≥ count) && value.testBit (i - count)) := by
    change ((value * 2 ^ count) % 2 ^ 32).testBit i = _
    rw [Nat.testBit_mod_two_pow]
    simp only [hi32, decide_true, Bool.true_and]
    rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
  by_cases hin : i < count
  · rw [List.getElem_append_left (by simpa using hin)]
    simp only [lowBits, List.getElem_ofFn, Nat.testBit_or, ht]
    simp [show ¬ i ≥ count by omega]
  · rw [List.getElem_append_right (by simp; omega)]
    have hwbit : word.testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      exact _root_.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))
    simp only [lowBits, List.getElem_ofFn, List.length_ofFn, Nat.testBit_or, ht, hwbit]
    simp [show i ≥ count by omega]

theorem lowBits_put64 (word count value width : ℕ) (hw : word < 2 ^ count)
    (hc : count + width ≤ 64) :
    lowBits (word ||| ((value * 2 ^ count) % 18446744073709551616)) (count + width) =
      lowBits word count ++ lowBits value width := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hib : i < count + width := by simpa using hi
  have hi64 : i < 64 := by omega
  have ht : ((value * 2 ^ count) % 18446744073709551616).testBit i =
      (decide (i ≥ count) && value.testBit (i - count)) := by
    change ((value * 2 ^ count) % 2 ^ 64).testBit i = _
    rw [Nat.testBit_mod_two_pow]
    simp only [hi64, decide_true, Bool.true_and]
    rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
  by_cases hin : i < count
  · rw [List.getElem_append_left (by simpa using hin)]
    simp only [lowBits, List.getElem_ofFn, Nat.testBit_or, ht]
    simp [show ¬ i ≥ count by omega]
  · rw [List.getElem_append_right (by simp; omega)]
    have hwbit : word.testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      exact _root_.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))
    simp only [lowBits, List.getElem_ofFn, List.length_ofFn, Nat.testBit_or, ht, hwbit]
    simp [show i ≥ count by omega]

theorem put_bits (out : List U8) (word count value width : ℕ)
    (hw : word < 2 ^ count) (hc : count + width ≤ 64) :
    byteBits (put out word count value width).1 ++
      lowBits (put out word count value width).2.1 (put out word count value width).2.2 =
    (byteBits out ++ lowBits word count) ++ lowBits value width := by
  rw [put, flush4_bits, lowBits_put64 word count value width hw hc, List.append_assoc]

theorem put_word_bound (out : List U8) (word count value width : ℕ)
    (hw : word < 2 ^ count) (hv : value < 2 ^ width) :
    (put out word count value width).2.1 < 2 ^ (put out word count value width).2.2 := by
  unfold put
  apply flush4_word_bound
  apply Nat.or_lt_two_pow
  · exact _root_.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))
  · have hm : value * 2 ^ count < 2 ^ width * 2 ^ count :=
      Nat.mul_lt_mul_of_pos_right hv (by positivity)
    have hpow : 2 ^ width * 2 ^ count = 2 ^ (count + width) := by rw [← pow_add, Nat.add_comm]
    rw [hpow] at hm
    exact _root_.lt_of_le_of_lt (Nat.mod_le _ _) hm

theorem put_count (out : List U8) (word count value width : ℕ) (hc : count + width < 64) :
    (put out word count value width).2.2 < 32 ∧
    (put out word count value width).1.length ≤ out.length + 4 ∧
    8 * (put out word count value width).1.length + (put out word count value width).2.2 =
      8 * out.length + count + width := by
  unfold put
  have h := flush4_layout out (word ||| ((value * 2 ^ count) % 18446744073709551616)) (count + width) hc
  exact ⟨h.2.1, h.1, by omega⟩

theorem bits_stream (self : Gzip.solution.Writer) (value count : U32)
    (hs : self.count.val < 32) (hw : self.bits.val < 2 ^ self.count.val)
    (hc : count.val ≤ 32) (hv : value.val < 2 ^ count.val)
    (hb : self.out.val.length + (self.count.val + count.val) / 8 ≤ Usize.max) :
    Gzip.solution.Writer.impl.bits self value count ⦃ r =>
      byteBits r.out.val ++ lowBits r.bits.val r.count.val =
        (byteBits self.out.val ++ lowBits self.bits.val self.count.val) ++ lowBits value.val count.val ∧
      r.count.val < 32 ∧ r.bits.val < 2 ^ r.count.val ⦄ := by
  refine WP.spec_mono (bits self value count hs hc hb) ?_
  intro r hr
  have hout := congrArg (fun p : List U8 × ℕ × ℕ => p.1) hr
  have hword := congrArg (fun p : List U8 × ℕ × ℕ => p.2.1) hr
  have hcount := congrArg (fun p : List U8 × ℕ × ℕ => p.2.2) hr
  simp only at hout hword hcount
  refine ⟨?_, ?_, ?_⟩
  · rw [hout, hword, hcount]
    exact put_bits _ _ _ _ _ hw (by omega)
  · rw [hcount]
    exact (put_count _ _ _ _ _ (by omega)).1
  · rw [hword, hcount]
    exact put_word_bound _ _ _ _ _ hw hv

@[simp] theorem byteBits_cons (b : U8) (tail : List U8) :
    byteBits (b :: tail) = lowBits b.val 8 ++ byteBits tail := by
  simp [byteBits]

@[simp] theorem byteBits_length (s : List U8) : (byteBits s).length = 8 * s.length := by
  induction s with
  | nil => simp [byteBits]
  | cons b tail ih => simp only [byteBits_cons, List.length_append, lowBits_length, ih, List.length_cons]; omega

theorem joined_bound (first firstWidth second secondWidth : ℕ)
    (hf : first < 2 ^ firstWidth) (hs : second < 2 ^ secondWidth) :
    first ||| ((second * 2 ^ firstWidth) % 4294967296) < 2 ^ (firstWidth + secondWidth) := by
  apply Nat.or_lt_two_pow
  · exact _root_.lt_of_lt_of_le hf (Nat.pow_le_pow_right (by decide) (by omega))
  · apply _root_.lt_of_le_of_lt (Nat.mod_le _ _)
    have h := Nat.mul_lt_mul_of_pos_right hs (by positivity : 0 < 2 ^ firstWidth)
    rw [← pow_add, Nat.add_comm secondWidth firstWidth] at h
    exact h

theorem bits2_stream (self : Gzip.solution.Writer) (first firstCount second secondCount : U32)
    (hc : self.count.val < 32) (hw : self.bits.val < 2 ^ self.count.val)
    (hf : firstCount.val ≤ 16) (hs : secondCount.val ≤ 16)
    (hfv : first.val < 2 ^ firstCount.val) (hsv : second.val < 2 ^ secondCount.val)
    (hb : self.out.val.length + 8 ≤ Usize.max) :
    Gzip.solution.Writer.bits2 self first firstCount second secondCount ⦃ r =>
      byteBits r.out.val ++ lowBits r.bits.val r.count.val =
        (byteBits self.out.val ++ lowBits self.bits.val self.count.val) ++
          (lowBits first.val firstCount.val ++ lowBits second.val secondCount.val) ∧
      r.count.val < 32 ∧ r.bits.val < 2 ^ r.count.val ⦄ := by
  unfold Gzip.solution.Writer.bits2
  step as ⟨shift, hshift⟩
  step as ⟨joined, hjoined⟩
  step as ⟨count, hcount⟩
  have hjv : joined.val = first.val ||| ((second.val * 2 ^ firstCount.val) % 4294967296) := by
    rw [hjoined, UScalar.val_or, hshift]
    simp only [Nat.shiftLeft_eq, U32.size, U32.numBits_eq]
    rfl
  have hjb : joined.val < 2 ^ count.val := by
    rw [hjv, hcount]
    exact joined_bound _ _ _ _ hfv hsv
  have hbits := bits_stream self joined count hc hw (by scalar_tac) hjb (by scalar_tac)
  refine WP.spec_mono hbits ?_
  intro r ⟨hstream, hc', hw'⟩
  refine ⟨?_, hc', hw'⟩
  rw [hjv, hcount, lowBits_put _ _ _ _ hfv (by omega)] at hstream
  exact hstream
theorem byteBits_get (s : List U8) (i : ℕ) (hi : i < 8 * s.length) :
    (byteBits s)[i]! = (s[i / 8]!).val.testBit (i % 8) := by
  induction s generalizing i with
  | nil => simp at hi
  | cons b tail ih =>
      rw [byteBits_cons]
      by_cases h8 : i < 8
      · rw [List.getElem!_append_left _ _ i (by simp; omega)]
        have hlen : i < (lowBits b.val 8).length := by simp; omega
        rw [getElem!_pos (lowBits b.val 8) i hlen]
        simp only [lowBits, List.getElem_ofFn, Nat.div_eq_of_lt h8, Nat.mod_eq_of_lt h8,
          List.getElem!_cons_zero]
      · have hd : i / 8 = (i - 8) / 8 + 1 := by omega
        have hm : i % 8 = (i - 8) % 8 := by omega
        have hi' : i - 8 < 8 * tail.length := by simp only [List.length_cons] at hi; omega
        rw [List.getElem!_append_right _ _ i (by simp; omega)]
        simp only [lowBits_length]
        rw [ih _ hi', hd, hm]
        simp

def bitValue (b : Bool) : ℤ := if b then 1 else 0

theorem bitValue_zero (word : ℕ) : bitValue (word.testBit 0) = (word % 2 : ℕ) := by
  simp only [bitValue, Nat.testBit_eq_decide_div_mod_eq, pow_zero, Nat.div_one]
  split <;> rename_i h
  · have he : word % 2 = 1 := by simpa using h
    rw [he]
    rfl
  · have he : word % 2 ≠ 1 := by simpa using h
    have hb := Nat.mod_lt word (by decide : 0 < 2)
    omega

theorem bit_decode (s : List U8) (i : ℕ) (hi : i < 8 * s.length) :
    Gzip.Spec.bit_spec s i (bitValue (byteBits s)[i]!) := by
  refine ⟨trivial, ⟨by omega, by omega⟩, ?_⟩
  rw [byteBits_get s i hi]
  have hd : ((i : ℤ) / 8).toNat = i / 8 := by omega
  have hm : ((i : ℤ) % 8).toNat = i % 8 := by omega
  rw [hd, hm]
  have hcast : ((((s[i / 8]!).val : ℤ) / 2 ^ (i % 8)) % 2) =
      (((s[i / 8]!).val / 2 ^ (i % 8) % 2 : ℕ) : ℤ) := by
    norm_cast
  rw [hcast]
  simp only [bitValue, Nat.testBit_eq_decide_div_mod_eq]
  split <;> rename_i h
  · have he : (s[i / 8]!).val / 2 ^ (i % 8) % 2 = 1 := by simpa using h
    rw [he]
    rfl
  · have he : (s[i / 8]!).val / 2 ^ (i % 8) % 2 ≠ 1 := by simpa using h
    have hb := Nat.mod_lt ((s[i / 8]!).val / 2 ^ (i % 8)) (by decide : 0 < 2)
    omega

/-- Every LSB-first field described by the encoder is read back by the specification. -/
theorem field_of_bits (s : List U8) (i : ℤ) (word count : ℕ)
    (hw : word < 2 ^ count)
    (hbits : ∀ k < count, Gzip.Spec.bit_spec s (i + k) (bitValue (word.testBit k))) :
    Gzip.Spec.field_spec s i count word := by
  induction count generalizing i word with
  | zero =>
      have hz : word = 0 := by simp only [pow_zero] at hw; omega
      subst word
      rw [Gzip.Spec.field_spec]
      exact ⟨by simp [Gzip.Spec.field_pre], fun _ => ⟨fun _ => rfl, fun hn => False.elim (hn rfl)⟩⟩
  | succ count ih =>
      have hw' : word / 2 < 2 ^ count := by
        apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
        simpa only [pow_succ] using hw
      have ht : Gzip.Spec.field_spec s (i + 1) count (word / 2) := by
        apply ih _ _ hw'
        intro k hk
        have h := hbits (k + 1) (by omega)
        simpa only [Nat.testBit_div_two, Nat.cast_add, Nat.cast_one,
          add_assoc, add_left_comm, add_comm] using h
      have hb := hbits 0 (by omega)
      simp only [Nat.cast_zero, add_zero, bitValue_zero] at hb
      rw [Gzip.Spec.field_spec]
      refine ⟨by unfold Gzip.Spec.field_pre; omega, fun _ => ⟨fun hz => by omega, fun _ => ?_⟩⟩
      refine ⟨((word % 2 : ℕ) : ℤ), hb, fun _ => ⟨((word / 2 : ℕ) : ℤ), ?_, ?_⟩⟩
      · convert ht using 1 <;> push_cast <;> omega
      · omega

/-- Canonical Huffman codewords are the corresponding MSB-first bit sequence. -/
theorem code_of_bits (s : List U8) (i : ℤ) (word count : ℕ)
    (hw : word < 2 ^ count)
    (hbits : ∀ k < count, Gzip.Spec.bit_spec s (i + k)
      (bitValue (word.testBit (count - 1 - k)))) :
    Gzip.Spec.code_spec s i count word := by
  induction count generalizing i word with
  | zero =>
      have hz : word = 0 := by simp only [pow_zero] at hw; omega
      subst word
      rw [Gzip.Spec.code_spec]
      exact ⟨by simp [Gzip.Spec.code_pre], fun _ => ⟨fun _ => rfl, fun hn => False.elim (hn rfl)⟩⟩
  | succ count ih =>
      have hw' : word / 2 < 2 ^ count := by
        apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
        simpa only [pow_succ] using hw
      have ht : Gzip.Spec.code_spec s i count (word / 2) := by
        apply ih _ _ hw'
        intro k hk
        have h := hbits k (by omega)
        simpa only [Nat.testBit_div_two, show count + 1 - 1 - k = (count - 1 - k) + 1 by omega] using h
      have hb := hbits count (by omega)
      simp only [show count + 1 - 1 - count = 0 by omega, bitValue_zero] at hb
      rw [Gzip.Spec.code_spec]
      refine ⟨by unfold Gzip.Spec.code_pre; omega, fun _ => ⟨fun hz => by omega, fun _ => ?_⟩⟩
      refine ⟨((word / 2 : ℕ) : ℤ), ?_, ((word % 2 : ℕ) : ℤ), ?_, ?_⟩
      · convert ht using 1 <;> omega
      · convert hb using 1 <;> omega
      · omega

theorem bit_at_prefix (s : List U8) (front payload tail : List Bool)
    (hstream : byteBits s = front ++ payload ++ tail) (k : ℕ) (hk : k < payload.length) :
    Gzip.Spec.bit_spec s (front.length + k) (bitValue payload[k]!) := by
  have hslen := congrArg List.length hstream
  simp only [byteBits_length, List.length_append] at hslen
  have hi : front.length + k < 8 * s.length := by omega
  have hb := bit_decode s (front.length + k) hi
  rw [hstream, List.append_assoc,
    List.getElem!_append_right front (payload ++ tail) (front.length + k) (by omega)] at hb
  simp only [Nat.add_sub_cancel_left] at hb
  rw [List.getElem!_append_left payload tail k hk] at hb
  exact hb

theorem field_at_prefix (s : List U8) (front tail : List Bool) (word count : ℕ)
    (hstream : byteBits s = front ++ lowBits word count ++ tail) (hw : word < 2 ^ count) :
    Gzip.Spec.field_spec s front.length count word := by
  apply field_of_bits s front.length word count hw
  intro k hk
  have hb := bit_at_prefix s front (lowBits word count) tail hstream k (by simpa using hk)
  rw [getElem!_pos (lowBits word count) k (by simpa using hk)] at hb
  simpa only [lowBits, List.getElem_ofFn, Nat.cast_add] using hb

theorem reverse16_bits (word k : ℕ) (hk : k < 16) :
    (reverse16 word).testBit k = word.testBit (15 - k) := by
  interval_cases k <;>
    simp only [reverse16, reverseStage, show (4294967296 : ℕ) = 2 ^ 32 by decide,
      Nat.testBit_or, Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow,
      Nat.testBit_mod_two_pow] <;>
    norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]

theorem reverse16_partial (word count : ℕ) (hc : count ≤ 16) :
    lowBits (reverse16 word / 2 ^ (16 - count)) count = (lowBits word count).reverse := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hic : i < count := by simpa using hi
  rw [List.getElem_reverse hi']
  simp only [lowBits, List.getElem_ofFn, List.length_ofFn, Nat.testBit_div_two_pow]
  rw [reverse16_bits word (i + (16 - count)) (by omega)]
  congr 1
  omega

theorem reverse16_bound (word : ℕ) : reverse16 word < 2 ^ 16 := by
  let v := reverseStage (reverseStage (reverseStage word 21845 1) 13107 2) 3855 4
  change (((v &&& 255) * 256) % 4294967296) ||| ((v / 256) &&& 255) < 2 ^ 16
  apply Nat.or_lt_two_pow
  · have hb : v &&& 255 ≤ 255 := Nat.and_le_right
    have hm := Nat.mod_le ((v &&& 255) * 256) 4294967296
    norm_num only [pow_succ, pow_zero] at *
    omega
  · have hb : v / 256 &&& 255 ≤ 255 := Nat.and_le_right
    norm_num only [pow_succ, pow_zero] at *
    omega

theorem reverse16_partial_bound (word count : ℕ) (hc : count ≤ 16) :
    reverse16 word / 2 ^ (16 - count) < 2 ^ count := by
  apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
  rw [← pow_add, show count + (16 - count) = 16 by omega]
  exact reverse16_bound word

theorem code_stream (self : Gzip.solution.Writer) (value count : U32)
    (hs : self.count.val < 32) (hw : self.bits.val < 2 ^ self.count.val)
    (hc : count.val ≤ 16)
    (hb : self.out.val.length + (self.count.val + count.val) / 8 ≤ Usize.max) :
    Gzip.solution.Writer.code self value count ⦃ r =>
      byteBits r.out.val ++ lowBits r.bits.val r.count.val =
        (byteBits self.out.val ++ lowBits self.bits.val self.count.val) ++ (lowBits value.val count.val).reverse ∧
      r.count.val < 32 ∧ r.bits.val < 2 ^ r.count.val ⦄ := by
  refine WP.spec_mono (code self value count hs hc hb) ?_
  intro r hr
  have hout := congrArg (fun p : List U8 × ℕ × ℕ => p.1) hr
  have hword := congrArg (fun p : List U8 × ℕ × ℕ => p.2.1) hr
  have hcount := congrArg (fun p : List U8 × ℕ × ℕ => p.2.2) hr
  simp only at hout hword hcount
  refine ⟨?_, ?_, ?_⟩
  · rw [hout, hword, hcount, put_bits _ _ _ _ _ hw (by omega), reverse16_partial _ _ hc]
  · rw [hcount]
    exact (put_count _ _ _ _ _ (by omega)).1
  · rw [hword, hcount]
    exact put_word_bound _ _ _ _ _ hw (reverse16_partial_bound _ _ hc)

theorem code_at_prefix (s : List U8) (front tail : List Bool) (word count : ℕ)
    (hstream : byteBits s = front ++ (lowBits word count).reverse ++ tail)
    (hw : word < 2 ^ count) : Gzip.Spec.code_spec s front.length count word := by
  apply code_of_bits s front.length word count hw
  intro k hk
  have hlen : k < (lowBits word count).reverse.length := by simpa using hk
  have hb := bit_at_prefix s front (lowBits word count).reverse tail hstream k hlen
  rw [getElem!_pos (lowBits word count).reverse k hlen, List.getElem_reverse hlen] at hb
  simpa only [lowBits, List.getElem_ofFn, List.length_ofFn, Nat.cast_add] using hb

end Gzip.Proofs.Writer
