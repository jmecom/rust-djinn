import Aeneas
import Gzip.Code.Funs

open Aeneas Std Result

namespace Gzip.Proofs.Writer

def byte (n : ℕ) : U8 := UScalar.ofNatCore (n % 256) (by exact Nat.mod_lt _ (by decide))

/-- Reference byte emission one byte at a time (the alignment loop), leaving the residual
partial byte. -/
def flush (out : List U8) (word count : ℕ) : List U8 × ℕ × ℕ :=
  if count < 8 then (out, word, count)
  else flush (out ++ [byte word]) (word / 256) (count - 8)
termination_by count
decreasing_by omega

theorem flush_layout (out : List U8) (word count : ℕ) :
    (flush out word count).1.length = out.length + count / 8 ∧
    (flush out word count).2.2 = count % 8 := by
  induction count using Nat.strong_induction_on generalizing out word with
  | h count ih =>
      rw [flush]
      split
      · rename_i hc
        simp [Nat.div_eq_of_lt hc, Nat.mod_eq_of_lt hc]
      · rename_i hc
        obtain ⟨hlen, hcount⟩ := ih (count - 8) (by omega) (out ++ [byte word]) (word / 256)
        simp only [List.length_append, List.length_singleton] at hlen
        exact ⟨by omega, by omega⟩

theorem flush_prefix (out : List U8) (word count : ℕ) :
    out <+: (flush out word count).1 := by
  induction count using Nat.strong_induction_on generalizing out word with
  | h count ih =>
      rw [flush]
      split
      · exact List.prefix_refl _
      · exact (List.prefix_append _ _).trans
          (ih (count - 8) (by omega) (out ++ [byte word]) (word / 256))

theorem flush_word_bound (out : List U8) (word count : ℕ) (hw : word < 2 ^ count) :
    (flush out word count).2.1 < 2 ^ (flush out word count).2.2 := by
  induction count using Nat.strong_induction_on generalizing out word with
  | h count ih =>
      rw [flush]
      split
      · exact hw
      · have hp : 2 ^ count = 2 ^ (count - 8) * 256 := by
          conv_lhs => rw [show count = (count - 8) + 8 by omega]
          rw [pow_add]
          rfl
        have hw' : word / 256 < 2 ^ (count - 8) := by
          apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
          rw [← hp]
          exact hw
        exact ih (count - 8) (by omega) (out ++ [byte word]) (word / 256) hw'

/-- A byte cast of a word is its low byte. -/
theorem cast_byte (x : U64) : UScalar.cast .U8 x = byte x.val := by
  apply (UScalar.eq_equiv _ _).mpr
  rw [UScalar.cast_val_eq]
  simp [byte]

/-- The alignment loop: whole bytes leave the accumulator one at a time. -/
theorem flush_body (self : Gzip.solution.Writer)
    (hb : self.out.val.length + self.count.val / 8 ≤ Usize.max) :
    Gzip.solution.Writer.align_loop.body self ⦃ r =>
      match r with
      | .done (out', word', count') =>
          (out'.val, word'.val, count'.val) = flush self.out.val self.bits.val self.count.val
      | .cont self' =>
          flush self'.out.val self'.bits.val self'.count.val =
            flush self.out.val self.bits.val self.count.val ∧
          self'.out.val.length + self'.count.val / 8 ≤ Usize.max ∧
          self'.count.val < self.count.val ⦄ := by
  unfold Gzip.solution.Writer.align_loop.body
  step*
  · have hbyte : i = byte self.bits.val := by rw [i_post]; exact cast_byte _
    have hshift : i1.val = self.bits.val / 256 := by
      simpa only [Nat.shiftRight_eq_div_pow] using i1_post
    try dsimp only
    refine ⟨?_, ?_, by omega⟩
    · conv_rhs => rw [flush]
      simp only [show ¬ self.count.val < 8 by omega, if_false]
      rw [v_post, hbyte, hshift, i2_post]
    · rw [v_post, List.length_append, List.length_singleton, i2_post]
      omega
  · have hc : self.count.val < 8 := by scalar_tac
    try dsimp only
    rw [flush]
    simp only [hc, if_true]

@[step]
theorem flush_loop (self : Gzip.solution.Writer)
    (hb : self.out.val.length + self.count.val / 8 ≤ Usize.max) :
    Gzip.solution.Writer.align_loop self ⦃ r =>
      (r.1.val, r.2.1.val, r.2.2.val) = flush self.out.val self.bits.val self.count.val ⦄ := by
  unfold Gzip.solution.Writer.align_loop
  apply loop.spec_decr_nat (fun w => w.count.val)
    (fun w => w.out.val.length + w.count.val / 8 ≤ Usize.max ∧
      flush w.out.val w.bits.val w.count.val = flush self.out.val self.bits.val self.count.val)
  · intro w ⟨hbudget, hstate⟩
    refine WP.spec_mono (flush_body w hbudget) ?_
    intro r hr
    cases r with
    | done state => exact hr.trans hstate
    | cont w' =>
        obtain ⟨hflush, hbudget', hdecr⟩ := hr
        exact ⟨⟨hbudget', hflush.trans hstate⟩, hdecr⟩
  · exact ⟨hb, rfl⟩

/-- Four whole bytes leave the accumulator at once when it holds at least 32 bits. -/
def flush4 (out : List U8) (word count : ℕ) : List U8 × ℕ × ℕ :=
  if count < 32 then (out, word, count)
  else (out ++ [byte word, byte (word / 256), byte (word / 65536), byte (word / 16777216)],
    word / 4294967296, count - 32)

theorem flush4_layout (out : List U8) (word count : ℕ) (hc : count < 64) :
    (flush4 out word count).1.length ≤ out.length + 4 ∧
    (flush4 out word count).2.2 < 32 ∧
    8 * (flush4 out word count).1.length + (flush4 out word count).2.2 = 8 * out.length + count := by
  unfold flush4
  split
  · simp
    omega
  · simp
    omega

theorem flush4_prefix (out : List U8) (word count : ℕ) :
    out <+: (flush4 out word count).1 := by
  unfold flush4
  split
  · exact List.prefix_refl _
  · exact List.prefix_append _ _

theorem flush4_word_bound (out : List U8) (word count : ℕ) (hw : word < 2 ^ count) :
    (flush4 out word count).2.1 < 2 ^ (flush4 out word count).2.2 := by
  unfold flush4
  split
  · exact hw
  · rename_i hc
    simp only
    have hp : 2 ^ count = 2 ^ (count - 32) * 4294967296 := by
      conv_lhs => rw [show count = (count - 32) + 32 by omega]
      rw [pow_add]
      rfl
    apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
    rw [← hp]
    exact hw

/-- The exact arithmetic encoder used by the Rust buffered writer. -/
def put (out : List U8) (word count value width : ℕ) : List U8 × ℕ × ℕ :=
  flush4 out (word ||| ((value * 2 ^ count) % 18446744073709551616)) (count + width)

theorem cast_u64_u32 (x : U32) : (UScalar.cast .U64 x).val = x.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  simp [UScalarTy.numBits]

@[step]
theorem bits (self : Gzip.solution.Writer) (value count : U32)
    (hs : self.count.val < 32) (hc : count.val ≤ 32)
    (hb : self.out.val.length + (self.count.val + count.val) / 8 ≤ Usize.max) :
    Gzip.solution.Writer.impl.bits self value count ⦃ r =>
      (r.out.val, r.bits.val, r.count.val) =
        put self.out.val self.bits.val self.count.val value.val count.val ⦄ := by
  unfold Gzip.solution.Writer.impl.bits
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨b, hbp⟩
  step as ⟨i2, hi2⟩
  have hiv : i.val = value.val := by rw [hi]; exact cast_u64_u32 value
  have hbv : b.val = self.bits.val ||| ((value.val * 2 ^ self.count.val) % 18446744073709551616) := by
    rw [hbp, UScalar.val_or, hi1, hiv]
    simp only [Nat.shiftLeft_eq, U64.size, U64.numBits_eq]
    rfl
  split
  · -- at least 32 bits: four bytes leave
    rename_i h32
    have h32' : 32 ≤ i2.val := by scalar_tac
    have hout4 : self.out.val.length + 4 ≤ Usize.max := by
      have hq : 4 ≤ (self.count.val + count.val) / 8 := by omega
      omega
    step as ⟨i3, hi3⟩
    have h3 : i3 = byte b.val := by rw [hi3]; exact cast_byte _
    step as ⟨v, hv⟩
    have hvl : v.val.length = self.out.val.length + 1 := by rw [hv]; simp
    step as ⟨i4, hi4⟩
    have h4 : i4.val = b.val / 256 := by simpa only [Nat.shiftRight_eq_div_pow] using hi4
    step as ⟨i5, hi5⟩
    have h5 : i5 = byte (b.val / 256) := by rw [hi5, cast_byte, h4]
    step as ⟨v1, hv1⟩
    have hv1l : v1.val.length = self.out.val.length + 2 := by rw [hv1]; simp [hvl]
    step as ⟨i6, hi6⟩
    have h6 : i6.val = b.val / 65536 := by simpa only [Nat.shiftRight_eq_div_pow] using hi6
    step as ⟨i7, hi7⟩
    have h7 : i7 = byte (b.val / 65536) := by rw [hi7, cast_byte, h6]
    step as ⟨v2, hv2⟩
    have hv2l : v2.val.length = self.out.val.length + 3 := by rw [hv2]; simp [hv1l]
    step as ⟨i8, hi8⟩
    have h8 : i8.val = b.val / 16777216 := by simpa only [Nat.shiftRight_eq_div_pow] using hi8
    step as ⟨i9, hi9⟩
    have h9 : i9 = byte (b.val / 16777216) := by rw [hi9, cast_byte, h8]
    step as ⟨v3, hv3⟩
    step as ⟨i10, hi10⟩
    have h10 : i10.val = b.val / 4294967296 := by simpa only [Nat.shiftRight_eq_div_pow] using hi10
    step as ⟨i11, hi11⟩
    have hge : ¬ self.count.val + count.val < 32 := by omega
    have hput : put self.out.val self.bits.val self.count.val value.val count.val =
        (self.out.val ++ [byte b.val, byte (b.val / 256), byte (b.val / 65536), byte (b.val / 16777216)],
          b.val / 4294967296, self.count.val + count.val - 32) := by
      unfold put flush4
      rw [if_neg hge, hbv]
    try simp only [WP.spec_ok]
    rw [hput, hv3, hv2, hv1, hv, h3, h5, h7, h9, h10, hi11, hi2]
    simp
  · -- fewer than 32 bits: nothing leaves
    rename_i h32
    have hlt : self.count.val + count.val < 32 := by scalar_tac
    have hput : put self.out.val self.bits.val self.count.val value.val count.val =
        (self.out.val, b.val, self.count.val + count.val) := by
      unfold put flush4
      rw [if_pos hlt, hbv]
    step*
    try rw [hput, hi2]

def pad (out : List U8) (word count : ℕ) : List U8 × ℕ × ℕ :=
  if count = 0 then (out, word, count) else (out ++ [byte word], 0, 0)

/-- Alignment: the whole bytes leave, then the partial byte padded with zeros. -/
def aligned (out : List U8) (word count : ℕ) : List U8 × ℕ × ℕ :=
  pad (flush out word count).1 (flush out word count).2.1 (flush out word count).2.2

@[step]
theorem align (self : Gzip.solution.Writer) (hs : self.count.val < 32)
    (hb : self.out.val.length + 4 ≤ Usize.max) :
    Gzip.solution.Writer.align self ⦃ r =>
      (r.out.val, r.bits.val, r.count.val) = aligned self.out.val self.bits.val self.count.val ⦄ := by
  unfold Gzip.solution.Writer.align
  have hl := flush_loop self (by omega)
  step as ⟨v, i, i1, hpost⟩
  have ho := congrArg (fun p : List U8 × ℕ × ℕ => p.1) hpost
  have hw := congrArg (fun p : List U8 × ℕ × ℕ => p.2.1) hpost
  have hn := congrArg (fun p : List U8 × ℕ × ℕ => p.2.2) hpost
  simp only at ho hw hn
  have hlen := (flush_layout self.out.val self.bits.val self.count.val).1
  have hvlen : v.val.length ≤ self.out.val.length + 3 := by rw [ho, hlen]; omega
  step*
  · have hc : i1.val ≠ 0 := by scalar_tac
    have hbyte : i2 = byte i.val := by rw [i2_post]; exact cast_byte _
    simp only [aligned]
    rw [← ho, ← hw, ← hn]
    simp [pad, hc, v1_post, hbyte]
  · have hc : i1.val = 0 := by scalar_tac
    simp only [aligned]
    rw [← ho, ← hw, ← hn]
    simp [pad, hc]

def reverseStage (value mask shift : ℕ) : ℕ :=
  (((value &&& mask) * 2 ^ shift) % 4294967296) ||| ((value / 2 ^ shift) &&& mask)

def reverse16 (value : ℕ) : ℕ :=
  reverseStage (reverseStage (reverseStage (reverseStage value 21845 1) 13107 2) 3855 4) 255 8

@[step]
theorem code (self : Gzip.solution.Writer) (value count : U32)
    (hs : self.count.val < 32) (hc : count.val ≤ 16)
    (hb : self.out.val.length + (self.count.val + count.val) / 8 ≤ Usize.max) :
    Gzip.solution.Writer.code self value count ⦃ r =>
      (r.out.val, r.bits.val, r.count.val) =
        put self.out.val self.bits.val self.count.val
          (reverse16 value.val / 2 ^ (16 - count.val)) count.val ⦄ := by
  unfold Gzip.solution.Writer.code
  step*
  simp only [r_post, i_post, i1_post, i2_post, i3_post, v_post,
    i4_post, i5_post, i6_post, i7_post, v1_post, i8_post, i9_post,
    i10_post, i11_post, v2_post, i12_post, i13_post, i14_post, i15_post,
    v3_post, i16_post, i17_post, UScalar.val_and, UScalar.val_or,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, U32.size, U32.numBits_eq,
    reverse16, reverseStage]
  rfl

end Gzip.Proofs.Writer
