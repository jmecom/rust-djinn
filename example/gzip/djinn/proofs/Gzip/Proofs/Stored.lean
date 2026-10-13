import Gzip.Proofs.Runtime

open Aeneas Std Result
open Gzip.solution Gzip.Spec Gzip.Proofs.Writer Gzip.Proofs.Runtime

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

namespace Gzip.Proofs.Runtime

theorem get_prefix {α : Type} [Inhabited α] (s out : List α) (hp : out <+: s)
    (k : ℕ) (hk : k < out.length) : s[k]! = out[k]! := by
  rw [getElem!_pos out k hk, getElem!_pos s k (Nat.lt_of_lt_of_le hk hp.length_le)]
  exact (hp.getElem hk).symm

theorem u16_prefix (s front tail : List U8) (v : ℕ) (hv : v < 65536)
    (hp : front ++ le16 v ++ tail <+: s) : u16le_spec s front.length v := by
  have hlen := hp.length_le
  simp only [List.length_append, le16, List.length_cons, List.length_nil] at hlen
  have hget0 := get_prefix s _ hp front.length (by simp [le16])
  have hget1 := get_prefix s _ hp (front.length + 1) (by simp [le16])
  rw [List.append_assoc, List.getElem!_append_right _ _ _ (by omega)] at hget0 hget1
  simp only [le16, List.cons_append, List.nil_append, List.getElem!_cons_zero,
    List.getElem!_cons_succ, Nat.add_sub_cancel_left, Nat.sub_self] at hget0 hget1
  refine ⟨trivial, ⟨by omega, by omega⟩, ?_⟩
  simp only [Int.toNat_natCast, show ((front.length : ℤ) + 1).toNat = front.length + 1 by omega]
  rw [hget0, hget1]
  simp only [byte, UScalar.ofNatCore_val_eq]
  have hdiv : v / 256 < 256 := by omega
  rw [Nat.mod_eq_of_lt hdiv]
  omega

def Fragment (data : List U8) (p q : ℕ) (front bits : List Bool) (final : Bool) : Prop :=
  ∀ s tail, byteBits s = front ++ bits ++ tail →
    bit_spec s front.length (if final then 1 else 0) ∧
    block_spec s (front.length + 1) (data.take p) (data.take q) (front.length + bits.length)

theorem header_bits (s : List U8) (front tail : List Bool) (final : Bool) (ty : ℕ)
    (ht : ty < 3)
    (hs : byteBits s = front ++ lowBits ((if final then 1 else 0) + 2 * ty) 3 ++ tail) :
    bit_spec s front.length (if final then 1 else 0) ∧
    field_spec s (front.length + 1) 2 ty := by
  have hb := bit_at_prefix s front (lowBits ((if final then 1 else 0) + 2 * ty) 3) tail hs 0 (by simp)
  have hf := field_at_prefix s (front ++ lowBits ((if final then 1 else 0) + 2 * ty) 1) tail ty 2
    (by
      rw [show 3 = 1 + 2 from rfl, lowBits_split] at hs
      have hdiv : ((if final then 1 else 0) + 2 * ty) / 2 ^ 1 = ty := by split <;> omega
      simpa only [hdiv, List.append_assoc] using hs) (by omega)
  simp only [List.length_append, lowBits_length, Nat.cast_add, Nat.cast_one] at hf
  refine ⟨?_, hf⟩
  try simp only [Nat.add_zero] at hb
  cases final <;> interval_cases ty <;> simpa [lowBits, bitValue] using hb

theorem field_unique (s : List U8) (i : ℤ) (n : ℕ) (a b : ℤ)
    (ha : field_spec s i n a) (hb : field_spec s i n b) : a = b := by
  induction n generalizing i a b with
  | zero =>
    rw [field_spec] at ha hb
    exact (ha.2 (by omega)).1 rfl |>.trans ((hb.2 (by omega)).1 rfl).symm
  | succ n ih =>
    rw [field_spec] at ha hb
    obtain ⟨x, hx, ha⟩ := (ha.2 (by omega)).2 (by omega)
    obtain ⟨y, hy, hb⟩ := (hb.2 (by omega)).2 (by omega)
    obtain ⟨a', ha', heqa⟩ := ha hx
    obtain ⟨b', hb', heqb⟩ := hb hy
    have hxy := Encoder.bit_unique hx hy
    have hab := ih (i + 1) a' b' (by simpa using ha') (by simpa using hb')
    omega

theorem stored_decode (data s aligned : List U8) (p q : ℕ) (i : ℤ)
    (hs : p ≤ q) (hq : q ≤ data.length) (hn : q - p < 65536)
    (ha : (i + 7) / 8 = aligned.length)
    (hp : aligned ++ le16 (q - p) ++ le16 (65535 - (q - p)) ++
      (data.drop p).take (q - p) <+: s) :
    stored_spec s i (data.take p) (data.take q) (8 * (aligned.length + 4 + (q - p))) := by
  have hn' : 65535 - (q - p) < 65536 := by omega
  have hlen := hp.length_le
  have hchunk : ((data.drop p).take (q - p)).length = q - p := by
    rw [List.length_take_of_le (by simp; omega)]
  simp only [List.length_append, le16, List.length_cons, List.length_nil, hchunk] at hlen
  have h16 := u16_prefix s aligned (le16 (65535 - (q - p)) ++ (data.drop p).take (q - p))
    (q - p) hn (by simpa only [List.append_assoc] using hp)
  have h16' := u16_prefix s (aligned ++ le16 (q - p)) ((data.drop p).take (q - p))
    (65535 - (q - p)) hn' hp
  have hplen : (data.take p).length = p := List.length_take_of_le (by omega)
  have hqlen : (data.take q).length = q := List.length_take_of_le hq
  refine ⟨trivial, aligned.length, (q - p : ℕ), ha.symm, h16, ?_, by omega,
    by rw [hplen, hqlen]; omega, ?_, ?_, ?_⟩
  · simp only [List.length_append, le16, List.length_cons, List.length_nil] at h16'
    convert h16' using 1 <;> omega
  · simp only [List.drop_zero, Int.toNat_natCast, hplen, List.take_take, Nat.min_eq_left hs]
  · simp only [hplen, hqlen, Int.toNat_natCast,
      show ((q : ℤ) - p).toNat = q - p by omega,
      show ((aligned.length : ℤ) + 4).toNat = aligned.length + 4 by omega,
      show (((aligned.length : ℤ) + 4 + (q - p : ℕ)) - (aligned.length + 4)).toNat = q - p by omega]
    rw [List.drop_take]
    obtain ⟨rest, he⟩ := hp
    rw [← he]
    have hfront : (aligned ++ le16 (q - p) ++ le16 (65535 - (q - p))).length = aligned.length + 4 := by
      simp [le16]
    rw [← hfront, List.append_assoc _ ((data.drop p).take (q - p)) rest, List.drop_left]
    rw [List.take_append_of_le_length (by rw [hchunk])]
  · push_cast
    omega

@[step] theorem extend_bytes (v : alloc.vec.Vec U8) (s : Aeneas.Std.Slice U8)
    (hspace : v.val.length + s.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r =>
      r.val = v.val ++ s.val ⦄ := by
  have hclone : Slice.clone core.clone.CloneU8.clone s = ok s := by
    have hc := Slice.clone_spec (clone := core.clone.CloneU8.clone) (s := s)
      (by intro x hx; rfl)
    rw [WP.spec_equiv_exists] at hc
    obtain ⟨s', he, hsame⟩ := hc
    simpa only [← hsame] using he
  unfold alloc.vec.Vec.extend_from_slice
  simp only [alloc.vec.Vec.length, Slice.length] at *
  rw [dif_pos hspace]
  split
  · rename_i s' he
    have hs : s' = s := by
      rw [hclone] at he
      cases he
      rfl
    subst s'
    step*
  · rename_i eff k he
    rw [hclone] at he
    cases he
  · rename_i he
    rw [hclone] at he
    cases he

theorem stored_correct (data : Aeneas.Std.Slice U8) (start stop : Usize)
    (w : Gzip.solution.Writer) (final : Bool)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length)
    (hn : stop.val - start.val ≤ 32768) (hb : Buffered w)
    (hbudget : (stream w).length + 8 * (stop.val - start.val) + 96 ≤ 34359738360) :
    stored w data start stop final ⦃ r =>
      Buffered r ∧ ∃ bits, stream r = stream w ++ bits ∧
        bits.length ≤ 8 * (stop.val - start.val) + 42 ∧ 3 ≤ bits.length ∧
        Fragment data.val start.val stop.val (stream w) bits final ⦄ := by
  have hc := hb.1
  have hw := hb.2
  have hheaderSpec : (if final then ok 1#u32 else ok 0#u32) ⦃ h =>
      h.val = if final then 1 else 0 ⦄ := by
    split <;> step*
  unfold stored
  step as ⟨header, hheader⟩
  have hh : header.val = if final then 1 else 0 := by
    exact hheader
  have hhbound : header.val < 2 ^ (3#u32).val := by rw [hh]; split <;> scalar_tac
  have hspace : w.out.val.length + 12 ≤ Usize.max := space w 12 (by omega)
  have hbits := bits_stream w header 3#u32 hc hw (by scalar_tac) hhbound (by scalar_tac)
  step as ⟨w1, hemit, hc1, hw1⟩
  have hsz1 := congrArg List.length hemit
  simp only [List.length_append, byteBits_length, lowBits_length] at hsz1
  have halign := align_stream w1 ⟨hc1, hw1⟩ (by omega)
  step as ⟨w2, hc2, hw2, padding, hpad, hpadlen, hpadsize⟩
  have hw2len : w2.out.val.length ≤ w1.out.val.length + 4 := by
    simp only [stream_length] at hpadsize
    omega
  have haligned : byteBits w2.out.val = stream w ++ lowBits header.val 3 ++ padding := by
    simpa only [stream, hemit, UScalar.ofNatCore_val_eq] using hpad
  have hsz2 := congrArg List.length haligned
  simp only [List.length_append, byteBits_length, lowBits_length] at hsz2
  step as ⟨n, hnval, _⟩
  step as ⟨len, hlen⟩
  have hlenval : len.val = stop.val - start.val := by scalar_tac
  have h3 := bits16a w2 len hc2 hw2 (by omega) (by omega)
  step as ⟨w3, hout3, hc3, hw3⟩
  step as ⟨comp, hcomp⟩
  have hcompval : comp.val = 65535 - (stop.val - start.val) := by omega
  have h4 := bits16b w3 comp hc3 (by rw [hw3]; omega) (by omega) (by rw [hout3]; omega)
  step as ⟨w4, hout4, hc4, hw4⟩
  have hsz4 : w4.out.val.length = w2.out.val.length + 4 := by simp [hout4, hout3, le16]
  have hsub := core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    ({ start, «end» := stop } : core.ops.range.Range Usize) data
    (by simp; scalar_tac) (by simp; scalar_tac)
  step as ⟨s, hsval, hslen⟩
  step as ⟨v, hv⟩
  let r : Gzip.solution.Writer := { w4 with out := v }
  change Buffered r ∧ ∃ bits, stream r = stream w ++ bits ∧
    bits.length ≤ 8 * (stop.val - start.val) + 42 ∧ 3 ≤ bits.length ∧
    Fragment data.val start.val stop.val (stream w) bits final
  have hout : r.out.val = w4.out.val ++ (data.val.drop start.val).take (stop.val - start.val) := by
    simp only [r]
    rw [hv, hsval]
    rfl
  have hrCount : r.count = w4.count := rfl
  have hrWord : r.bits = w4.bits := rfl
  have hout' : r.out.val = w2.out.val ++ le16 (stop.val - start.val) ++
      le16 (65535 - (stop.val - start.val)) ++
      (data.val.drop start.val).take (stop.val - start.val) := by
    rw [hout, hout4, hout3, hw3, hlenval, hcompval]
  have hc0 : r.count.val = 0 := by rw [hrCount]; exact hc4
  have hw0 : r.bits.val = 0 := by rw [hrWord]; exact hw4
  let bits := lowBits header.val 3 ++ padding ++
    byteBits (le16 (stop.val - start.val) ++ le16 (65535 - (stop.val - start.val)) ++
      (data.val.drop start.val).take (stop.val - start.val))
  have hstream : stream r = stream w ++ bits := by
    simp only [stream, hc0, lowBits, List.ofFn_zero, List.append_nil, hout',
      byteBits_append, haligned, bits, List.append_assoc]
  have hbitslen : bits.length = 3 + padding.length + 32 + 8 * (stop.val - start.val) := by
    simp [bits, le16, List.length_take_of_le (show stop.val - start.val ≤ (data.val.drop start.val).length by simp; omega)]
    omega
  refine ⟨⟨by omega, by simp [hc0, hw0]⟩, bits, hstream, by omega, by omega, ?_⟩
  intro s tail hss
  have hhead := header_bits s (stream w)
    (padding ++ byteBits (le16 (stop.val - start.val) ++ le16 (65535 - (stop.val - start.val)) ++
      (data.val.drop start.val).take (stop.val - start.val)) ++ tail) final 0 (by omega)
    (by simpa only [bits, hh, Nat.mul_zero, Nat.add_zero, List.append_assoc] using hss)
  have hbyte : byteBits s = byteBits r.out.val ++ tail := by
    rw [← hstream] at hss
    simpa only [stream, hc0, lowBits, List.ofFn_zero, List.append_nil] using hss
  have hpref : r.out.val <+: s := by
    rw [← bytes_prefix s _ tail hbyte]
    exact List.take_prefix _ _
  have hst := stored_decode data.val s w2.out.val start.val stop.val ((stream w).length + 3)
    hs hd (by omega) (by omega) (by rw [← hout']; exact hpref)
  have hszr : 8 * r.out.val.length = (stream w).length + bits.length := by
    have he := congrArg List.length hstream
    simp only [stream_length, hc0, Nat.add_zero, List.length_append] at he
    simpa only [stream_length] using he
  have hchunk : ((data.val.drop start.val).take (stop.val - start.val)).length = stop.val - start.val :=
    List.length_take_of_le (by simp; omega)
  have houtlen := congrArg List.length hout'
  simp only [List.length_append, le16, List.length_cons, List.length_nil, hchunk] at houtlen
  refine ⟨hhead.1, trivial, fun _ => ?_, fun hnzero => False.elim (hnzero hhead.2)⟩
  convert hst using 1 <;> omega

end Gzip.Proofs.Runtime
