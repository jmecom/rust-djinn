import Aeneas
import Gzip.Code.Funs
import Gzip.Spec
import Gzip.Proofs.CrcImpl
import Gzip.Proofs.WordPrefix
import Gzip.Proofs.DeBruijn
import Gzip.Proofs.PrefixModel

open Aeneas Std Result
open Gzip.solution

namespace Gzip.Proofs.Matches

def EqualRun (data : List U8) (p q n : ℕ) : Prop :=
  ∀ k < n, data[p + k]! = data[q + k]!

/-- Equality of four packed bytes implies equality of each byte. -/
theorem word_bytes (a0 a1 a2 a3 b0 b1 b2 b3 : U8)
    (h : a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216 =
      b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  have ha0 := a0.hBounds
  have ha1 := a1.hBounds
  have ha2 := a2.hBounds
  have ha3 := a3.hBounds
  have hb0 := b0.hBounds
  have hb1 := b1.hBounds
  have hb2 := b2.hBounds
  have hb3 := b3.hBounds
  norm_num [U8.numBits_eq] at ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
  refine ⟨(UScalar.eq_equiv _ _).mpr ?_, (UScalar.eq_equiv _ _).mpr ?_,
    (UScalar.eq_equiv _ _).mpr ?_, (UScalar.eq_equiv _ _).mpr ?_⟩ <;> omega

theorem word_run {data : List U8} {p q n : ℕ}
    (he : EqualRun data p q n)
    (hw : (data[p + n]!).val + (data[p + n + 1]!).val * 256 +
        (data[p + n + 2]!).val * 65536 + (data[p + n + 3]!).val * 16777216 =
      (data[q + n]!).val + (data[q + n + 1]!).val * 256 +
        (data[q + n + 2]!).val * 65536 + (data[q + n + 3]!).val * 16777216) :
    EqualRun data p q (n + 4) := by
  obtain ⟨h0, h1, h2, h3⟩ := word_bytes _ _ _ _ _ _ _ _ hw
  intro k hk
  by_cases hkn : k < n
  · exact he k hkn
  · have hc : k = n ∨ k = n + 1 ∨ k = n + 2 ∨ k = n + 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · exact h0
    · simpa only [Nat.add_assoc] using h1
    · simpa only [Nat.add_assoc] using h2
    · simpa only [Nat.add_assoc] using h3

/-- A failed word comparison still verifies its low-byte prefix without another load. -/
theorem prefix_run {data : List U8} {p q n a b : ℕ}
    (he : EqualRun data p q n)
    (ha : a = (data[p + n]!).val + (data[p + n + 1]!).val * 256 +
      (data[p + n + 2]!).val * 65536 + (data[p + n + 3]!).val * 16777216)
    (hb : b = (data[q + n]!).val + (data[q + n + 1]!).val * 256 +
      (data[q + n + 2]!).val * 65536 + (data[q + n + 3]!).val * 16777216) :
    EqualRun data p q (n + WordPrefix.prefixValue a b) := by
  have hbound := WordPrefix.prefixValue_le a b
  have hbytes := WordPrefix.prefix_bytes data[p + n]! data[p + n + 1]!
    data[p + n + 2]! data[p + n + 3]! data[q + n]! data[q + n + 1]!
    data[q + n + 2]! data[q + n + 3]!
  dsimp only at hbytes
  rw [← ha, ← hb] at hbytes
  intro k hk
  by_cases hkn : k < n
  · exact he k hkn
  · have hc : k = n ∨ k = n + 1 ∨ k = n + 2 := by omega
    rcases hc with rfl | rfl | rfl
    · exact hbytes.1 (by omega)
    · simpa only [Nat.add_assoc] using hbytes.2.1 (by omega)
    · simpa only [Nat.add_assoc] using hbytes.2.2 (by omega)

theorem mask_eq_mod (a b mask : U32) (n : ℕ) (hm : mask.val = 2 ^ n - 1) :
    (a &&& mask = b &&& mask) ↔ a.val % 2 ^ n = b.val % 2 ^ n := by
  rw [UScalar.eq_equiv, UScalar.val_and, UScalar.val_and, hm,
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]

theorem mask_mod_val (a mask : U32) (n : ℕ) (hm : mask.val = 2 ^ n - 1) :
    (a &&& mask).val = a.val % 2 ^ n := by
  rw [UScalar.val_and, hm]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem prefix_indicator (a b : U32) (x y : ℕ) (he : (a = b) ↔ x = y) :
    (if a = b then ok 1#usize else ok 0#usize) ⦃ n =>
      n.val = (if x = y then 1 else 0) ∧ n.val ≤ 1 ⦄ := by
  split <;> simp_all [WP.spec_ok]

@[step]
theorem prefix3_spec (a b : U32) :
    prefix3 a b ⦃ n => n.val = WordPrefix.prefixValue a.val b.val ∧ n.val ≤ 3 ⦄ := by
  unfold prefix3
  step as ⟨a8, ha8, _⟩
  step as ⟨b8, hb8, _⟩
  have ha8v : a8.val = a.val % 256 := by
    rw [ha8]
    exact Nat.and_two_pow_sub_one_eq_mod _ 8
  have hb8v : b8.val = b.val % 256 := by
    rw [hb8]
    exact Nat.and_two_pow_sub_one_eq_mod _ 8
  have hfirst := prefix_indicator a8 b8 (a.val % 256) (b.val % 256)
    (by rw [UScalar.eq_equiv, ha8v, hb8v])
  step as ⟨first, hfirstv, hfirstb⟩
  step as ⟨a16, ha16, _⟩
  step as ⟨b16, hb16, _⟩
  have ha16v : a16.val = a.val % 65536 := by
    rw [ha16]
    exact Nat.and_two_pow_sub_one_eq_mod _ 16
  have hb16v : b16.val = b.val % 65536 := by
    rw [hb16]
    exact Nat.and_two_pow_sub_one_eq_mod _ 16
  have hsecond := prefix_indicator a16 b16 (a.val % 65536) (b.val % 65536)
    (by rw [UScalar.eq_equiv, ha16v, hb16v])
  step as ⟨second, hsecondv, hsecondb⟩
  step as ⟨a24, ha24, _⟩
  step as ⟨b24, hb24, _⟩
  have ha24v : a24.val = a.val % 16777216 := by
    rw [ha24]
    exact Nat.and_two_pow_sub_one_eq_mod _ 24
  have hb24v : b24.val = b.val % 16777216 := by
    rw [hb24]
    exact Nat.and_two_pow_sub_one_eq_mod _ 24
  have hthird := prefix_indicator a24 b24 (a.val % 16777216) (b.val % 16777216)
    (by rw [UScalar.eq_equiv, ha24v, hb24v])
  step as ⟨third, hthirdv, hthirdb⟩
  step*
  constructor
  · simp only [WordPrefix.prefixValue]
    omega
  · omega

/-- Two numbers whose exclusive or is zero are equal. -/
theorem xor_zero_eq (a b : ℕ) (h : a ^^^ b = 0) : a = b := by
  calc a = a ^^^ (b ^^^ b) := by rw [Nat.xor_self, Nat.xor_zero]
    _ = (a ^^^ b) ^^^ b := by rw [Nat.xor_assoc]
    _ = 0 ^^^ b := by rw [h]
    _ = b := Nat.zero_xor b

/-- Equality of three packed bytes implies equality of each byte. -/
theorem word3_bytes (a0 a1 a2 b0 b1 b2 : U8)
    (h : a0.val + a1.val * 256 + a2.val * 65536 = b0.val + b1.val * 256 + b2.val * 65536) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 := by
  have ha0 := a0.hBounds
  have ha1 := a1.hBounds
  have ha2 := a2.hBounds
  have hb0 := b0.hBounds
  have hb1 := b1.hBounds
  have hb2 := b2.hBounds
  norm_num [U8.numBits_eq] at ha0 ha1 ha2 hb0 hb1 hb2
  refine ⟨(UScalar.eq_equiv _ _).mpr ?_, (UScalar.eq_equiv _ _).mpr ?_,
    (UScalar.eq_equiv _ _).mpr ?_⟩ <;> omega

/-- The bytes lo `lo` on agree for `n` bytes: what the walk's comparison establishes (the
bytes before `lo` are its assumption, checked separately by `prefix_equal`). -/
def RunFrom (data : List U8) (p q lo n : ℕ) : Prop :=
  ∀ k, lo ≤ k → k < n → data[p + k]! = data[q + k]!

/-- The same on the two windows the comparison reads (`a` from `p`, `b` from `q`). -/
def SRun (a b : List U8) (lo n : ℕ) : Prop :=
  ∀ k, lo ≤ k → k < n → a[k]! = b[k]!

/-- Four bytes of a list from `i` on as a little-endian number. -/
def W4 (l : List U8) (i : ℕ) : ℕ :=
  (l[i]!).val + (l[i + 1]!).val * 256 + (l[i + 2]!).val * 65536 + (l[i + 3]!).val * 16777216

theorem W4_lt (l : List U8) (i : ℕ) : W4 l i < 4294967296 := by
  have h0 : (l[i]!).val < 256 := by scalar_tac
  have h1 : (l[i + 1]!).val < 256 := by scalar_tac
  have h2 : (l[i + 2]!).val < 256 := by scalar_tac
  have h3 : (l[i + 3]!).val < 256 := by scalar_tac
  unfold W4
  omega

theorem srun_word {a b : List U8} {lo i : ℕ} (hr : SRun a b lo i) (h : W4 a i = W4 b i) :
    SRun a b lo (i + 4) := by
  unfold W4 at h
  obtain ⟨h0, h1, h2, h3⟩ := word_bytes _ _ _ _ _ _ _ _ h
  intro k hk0 hk
  by_cases hki : k < i
  · exact hr k hk0 hki
  · have hc : k = i ∨ k = i + 1 ∨ k = i + 2 ∨ k = i + 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3

theorem srun_prefix {a b : List U8} {lo i : ℕ} (hr : SRun a b lo i) :
    SRun a b lo (i + WordPrefix.prefixValue (W4 a i) (W4 b i)) := by
  have hbound := WordPrefix.prefixValue_le (W4 a i) (W4 b i)
  have hbytes := WordPrefix.prefix_bytes a[i]! a[i + 1]! a[i + 2]! a[i + 3]!
    b[i]! b[i + 1]! b[i + 2]! b[i + 3]!
  dsimp only at hbytes
  have hA : W4 a i = (a[i]!).val + (a[i + 1]!).val * 256 + (a[i + 2]!).val * 65536 +
      (a[i + 3]!).val * 16777216 := rfl
  have hB : W4 b i = (b[i]!).val + (b[i + 1]!).val * 256 + (b[i + 2]!).val * 65536 +
      (b[i + 3]!).val * 16777216 := rfl
  rw [← hA, ← hB] at hbytes
  intro k hk0 hk
  by_cases hki : k < i
  · exact hr k hk0 hki
  · have hc : k = i ∨ k = i + 1 ∨ k = i + 2 := by omega
    rcases hc with rfl | rfl | rfl
    · exact hbytes.1 (by omega)
    · exact hbytes.2.1 (by omega)
    · exact hbytes.2.2 (by omega)

/-- The word of eight bytes: its low and high four bytes. -/
@[step]
theorem word8_spec (data : Aeneas.Std.Slice U8) (p : Usize) (hp : p.val + 8 ≤ data.val.length) :
    word8 data p ⦃ r => r.val = W4 data.val p.val + W4 data.val (p.val + 4) * 4294967296 ⦄ := by
  unfold word8
  step as ⟨i, hi⟩
  have hsub := core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    ({ start := p, «end» := i } : core.ops.range.Range Usize) data (by simp; scalar_tac) (by simp; scalar_tac)
  step as ⟨w, hw1, hw2⟩
  have hwlen : w.val.length = 8 := by
    have h := hw2
    simp only [Slice.length] at h
    omega
  have hb : ∀ j, j < 8 → w.val[j]! = data.val[p.val + j]! := by
    intro j hj
    rw [hw1]
    exact Gzip.Proofs.Crc.slice_getElem! data.val p.val i.val j (by omega) (by omega)
  have hl0 : (data.val[p.val]!).val < 256 := by scalar_tac
  have hl1 : (data.val[p.val + 1]!).val < 256 := by scalar_tac
  have hl2 : (data.val[p.val + 2]!).val < 256 := by scalar_tac
  have hl3 : (data.val[p.val + 3]!).val < 256 := by scalar_tac
  have hl4 : (data.val[p.val + 4]!).val < 256 := by scalar_tac
  have hl5 : (data.val[p.val + 5]!).val < 256 := by scalar_tac
  have hl6 : (data.val[p.val + 6]!).val < 256 := by scalar_tac
  have hl7 : (data.val[p.val + 7]!).val < 256 := by scalar_tac
  have byte_of : ∀ j, j < 8 → ∀ (b : U8) (c : U64), b = w.val[j]! →
      c = UScalar.cast .U64 b → c.val = (data.val[p.val + j]!).val := by
    intro j hj b c hbj hc
    rw [hc, UScalar.cast_val_eq, hbj, hb j hj]
    have := (data.val[p.val + j]!).hBounds
    norm_num [U8.numBits_eq] at this ⊢
    omega
  step as ⟨b0, hb0⟩
  step as ⟨c0, hc0⟩
  have hc0v := byte_of 0 (by omega) b0 c0 (by rw [hb0, getElem!_pos w.val 0 (by omega)]) hc0
  step as ⟨b1, hb1⟩
  step as ⟨c1, hc1⟩
  have hc1v := byte_of 1 (by omega) b1 c1 (by rw [hb1, getElem!_pos w.val 1 (by omega)]) hc1
  step as ⟨m1, hm1⟩
  step as ⟨s1, hs1⟩
  step as ⟨b2, hb2⟩
  step as ⟨c2, hc2⟩
  have hc2v := byte_of 2 (by omega) b2 c2 (by rw [hb2, getElem!_pos w.val 2 (by omega)]) hc2
  step as ⟨m2, hm2⟩
  step as ⟨s2, hs2⟩
  step as ⟨b3, hb3⟩
  step as ⟨c3, hc3⟩
  have hc3v := byte_of 3 (by omega) b3 c3 (by rw [hb3, getElem!_pos w.val 3 (by omega)]) hc3
  step as ⟨m3, hm3⟩
  step as ⟨s3, hs3⟩
  step as ⟨b4, hb4⟩
  step as ⟨c4, hc4⟩
  have hc4v := byte_of 4 (by omega) b4 c4 (by rw [hb4, getElem!_pos w.val 4 (by omega)]) hc4
  step as ⟨m4, hm4⟩
  step as ⟨s4, hs4⟩
  step as ⟨b5, hb5⟩
  step as ⟨c5, hc5⟩
  have hc5v := byte_of 5 (by omega) b5 c5 (by rw [hb5, getElem!_pos w.val 5 (by omega)]) hc5
  step as ⟨m5, hm5⟩
  step as ⟨s5, hs5⟩
  step as ⟨b6, hb6⟩
  step as ⟨c6, hc6⟩
  have hc6v := byte_of 6 (by omega) b6 c6 (by rw [hb6, getElem!_pos w.val 6 (by omega)]) hc6
  step as ⟨m6, hm6⟩
  step as ⟨s6, hs6⟩
  step as ⟨b7, hb7⟩
  step as ⟨c7, hc7⟩
  have hc7v := byte_of 7 (by omega) b7 c7 (by rw [hb7, getElem!_pos w.val 7 (by omega)]) hc7
  step as ⟨m7, hm7⟩
  step as ⟨r, hr⟩
  simp only [W4, Nat.add_assoc, Nat.reduceAdd]
  simp only [Nat.add_zero] at hc0v
  omega

/-- A failed comparison of eight bytes gives the agreeing prefix (at most seven bytes). -/
theorem prefix7_run (a b : List U8) (lo i : ℕ) (x y : U64) (hr : SRun a b lo i)
    (hx : x.val = W4 a i + W4 a (i + 4) * 4294967296)
    (hy : y.val = W4 b i + W4 b (i + 4) * 4294967296) :
    prefix7 x y ⦃ r => r.val ≤ 7 ∧ SRun a b lo (i + r.val) ⦄ := by
  have ha0 := W4_lt a i
  have ha4 := W4_lt a (i + 4)
  have hb0 := W4_lt b i
  have hb4 := W4_lt b (i + 4)
  refine WP.spec_mono (PrefixModel.raw_spec x y) ?_
  intro r hres
  obtain ⟨hvalue, hbound⟩ := hres
  have heq : r.val = PrefixFlags.equalityFlags64 x.val y.val := by
    rw [hvalue]
    by_cases hz : x.val ^^^ y.val = 0
    · rw [if_pos hz]
      have hxy := xor_zero_eq x.val y.val hz
      rw [hxy]
      simp [PrefixFlags.equalityFlags64]
    · rw [if_neg hz]
      have ht : ∀ k < 64, (CTZ64.val[k]!).val = DeBruijn.counts64[k]! := by
        intro k hk
        interval_cases k <;> norm_num [CTZ64, Array.make, DeBruijn.counts64]
      have hi := DeBruijn.index64_lt (x.val ^^^ y.val)
      change (CTZ64.val[DeBruijn.index64 (x.val ^^^ y.val)]!).val / 8 = _
      rw [ht _ hi]
      have hxor : x.val ^^^ y.val < 18446744073709551616 := by
        have hb := (x ^^^ y).hBounds
        norm_num [U64.numBits_eq] at hb
        exact hb
      rw [DeBruijn.bytesNat64 _ hxor hz]
      change PrefixFlags.equalityFlags64 (x.val ^^^ y.val) 0 = _
      exact PrefixFlags.xor_equalityFlags64 x.val y.val
  rw [PrefixFlags.equalityFlags64_split] at heq
  have hxl : x.val % 4294967296 = W4 a i := by omega
  have hyl : y.val % 4294967296 = W4 b i := by omega
  have hxh : x.val / 4294967296 = W4 a (i + 4) := by omega
  have hyh : y.val / 4294967296 = W4 b (i + 4) := by omega
  rw [hxl, hyl, hxh, hyh] at heq
  refine ⟨hbound, ?_⟩
  by_cases hlo : W4 a i = W4 b i
  · rw [if_pos hlo] at heq
    have hrun := srun_prefix (srun_word hr hlo)
    rw [heq]
    simpa only [Nat.add_assoc] using hrun
  · rw [if_neg hlo] at heq
    rw [heq]
    exact srun_prefix hr

/-- The byte loop of the comparison's tail. -/
theorem tail_body (a b : Aeneas.Std.Slice U8) (limit n : Usize) (lo : ℕ)
    (hla : limit.val ≤ a.val.length) (hlb : limit.val ≤ b.val.length)
    (hf : lo ≤ n.val) (hn : n.val ≤ limit.val) (hr : SRun a.val b.val lo n.val) :
    (if n < limit then do
        let i ← Slice.index_usize a n
        let i1 ← Slice.index_usize b n
        if i = i1 then do
          let n1 ← n + 1#usize
          ok (ControlFlow.cont n1)
        else ok (ControlFlow.done n)
      else ok (ControlFlow.done n)) ⦃ r =>
      match r with
      | .done m => lo ≤ m.val ∧ m.val ≤ limit.val ∧ SRun a.val b.val lo m.val
      | .cont m => m.val = n.val + 1 ∧ lo ≤ m.val ∧ m.val ≤ limit.val ∧
          SRun a.val b.val lo m.val ⦄ := by
  split
  · rename_i hlt
    have hlt' : n.val < limit.val := (UScalar.lt_equiv n limit).mp hlt
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    split
    · rename_i heq
      step as ⟨n1, hn1⟩
      refine ⟨hn1, by omega, by omega, ?_⟩
      intro k hk0 hk
      by_cases hk' : k < n.val
      · exact hr k hk0 hk'
      · have hkn : k = n.val := by omega
        subst k
        have h1 : i = a.val[n.val]! := by rw [hi, getElem!_pos a.val n.val (by omega)]
        have h3 : i1 = b.val[n.val]! := by rw [hi1, getElem!_pos b.val n.val (by omega)]
        exact h1.symm.trans (heq.trans h3)
    · simp only [WP.spec_ok]
      exact ⟨hf, hn, hr⟩
  · simp only [WP.spec_ok]
    exact ⟨hf, hn, hr⟩

theorem tail_loop0 (a b : Aeneas.Std.Slice U8) (limit n : Usize) (lo : ℕ)
    (hla : limit.val ≤ a.val.length) (hlb : limit.val ≤ b.val.length)
    (hf : lo ≤ n.val) (hn : n.val ≤ limit.val) (hr : SRun a.val b.val lo n.val) :
    match_tail_loop0 a b limit n ⦃ m =>
      lo ≤ m.val ∧ m.val ≤ limit.val ∧ SRun a.val b.val lo m.val ⦄ := by
  unfold match_tail_loop0
  apply loop.spec_decr_nat (fun m => limit.val - m.val)
    (fun m => lo ≤ m.val ∧ m.val ≤ limit.val ∧ SRun a.val b.val lo m.val)
  · intro m hm
    unfold match_tail_loop0.body
    refine WP.spec_mono (tail_body a b limit m lo hla hlb hm.1 hm.2.1 hm.2.2) ?_
    intro r hr'
    cases r with
    | done m => exact hr'
    | cont m' =>
        obtain ⟨heq, hf', hb', hrun⟩ := hr'
        exact ⟨⟨hf', hb', hrun⟩, by omega⟩
  · exact ⟨hf, hn, hr⟩

theorem tail_loop1 (a b : Aeneas.Std.Slice U8) (limit n : Usize) (lo : ℕ)
    (hla : limit.val ≤ a.val.length) (hlb : limit.val ≤ b.val.length)
    (hf : lo ≤ n.val) (hn : n.val ≤ limit.val) (hr : SRun a.val b.val lo n.val) :
    match_tail_loop1 a b limit n ⦃ m =>
      lo ≤ m.val ∧ m.val ≤ limit.val ∧ SRun a.val b.val lo m.val ⦄ := by
  unfold match_tail_loop1
  apply loop.spec_decr_nat (fun m => limit.val - m.val)
    (fun m => lo ≤ m.val ∧ m.val ≤ limit.val ∧ SRun a.val b.val lo m.val)
  · intro m hm
    unfold match_tail_loop1.body
    refine WP.spec_mono (tail_body a b limit m lo hla hlb hm.1 hm.2.1 hm.2.2) ?_
    intro r hr'
    cases r with
    | done m => exact hr'
    | cont m' =>
        obtain ⟨heq, hf', hb', hrun⟩ := hr'
        exact ⟨⟨hf', hb', hrun⟩, by omega⟩
  · exact ⟨hf, hn, hr⟩

theorem tail_spec (a b : Aeneas.Std.Slice U8) (n limit : Usize) (lo : ℕ)
    (hla : limit.val ≤ a.val.length) (hlb : limit.val ≤ b.val.length)
    (hf : lo ≤ n.val) (hn : n.val ≤ limit.val) (hr : SRun a.val b.val lo n.val) :
    match_tail a b n limit ⦃ m =>
      lo ≤ m.val ∧ m.val ≤ limit.val ∧ SRun a.val b.val lo m.val ⦄ := by
  unfold match_tail
  step as ⟨rem, hrem⟩
  split
  · rename_i h4
    have h4' : n.val + 4 ≤ limit.val := by scalar_tac
    step as ⟨x, hx⟩
    step as ⟨y, hy⟩
    split
    · step as ⟨pv, hpv, hpv3⟩
      step as ⟨m, hm⟩
      refine ⟨by omega, by omega, ?_⟩
      rw [hm, hpv, hx, hy]
      exact srun_prefix hr
    · rename_i hne
      have h : x.val = y.val := by simpa using hne
      have hw : W4 a.val n.val = W4 b.val n.val := by
        rw [hx, hy] at h
        exact h
      step as ⟨n1, hn1⟩
      have hr4 := srun_word hr hw
      rw [← hn1] at hr4
      exact tail_loop0 a b limit n1 lo hla hlb (by omega) (by omega) hr4
  · exact tail_loop1 a b limit n lo hla hlb hf hn hr

/-- The comparison's main loop: eight bytes per step. -/
theorem from_body (a b : Aeneas.Std.Slice U8) (limit n : Usize) (lo : ℕ)
    (hla : limit.val ≤ a.val.length) (hlb : limit.val ≤ b.val.length)
    (hf : lo ≤ n.val) (hn : n.val ≤ limit.val) (hr : SRun a.val b.val lo n.val) :
    match_from_loop.body limit a b n ⦃ r =>
      match r with
      | .done m => lo ≤ m.val ∧ m.val ≤ limit.val ∧ SRun a.val b.val lo m.val
      | .cont m => m.val = n.val + 8 ∧ lo ≤ m.val ∧ m.val ≤ limit.val ∧
          SRun a.val b.val lo m.val ⦄ := by
  unfold match_from_loop.body
  step as ⟨rem, hrem⟩
  split
  · rename_i h8
    have h8' : n.val + 8 ≤ limit.val := by scalar_tac
    step as ⟨x, hx⟩
    step as ⟨y, hy⟩
    split
    · have hp7 := prefix7_run a.val b.val lo n.val x y hr hx hy
      step as ⟨pv, hpv3, hpv⟩
      step as ⟨m, hm⟩
      refine ⟨by omega, by omega, ?_⟩
      rw [hm]
      exact hpv
    · rename_i hne
      have hv : x.val = y.val := by simpa using hne
      rw [hx, hy] at hv
      have hl := W4_lt a.val n.val
      have hl' := W4_lt b.val n.val
      have hw0 : W4 a.val n.val = W4 b.val n.val := by omega
      have hw4 : W4 a.val (n.val + 4) = W4 b.val (n.val + 4) := by omega
      have hr4 := srun_word hr hw0
      have hr8 := srun_word hr4 hw4
      step as ⟨n1, hn1⟩
      refine ⟨hn1, by omega, by omega, ?_⟩
      rw [hn1]
      simpa only [Nat.add_assoc] using hr8
  · have ht := tail_spec a b n limit lo hla hlb hf hn hr
    step as ⟨m, hm1, hm2, hm3⟩
    exact ⟨hm1, hm2, hm3⟩

theorem from_loop (a b : Aeneas.Std.Slice U8) (limit n : Usize) (lo : ℕ)
    (hla : limit.val ≤ a.val.length) (hlb : limit.val ≤ b.val.length)
    (hf : lo ≤ n.val) (hn : n.val ≤ limit.val) (hr : SRun a.val b.val lo n.val) :
    match_from_loop limit a b n ⦃ m =>
      lo ≤ m.val ∧ m.val ≤ limit.val ∧ SRun a.val b.val lo m.val ⦄ := by
  unfold match_from_loop
  apply loop.spec_decr_nat (fun m => limit.val - m.val)
    (fun m => lo ≤ m.val ∧ m.val ≤ limit.val ∧ SRun a.val b.val lo m.val)
  · intro m hm
    refine WP.spec_mono (from_body a b limit m lo hla hlb hm.1 hm.2.1 hm.2.2) ?_
    intro r hr'
    cases r with
    | done m => exact hr'
    | cont m' =>
        obtain ⟨heq, hf', hb', hrun⟩ := hr'
        exact ⟨⟨hf', hb', hrun⟩, by omega⟩
  · exact ⟨hf, hn, hr⟩

/-- The walk's comparison lo `lb` on: at least `lb`, and the bytes lo `lb` on agree. -/
theorem from_bounded_spec (data : Aeneas.Std.Slice U8) (p q lb limit : Usize)
    (hq : q.val ≤ p.val) (hl : p.val + limit.val ≤ data.val.length) :
    match_from data p q lb limit ⦃ n =>
      lb.val ≤ n.val ∧ n.val ≤ max lb.val limit.val ∧ RunFrom data.val p.val q.val lb.val n.val ⦄ := by
  unfold match_from
  step as ⟨i, hi⟩
  have hsub := core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    ({ start := p, «end» := i } : core.ops.range.Range Usize) data (by simp; scalar_tac) (by simp; scalar_tac)
  step as ⟨a, ha1, ha2⟩
  have halen : limit.val ≤ a.val.length := by
    have h := ha2
    simp only [Slice.length] at h
    omega
  have hap : ∀ k, k < limit.val → a.val[k]! = data.val[p.val + k]! := by
    intro k hk
    rw [ha1]
    exact Gzip.Proofs.Crc.slice_getElem! data.val p.val i.val k (by omega) (by omega)
  step as ⟨j, hj⟩
  have hsub' := core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    ({ start := q, «end» := j } : core.ops.range.Range Usize) data (by simp; scalar_tac) (by simp; scalar_tac)
  step as ⟨b, hb1, hb2⟩
  have hblen : limit.val ≤ b.val.length := by
    have h := hb2
    simp only [Slice.length] at h
    omega
  have hbp : ∀ k, k < limit.val → b.val[k]! = data.val[q.val + k]! := by
    intro k hk
    rw [hb1]
    exact Gzip.Proofs.Crc.slice_getElem! data.val q.val j.val k (by omega) (by omega)
  split
  · simp only [WP.spec_ok]
    exact ⟨Nat.le_refl _, Nat.le_max_left _ _, by intro k h1 h2; omega⟩
  · rename_i hlt
    have hlt' : lb.val < limit.val := by scalar_tac
    have hfl := from_loop a b limit lb lb.val halen hblen (Nat.le_refl _) (by omega)
      (by intro k h1 h2; omega)
    step as ⟨m, hm1, hm2, hm3⟩
    refine ⟨hm1, hm2.trans (Nat.le_max_right _ _), ?_⟩
    intro k hk0 hk
    rw [← hap k (by omega), ← hbp k (by omega)]
    exact hm3 k hk0 hk

@[step]
theorem from_spec (data : Aeneas.Std.Slice U8) (p q lb limit : Usize)
    (hq : q.val ≤ p.val) (hl : p.val + limit.val ≤ data.val.length) :
    match_from data p q lb limit ⦃ n =>
      lb.val ≤ n.val ∧ RunFrom data.val p.val q.val lb.val n.val ⦄ := by
  refine WP.spec_mono (from_bounded_spec data p q lb limit hq hl) ?_
  intro n hn
  exact ⟨hn.1, hn.2.2⟩

@[step]
theorem length (data : Aeneas.Std.Slice U8) (p q stop : Usize)
    (hq : q.val ≤ p.val) (hp : p.val ≤ stop.val) (hend : stop.val ≤ data.val.length) :
    match_length data p q stop ⦃ n =>
      n.val ≤ 258 ∧ n.val ≤ stop.val - p.val ∧ EqualRun data.val p.val q.val n.val ⦄ := by
  have hcontinue : ∀ limit : Usize,
      limit.val ≤ 258 → limit.val ≤ stop.val - p.val →
      match_from data p q 0#usize limit ⦃ n =>
        n.val ≤ 258 ∧ n.val ≤ stop.val - p.val ∧ EqualRun data.val p.val q.val n.val ⦄ := by
    intro limit hhi hrem
    refine WP.spec_mono (from_bounded_spec data p q 0#usize limit hq (by omega)) ?_
    intro n hn
    have h0 : (0#usize).val = 0 := by scalar_tac
    simp only [h0] at hn
    have hnlim : n.val ≤ limit.val := by simpa using hn.2.1
    refine ⟨by omega, by omega, ?_⟩
    intro k hk
    exact hn.2.2 k (Nat.zero_le k) hk
  unfold match_length
  step*
  all_goals (split <;> step*)

/-- The level-1 length: a disagreement in the low three bytes gives 0 (no copy), an
agreement of exactly three gives 3, and four agreeing bytes are measured in full. -/
@[step]
theorem first_length_spec (data : Aeneas.Std.Slice U8) (p q stop : Usize)
    (hq : q.val ≤ p.val) (hp : p.val ≤ stop.val) (hend : stop.val ≤ data.val.length) :
    first_length data p q stop ⦃ n =>
      n.val ≤ 258 ∧ n.val ≤ stop.val - p.val ∧ EqualRun data.val p.val q.val n.val ⦄ := by
  unfold first_length
  step as ⟨rem, hrem⟩
  split
  · rename_i h4
    have hp4 : p.val + 4 ≤ data.val.length := by scalar_tac
    have hq4 : q.val + 4 ≤ data.val.length := by omega
    step as ⟨wp, hwp⟩
    step as ⟨wq, hwq⟩
    step as ⟨x, hx⟩
    step as ⟨low, hlow⟩
    have hxv : x.val = wp.val ^^^ wq.val := by rw [hx, UScalar.val_xor]
    have hlowv : low.val = x.val % 16777216 := by
      rw [hlow, UScalar.val_and]
      exact Nat.and_two_pow_sub_one_eq_mod x.val 24
    split
    · step*
      simp [EqualRun]
    · rename_i hlow0
      have hl0 : low.val = 0 := by simpa using hlow0
      have hmod : wp.val % 16777216 = wq.val % 16777216 := by
        have h := hlowv
        rw [hl0, hxv] at h
        change 0 = (wp.val ^^^ wq.val) % 2 ^ 24 at h
        rw [Nat.xor_mod_two_pow] at h
        exact xor_zero_eq _ _ h.symm
      have hl0' : (data.val[p.val]!).val < 256 := by scalar_tac
      have hl1' : (data.val[p.val + 1]!).val < 256 := by scalar_tac
      have hl2' : (data.val[p.val + 2]!).val < 256 := by scalar_tac
      have hl3' : (data.val[p.val + 3]!).val < 256 := by scalar_tac
      have hm0' : (data.val[q.val]!).val < 256 := by scalar_tac
      have hm1' : (data.val[q.val + 1]!).val < 256 := by scalar_tac
      have hm2' : (data.val[q.val + 2]!).val < 256 := by scalar_tac
      have hm3' : (data.val[q.val + 3]!).val < 256 := by scalar_tac
      have hp3 : wp.val % 16777216 = (data.val[p.val]!).val + (data.val[p.val + 1]!).val * 256 +
          (data.val[p.val + 2]!).val * 65536 := by
        rw [hwp]
        omega
      have hq3 : wq.val % 16777216 = (data.val[q.val]!).val + (data.val[q.val + 1]!).val * 256 +
          (data.val[q.val + 2]!).val * 65536 := by
        rw [hwq]
        omega
      have h3 : (data.val[p.val]!).val + (data.val[p.val + 1]!).val * 256 + (data.val[p.val + 2]!).val * 65536 =
          (data.val[q.val]!).val + (data.val[q.val + 1]!).val * 256 + (data.val[q.val + 2]!).val * 65536 :=
        hp3.symm.trans (hmod.trans hq3)
      obtain ⟨e0, e1, e2⟩ := word3_bytes _ _ _ _ _ _ h3
      split
      · step*
        refine ⟨by scalar_tac, by scalar_tac, ?_⟩
        intro k hk
        have hk3 : k < 3 := by scalar_tac
        have hc : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases hc with rfl | rfl | rfl
        · simpa using e0
        · exact e1
        · exact e2
      · have hx0 : x.val = 0 := by scalar_tac
        have hsame : wp.val = wq.val := xor_zero_eq _ _ (by rw [← hxv]; exact hx0)
        rw [hwp, hwq] at hsame
        obtain ⟨f0, f1, f2, f3⟩ := word_bytes _ _ _ _ _ _ _ _ hsame
        have hfour : EqualRun data.val p.val q.val 4 := by
          intro k hk
          have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hcases with rfl | rfl | rfl | rfl
          · simpa using f0
          · exact f1
          · exact f2
          · exact f3
        have hcontinue : ∀ limit : Usize,
            4 ≤ limit.val → limit.val ≤ 258 → limit.val ≤ stop.val - p.val →
            match_from data p q 4#usize limit ⦃ n =>
              n.val ≤ 258 ∧ n.val ≤ stop.val - p.val ∧ EqualRun data.val p.val q.val n.val ⦄ := by
          intro limit hlo hhi hrem
          refine WP.spec_mono (from_bounded_spec data p q 4#usize limit hq (by omega)) ?_
          intro n hn
          have h4val : (4#usize).val = 4 := by scalar_tac
          simp only [h4val] at hn
          have hnlim : n.val ≤ limit.val := by simpa only [Nat.max_eq_right hlo] using hn.2.1
          refine ⟨by omega, by omega, ?_⟩
          intro k hk
          by_cases hk4 : k < 4
          · exact hfour k hk4
          · exact hn.2.2 k (by omega) hk
        step*
        all_goals (split <;> step*)
  · step*

/-- The match predicate gives the specification's overlapping-copy semantics. -/
theorem copy_of_equal_run (data : List U8) (p q n : ℕ)
    (hq : q < p) (hbound : p + n ≤ data.length) (he : EqualRun data p q n) :
    Gzip.Spec.copy_spec (data.take p) ((p - q : ℕ) : ℤ) n (data.take (p + n)) := by
  have hp : p ≤ data.length := by omega
  have hlen : (data.take p).length = p := List.length_take_of_le hp
  have hlen' : (data.take (p + n)).length = p + n := List.length_take_of_le hbound
  refine ⟨trivial, ?_, ?_, ?_, ?_⟩
  · rw [hlen]
    constructor <;> omega
  · rw [hlen, hlen']
    push_cast
    rfl
  · simp only [List.drop_zero, hlen, Int.toNat_natCast, List.take_take]
    rw [Nat.min_eq_left (by omega)]
  · intro k hk0 hk1
    rw [hlen] at hk0
    rw [hlen'] at hk1
    have hk : 0 ≤ k := by omega
    have hki : k.toNat < p + n := by omega
    have hkd : 0 ≤ k - (p - q : ℕ) := by omega
    have hkdir : (k - (p - q : ℕ)).toNat < p + n := by omega
    have hr := he (k.toNat - p) (by omega)
    have hleft : p + (k.toNat - p) = k.toNat := by omega
    have hright : q + (k.toNat - p) = (k - (p - q : ℕ)).toNat := by omega
    rw [hleft, hright] at hr
    rw [getElem!_pos (data.take (p + n)) k.toNat (by rw [hlen']; exact hki),
      getElem!_pos (data.take (p + n)) (k - (p - q : ℕ)).toNat (by rw [hlen']; exact hkdir)]
    simp only [List.getElem_take]
    simpa only [getElem!_pos data k.toNat (by omega),
      getElem!_pos data (k - (p - q : ℕ)).toNat (by omega)] using hr

def ValidMatch (data : List U8) (p stop length distance : ℕ) : Prop :=
  distance = 0 ∨ (3 ≤ length ∧ length ≤ 258 ∧ p + length ≤ stop ∧
    0 < distance ∧ distance ≤ p ∧ distance ≤ 32768 ∧ EqualRun data p (p - distance) length)

/-- The candidate filter of the chain walk: total where `p + best` is in the data and `q`
before `p` (its result decides only whether a candidate is measured). -/
@[step]
theorem can_beat_spec (data : Aeneas.Std.Slice U8) (p q best : Usize)
    (hq : q.val < p.val) (hpb : p.val + best.val < data.val.length) :
    can_beat data p q best ⦃ _ => True ⦄ := by
  unfold can_beat
  split
  · step*
  · step*

theorem find_body (data : Aeneas.Std.Slice U8) (p stop : Usize)
    (chain : Aeneas.Std.Slice U32) (depth best distance candidate count : Usize)
    (hp : p.val ≤ stop.val) (hend : stop.val ≤ data.val.length)
    (hchain : chain.val.length = 65536) (hc : count.val ≤ depth.val)
    (hb : 2 ≤ best.val ∧ best.val ≤ 258)
    (hv : ValidMatch data.val p.val stop.val best.val distance.val) :
    find_match_loop.body data p stop chain depth best distance candidate count ⦃ r =>
      match r with
      | .done (b, d) => (2 ≤ b.val ∧ b.val ≤ 258) ∧ ValidMatch data.val p.val stop.val b.val d.val
      | .cont (b, d, _, c) => (2 ≤ b.val ∧ b.val ≤ 258) ∧ ValidMatch data.val p.val stop.val b.val d.val ∧
          c.val = count.val + 1 ∧ c.val ≤ depth.val ⦄ := by
  unfold find_match_loop.body
  step*
  split
  · step*
  · step as ⟨d, hd, hdq⟩
    split
    · step*
    · have hslot : (q &&& 32767#usize).val < chain.length := by
        rw [UScalar.val_and]
        change q.val &&& 32767 < chain.val.length
        rw [hchain]
        have hb : q.val &&& 32767 ≤ 32767 := Nat.and_le_right
        omega
      step as ⟨i1, hi1⟩
      split
      · have hqp : q.val < p.val := by scalar_tac
        have hpb : p.val + best.val < data.val.length := by scalar_tac
        step as ⟨b, _⟩
        split
        · step as ⟨len, hlen0, hlen1, hlenEq⟩
          split <;> step*
          refine ⟨by scalar_tac, hlen0, Or.inr ?_, count1_post, by scalar_tac⟩
          refine ⟨by scalar_tac, hlen0, by omega, by scalar_tac, by omega, by scalar_tac, ?_⟩
          have hdiff : p.val - d.val = q.val := by omega
          rw [hdiff]
          exact hlenEq
        · step*
      · step*

@[step]
theorem find_loop (data : Aeneas.Std.Slice U8) (p stop : Usize)
    (chain : Aeneas.Std.Slice U32) (depth best distance candidate count : Usize)
    (hp : p.val ≤ stop.val) (hend : stop.val ≤ data.val.length)
    (hchain : chain.val.length = 65536) (hc : count.val ≤ depth.val)
    (hb : 2 ≤ best.val ∧ best.val ≤ 258)
    (hv : ValidMatch data.val p.val stop.val best.val distance.val) :
    find_match_loop data p stop chain depth best distance candidate count ⦃ r =>
      (2 ≤ r.1.val ∧ r.1.val ≤ 258) ∧ ValidMatch data.val p.val stop.val r.1.val r.2.val ⦄ := by
  unfold find_match_loop
  apply loop.spec_decr_nat (fun (_, _, _, c) => depth.val - c.val)
    (fun (b, d, _, c) => c.val ≤ depth.val ∧ (2 ≤ b.val ∧ b.val ≤ 258) ∧
      ValidMatch data.val p.val stop.val b.val d.val)
  · rintro ⟨b, d, ca, c⟩ ⟨hc', hb', hv'⟩
    refine WP.spec_mono (find_body data p stop chain depth b d ca c hp hend hchain hc' hb' hv') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨b', d', ca', c'⟩ := state
        obtain ⟨hb'', hv'', heq, hc''⟩ := hr
        exact ⟨⟨hc'', hb'', hv''⟩, by change depth.val - c'.val < depth.val - c.val; omega⟩
  · exact ⟨hc, hb, hv⟩

@[step]
theorem hash4_bound (data : Aeneas.Std.Slice U8) (p mask : Usize)
    (hp : p.val + 4 ≤ data.val.length) :
    Gzip.solution.hash4 data p mask ⦃ h => h.val ≤ mask.val ⦄ := by
  unfold Gzip.solution.hash4
  step as ⟨i, hi⟩
  step as ⟨w, hw⟩
  have hw32 : w.val < 4294967296 := by
    have hwi : w.val = i.val := by
      rw [hw]
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      scalar_tac
    rw [hwi]
    scalar_tac
  step as ⟨a, ha, ha2⟩
  have hab : a.val ≤ 255 := by
    rw [ha, UScalar.val_and]
    have := @Nat.and_le_right w.val (255#usize).val
    simpa using this
  step as ⟨s8, hs8⟩
  case hy => rcases System.Platform.numBits_eq with h | h <;> simp [h]
  step as ⟨b, hb, hb2⟩
  have hbb : b.val ≤ 255 := by
    rw [hb, UScalar.val_and]
    have := @Nat.and_le_right s8.val (255#usize).val
    simpa using this
  step as ⟨s16, hs16⟩
  case hy => rcases System.Platform.numBits_eq with h | h <;> simp [h]
  step as ⟨c, hc, hc2⟩
  have hcb : c.val ≤ 255 := by
    rw [hc, UScalar.val_and]
    have := @Nat.and_le_right s16.val (255#usize).val
    simpa using this
  step as ⟨d, hd⟩
  case hy => rcases System.Platform.numBits_eq with h | h <;> simp [h]
  have hdb : d.val ≤ 255 := by
    rw [hd, Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow]
    omega
  step*
  rw [UScalar.val_and]
  exact Nat.and_le_right

@[step]
theorem hash5_bound (data : Aeneas.Std.Slice U8) (p mask : Usize)
    (hp : p.val + 5 ≤ data.val.length) :
    Gzip.solution.hash5 data p mask ⦃ h => h.val ≤ mask.val ⦄ := by
  unfold Gzip.solution.hash5
  step as ⟨i, hi⟩
  step as ⟨w, hw⟩
  have hw32 : w.val < 4294967296 := by
    have hwi : w.val = i.val := by
      rw [hw]
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      scalar_tac
    rw [hwi]
    scalar_tac
  step as ⟨i4, hi4⟩
  step as ⟨e8, he8⟩
  step as ⟨e, he⟩
  have heb : e.val ≤ 255 := by
    have hee : e.val = e8.val := by
      rw [he]
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      scalar_tac
    rw [hee]
    scalar_tac
  step as ⟨a, ha, ha2⟩
  have hab : a.val ≤ 255 := by
    rw [ha, UScalar.val_and]
    have := @Nat.and_le_right w.val (255#usize).val
    simpa using this
  step as ⟨s8, hs8⟩
  case hy => rcases System.Platform.numBits_eq with h | h <;> simp [h]
  step as ⟨b, hb, hb2⟩
  have hbb : b.val ≤ 255 := by
    rw [hb, UScalar.val_and]
    have := @Nat.and_le_right s8.val (255#usize).val
    simpa using this
  step as ⟨s16, hs16⟩
  case hy => rcases System.Platform.numBits_eq with h | h <;> simp [h]
  step as ⟨c, hc, hc2⟩
  have hcb : c.val ≤ 255 := by
    rw [hc, UScalar.val_and]
    have := @Nat.and_le_right s16.val (255#usize).val
    simpa using this
  step as ⟨d, hd⟩
  case hy => rcases System.Platform.numBits_eq with h | h <;> simp [h]
  have hdb : d.val ≤ 255 := by
    rw [hd, Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow]
    omega
  step*
  rw [UScalar.val_and]
  exact Nat.and_le_right

@[step]
theorem chain_hash5_bound (data : Aeneas.Std.Slice U8) (p mask : Usize)
    (hp : p.val + 5 ≤ data.val.length) :
    Gzip.solution.chain_hash5 data p mask ⦃ h => h.val ≤ mask.val ⦄ := by
  unfold Gzip.solution.chain_hash5
  step as ⟨i, hi⟩
  step as ⟨w, hw⟩
  have hw32 : w.val < 4294967296 := by
    have hwi : w.val = i.val := by
      rw [hw]
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      scalar_tac
    rw [hwi]
    scalar_tac
  step as ⟨i4, hi4⟩
  step as ⟨e8, he8⟩
  step as ⟨e, he⟩
  have heb : e.val ≤ 255 := by
    have hee : e.val = e8.val := by
      rw [he]
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      scalar_tac
    rw [hee]
    scalar_tac
  step*
  rw [UScalar.val_and]
  exact Nat.and_le_right

/-- The hash of a tree's position: within the mask whenever four bytes remain. -/
@[step]
theorem tree_hash_bound (data : Aeneas.Std.Slice U8) (p mask : Usize) (five : Bool)
    (hp : p.val + 4 ≤ data.val.length) :
    Gzip.solution.tree_hash data p mask five ⦃ h => h.val ≤ mask.val ⦄ := by
  unfold Gzip.solution.tree_hash
  split
  · step as ⟨i1, hi1⟩
    split
    · step*
    · step*
  · step*

@[step]
theorem find (data : Aeneas.Std.Slice U8) (p stop h : Usize)
    (head : Aeneas.Std.Slice U32) (chain : Aeneas.Std.Slice U32) (depth : Usize)
    (hp : p.val ≤ stop.val) (hend : stop.val ≤ data.val.length)
    (hchain : chain.val.length = 65536) :
    find_match data p stop h head chain depth ⦃ r =>
      (2 ≤ r.1.val ∧ r.1.val ≤ 258) ∧ ValidMatch data.val p.val stop.val r.1.val r.2.val ⦄ := by
  unfold find_match
  step*
  all_goals simp [ValidMatch]

/-- The hash of a position, if it has one: total. -/
@[step]
theorem hash_at_spec (data : Aeneas.Std.Slice U8) (p : Usize) (head : alloc.vec.Vec U32)
    (four : Bool) (hp : p.val ≤ data.val.length) (hhead : 0 < head.val.length) :
    hash_at data p head four ⦃ _ => True ⦄ := by
  unfold hash_at
  split
  · step*
  · step*

end Gzip.Proofs.Matches
