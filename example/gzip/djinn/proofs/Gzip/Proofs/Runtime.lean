import Gzip.Proofs.Tokens
import Gzip.Proofs.Greedy
import Gzip.Proofs.Dp
import Gzip.Proofs.CrcImpl

open Aeneas Std Result
open Gzip.solution Gzip.Spec Gzip.Proofs.Writer Gzip.Proofs.Plans

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

namespace Gzip.Proofs.Runtime

attribute [local step] Copies.copy_stream

def stream (w : Gzip.solution.Writer) : List Bool :=
  byteBits w.out.val ++ lowBits w.bits.val w.count.val

def Buffered (w : Gzip.solution.Writer) : Prop :=
  w.count.val < 32 ∧ w.bits.val < 2 ^ w.count.val

@[simp] theorem stream_length (w : Gzip.solution.Writer) :
    (stream w).length = 8 * w.out.val.length + w.count.val := by
  simp [stream]

theorem space (w : Gzip.solution.Writer) (n : ℕ)
    (h : (stream w).length + 8 * n ≤ 34359738360) :
    w.out.val.length + n ≤ Usize.max := by
  simp only [stream_length] at h
  scalar_tac

theorem symbol_size (sym : ℕ) : (Symbols.encode sym).length ≤ 9 := by
  simp only [Symbols.encode, List.length_reverse, lowBits_length]
  unfold Symbols.width
  split_ifs <;> omega

theorem copy_size (len dist l d : ℕ) (hl : l ≤ 28) (hd : d ≤ 29) :
    (Copies.encode len dist l d).length ≤ 32 := by
  have hs := symbol_size (257 + l)
  have he := Costs.length_extra_bound l (by omega)
  have hd' := Costs.distance_extra_bound d (by omega)
  change Indices.le l ≤ 5 at he
  change Indices.de d ≤ 13 at hd'
  simp only [Copies.encode, List.length_append, List.length_reverse, lowBits_length]
  omega

structure TokenState (data : List U8) (start stop : ℕ) (front : List Bool)
    (ls ds : List U16) (w : Gzip.solution.Writer) (p t : Usize) : Prop where
  position : start ≤ p.val ∧ p.val ≤ stop ∧ stop ≤ data.length
  lengths : ls.length = ds.length
  index : t.val ≤ ls.length
  runs : Runs data stop p.val stop (ls.drop t.val) (ds.drop t.val)
  buffer : Buffered w
  emitted : ∃ bits, stream w = front ++ bits ∧
    bits.length ≤ 11 * (p.val - start) ∧ Tokens.Emitted data start p.val bits

theorem token_body (data : Aeneas.Std.Slice U8) (start stop : ℕ) (front : List Bool)
    (ls ds : alloc.vec.Vec U16) (w : Gzip.solution.Writer) (p t : Usize)
    (h : TokenState data.val start stop front ls.val ds.val w p t)
    (hbudget : front.length + 11 * (stop - start) + 192 ≤ 34359738360) :
    fixed_loop.body data ls ds w p t ⦃ r =>
      match r with
      | .done w' => Buffered w' ∧ ∃ bits, stream w' = front ++ bits ∧
          bits.length ≤ 11 * (stop - start) ∧
          Encoding.Encodes data.val start stop (bits ++ Symbols.encode 256)
      | .cont (w', p', t') =>
          TokenState data.val start stop front ls.val ds.val w' p' t' ∧
          t'.val = t.val + 1 ⦄ := by
  obtain ⟨hp, hlen, ht, hr, hb, bits, hstream, hsize, hemit⟩ := h
  have hc := hb.1
  have hw := hb.2
  have hslen := congrArg List.length hstream
  simp only [List.length_append] at hslen
  have hspace : w.out.val.length + 24 ≤ Usize.max := space w 24 (by omega)
  unfold fixed_loop.body
  dsimp only
  split
  · have hlt : t.val < ls.val.length := by scalar_tac
    obtain ⟨hstep, htail⟩ := Tokens.runs_head hr hlt hlen
    have hpos := step_positive hstep
    have hpend := runs_bound htail
    step as ⟨len16, hlenget⟩
    step as ⟨len, hlcast⟩
    step as ⟨dist16, hdistget⟩
    step as ⟨dist, hdcast⟩
    have hlget : len.val = (ls.val[t.val]!).val := by
      rw [hlcast]
      change (widen len16).val = _
      rw [widen_val, hlenget, getElem!_pos ls.val t.val hlt]
    have hdget : dist.val = (ds.val[t.val]!).val := by
      rw [hdcast]
      change (widen dist16).val = _
      rw [widen_val, hdistget, getElem!_pos ds.val t.val (by omega)]
    simp only [Step] at hstep
    rw [← hlget, ← hdget] at hstep
    rw [← hlget] at htail hpos hpend
    split
    · rename_i hz
      have hdz : dist.val = 0 := by scalar_tac
      have hlone : len.val = 1 := by
        rcases hstep with hstep | ⟨hmatch, hd⟩
        · exact hstep.1
        · omega
      have hpdata : p.val < data.val.length := by omega
      step as ⟨b, hget⟩
      step as ⟨sym, hsym⟩
      have hbget : b = data.val[p.val]! := by rw [hget, getElem!_pos data.val p.val hpdata]
      have hsymval : sym.val = data.val[p.val]!.val := by scalar_tac
      step as ⟨w', hwstream, hwcount, hwword⟩
      step as ⟨p', hp'⟩
      step as ⟨t', ht'⟩
      refine ⟨⟨⟨by omega, by omega, hp.2.2⟩, hlen, by omega, ?_,
        ⟨hwcount, hwword⟩, bits ++ Symbols.encode data.val[p.val]!.val, ?_, ?_, ?_⟩, ht'⟩
      · simpa only [hp', ht', hlone] using htail
      · change stream w' = _ at hwstream
        change stream w' = stream w ++ Symbols.encode sym.val at hwstream
        rw [hwstream, hsymval, hstream, List.append_assoc]
      · have := symbol_size data.val[p.val]!.val
        simp only [List.length_append]
        omega
      · simpa only [hp', hlone] using Tokens.emitted_literal hemit hpdata
    · rename_i hnz
      have hdz : dist.val ≠ 0 := by scalar_tac
      have hm : Matches.ValidMatch data.val p.val stop len.val dist.val := by
        rcases hstep with hstep | ⟨hm, _⟩
        · omega
        · exact hm
      rcases hm with hm | hm
      · omega
      step as ⟨w', l, d, hl, hd, hlb, hdb, hlf, hdf, hwstream, hwcount, hwword⟩
      step as ⟨p', hp'⟩
      step as ⟨t', ht'⟩
      refine ⟨⟨⟨by omega, by omega, hp.2.2⟩, hlen, by omega, ?_,
        ⟨hwcount, hwword⟩, bits ++ Copies.encode len.val dist.val l d, ?_, ?_, ?_⟩, ht'⟩
      · simpa only [hp', ht'] using htail
      · change stream w' = _ at hwstream
        change stream w' = stream w ++ Copies.encode len.val dist.val l d at hwstream
        rw [hwstream, hstream, List.append_assoc]
      · have := copy_size len.val dist.val l d hl hd
        simp only [List.length_append]
        omega
      · have hm' : 3 ≤ len.val ∧ len.val ≤ 258 ∧ p.val + len.val ≤ data.val.length ∧
            0 < dist.val ∧ dist.val ≤ p.val ∧ dist.val ≤ 32768 ∧
            Matches.EqualRun data.val p.val (p.val - dist.val) len.val := by
          exact ⟨hm.1, hm.2.1, by omega, hm.2.2.2.1, hm.2.2.2.2.1,
            hm.2.2.2.2.2.1, hm.2.2.2.2.2.2⟩
        simpa only [hp'] using Tokens.emitted_copy hemit hm' ⟨hl, hd, hlb, hdb, hlf, hdf⟩
  · have htend : t.val = ls.val.length := by scalar_tac
    have hpeq : p.val = stop := by
      rw [htend, hlen, List.drop_length, ← hlen, List.drop_length] at hr
      cases hr
      rfl
    simp only [WP.spec_ok]
    refine ⟨hb, bits, hstream, by omega, ?_⟩
    rw [hpeq] at hemit
    exact hemit stop _ (Encoding.Encodes.finish stop)

@[step] theorem token_loop (data : Aeneas.Std.Slice U8) (start stop : ℕ) (front : List Bool)
    (ls ds : alloc.vec.Vec U16) (w : Gzip.solution.Writer) (p t : Usize)
    (h : TokenState data.val start stop front ls.val ds.val w p t)
    (hbudget : front.length + 11 * (stop - start) + 192 ≤ 34359738360) :
    fixed_loop w data ls ds p t ⦃ w' =>
      Buffered w' ∧ ∃ bits, stream w' = front ++ bits ∧
        bits.length ≤ 11 * (stop - start) ∧
        Encoding.Encodes data.val start stop (bits ++ Symbols.encode 256) ⦄ := by
  unfold fixed_loop
  apply loop.spec_decr_nat (fun (_, _, t') => ls.val.length - t'.val)
    (fun (w', p', t') => TokenState data.val start stop front ls.val ds.val w' p' t')
  · rintro ⟨w', p', t'⟩ hi
    refine WP.spec_mono (token_body data start stop front ls ds w' p' t' hi hbudget) ?_
    intro r hr
    cases r with
    | done w'' => exact hr
    | cont state => exact ⟨hr.1, by have := hr.1.index; simp only at *; omega⟩
  · exact h

theorem align_stream (w : Gzip.solution.Writer) (hb : Buffered w)
    (hspace : w.out.val.length + 4 ≤ Usize.max) :
    Gzip.solution.Writer.align w ⦃ r =>
      r.count.val = 0 ∧ r.bits.val = 0 ∧
      ∃ padding, byteBits r.out.val = stream w ++ padding ∧
        padding.length < 8 ∧ 8 * r.out.val.length = (stream w).length + padding.length ⦄ := by
  refine WP.spec_mono (Writer.align w hb.1 hspace) ?_
  intro r hr
  have hfb := flush_bits w.out.val w.bits.val w.count.val
  have hfl := flush_layout w.out.val w.bits.val w.count.val
  have hfw := flush_word_bound w.out.val w.bits.val w.count.val hb.2
  simp only [aligned] at hr
  generalize hf : flush w.out.val w.bits.val w.count.val = f at hr hfb hfl hfw
  obtain ⟨out1, word1, count1⟩ := f
  dsimp only at hr hfb hfl hfw
  have hstream : stream w = byteBits out1 ++ lowBits word1 count1 := by
    rw [stream, ← hfb]
  have hcnt : count1 < 8 := by rw [hfl.2]; exact Nat.mod_lt _ (by decide)
  by_cases hc : count1 = 0
  · have hw : word1 = 0 := by rw [hc] at hfw; simp at hfw; omega
    simp only [pad, hc, if_true] at hr
    have ho := congrArg (fun x : List U8 × ℕ × ℕ => x.1) hr
    have hword := congrArg (fun x : List U8 × ℕ × ℕ => x.2.1) hr
    have hcount := congrArg (fun x : List U8 × ℕ × ℕ => x.2.2) hr
    dsimp only at ho hword hcount
    have hnil : lowBits word1 count1 = [] := List.eq_nil_of_length_eq_zero (by simp [hc])
    refine ⟨by omega, by omega, [], ?_, by simp, ?_⟩
    · rw [ho, hstream, hnil]
      simp
    · rw [ho, hstream, hnil]
      simp
  · simp only [pad, hc, if_false] at hr
    have ho := congrArg (fun x : List U8 × ℕ × ℕ => x.1) hr
    have hword := congrArg (fun x : List U8 × ℕ × ℕ => x.2.1) hr
    have hcount := congrArg (fun x : List U8 × ℕ × ℕ => x.2.2) hr
    dsimp only at ho hword hcount
    refine ⟨hcount, hword, lowBits (word1 / 2 ^ count1) (8 - count1), ?_, ?_, ?_⟩
    · rw [ho, byteBits_append, byteBits_singleton, byte_lowBits, hstream]
      rw [show 8 = count1 + (8 - count1) by omega, lowBits_split, ← List.append_assoc]
      simp only [Nat.add_sub_cancel_left]
    · simp only [lowBits_length]; omega
    · rw [ho, hstream]
      simp only [List.length_append, List.length_singleton, byteBits_length, lowBits_length]
      omega

def le16 (v : ℕ) : List U8 := [byte v, byte (v / 256)]

theorem le16_bits (v : ℕ) : byteBits (le16 v) = lowBits v 16 := by
  rw [show (16 : ℕ) = 8 + 8 from rfl, lowBits_split]
  simp [le16, byteBits]

/-- Sixteen bits into an empty accumulator stay in it. -/
theorem bits16a (w : Gzip.solution.Writer) (v : U32)
    (hc : w.count.val = 0) (hw : w.bits.val = 0) (hv : v.val < 65536)
    (hspace : w.out.val.length + 2 ≤ Usize.max) :
    Gzip.solution.Writer.impl.bits w v 16#u32 ⦃ r =>
      r.out.val = w.out.val ∧ r.count.val = 16 ∧ r.bits.val = v.val ⦄ := by
  refine WP.spec_mono (Writer.bits w v 16#u32 (by omega) (by scalar_tac) (by simp [hc]; omega)) ?_
  intro r hr
  have hv16 : (16#u32).val = 16 := by scalar_tac
  simp only [hc, hw, hv16, put, flush4, pow_zero, Nat.mul_one, Nat.zero_or, Nat.zero_add,
    show (16 : ℕ) < 32 by decide, if_true] at hr
  have hv64 : v.val < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hv64] at hr
  have ho := congrArg (fun x : List U8 × ℕ × ℕ => x.1) hr
  have hb := congrArg (fun x : List U8 × ℕ × ℕ => x.2.1) hr
  have hn := congrArg (fun x : List U8 × ℕ × ℕ => x.2.2) hr
  exact ⟨ho, hn, hb⟩

@[simp] theorem byteBits_take (s : List U8) (n : ℕ) :
    byteBits (s.take n) = (byteBits s).take (8 * n) := by
  induction s generalizing n with
  | nil => simp [byteBits]
  | cons b s ih =>
    cases n with
    | zero => simp [byteBits]
    | succ n =>
      simp only [List.take_succ_cons, byteBits_cons, ih]
      rw [show 8 * (n + 1) = (lowBits b.val 8).length + 8 * n by simp; omega,
        List.take_length_add_append]

theorem byteBits_injective : Function.Injective byteBits := by
  intro a b hab
  have hl := congrArg List.length hab
  simp only [byteBits_length] at hl
  apply List.ext_getElem (by omega)
  intro k hk hk'
  apply UScalar.eq_of_val_eq
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · have he := congrArg (fun xs : List Bool => xs[8 * k + i]!) hab
    rw [byteBits_get a _ (by omega), byteBits_get b _ (by omega)] at he
    simp only [show (8 * k + i) / 8 = k by omega,
      show (8 * k + i) % 8 = i by omega,
      getElem!_pos a k hk, getElem!_pos b k hk'] at he
    exact he
  · have ha : (a[k]).val < 256 := by scalar_tac
    have hb : (b[k]).val < 256 := by scalar_tac
    have hpow : 256 ≤ 2 ^ i := by
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 8 ≤ i by omega)
    have hia : (a[k]).val < 2 ^ i := by omega
    have hib : (b[k]).val < 2 ^ i := by omega
    rw [Nat.testBit_eq_false_of_lt hia, Nat.testBit_eq_false_of_lt hib]

theorem bytes_prefix (s out : List U8) (tail : List Bool)
    (hs : byteBits s = byteBits out ++ tail) : s.take out.length = out := by
  apply byteBits_injective
  rw [byteBits_take, hs, ← byteBits_length out, List.take_left]

/-- Sixteen more bits after sixteen: the four bytes leave, little-endian, and the accumulator
is empty again. -/
theorem bits16b (w : Gzip.solution.Writer) (v : U32)
    (hc : w.count.val = 16) (hw : w.bits.val < 65536) (hv : v.val < 65536)
    (hspace : w.out.val.length + 4 ≤ Usize.max) :
    Gzip.solution.Writer.impl.bits w v 16#u32 ⦃ r =>
      r.out.val = w.out.val ++ le16 w.bits.val ++ le16 v.val ∧ r.count.val = 0 ∧ r.bits.val = 0 ⦄ := by
  have hw' : w.bits.val < 2 ^ w.count.val := by rw [hc]; exact hw
  have hv16 : (16#u32).val = 16 := by scalar_tac
  refine WP.spec_mono (Writer.bits w v 16#u32 (by omega) (by scalar_tac) (by simp [hc]; omega)) ?_
  intro r hr
  have ho := congrArg (fun p : List U8 × ℕ × ℕ => p.1) hr
  have hword := congrArg (fun p : List U8 × ℕ × ℕ => p.2.1) hr
  have hcount := congrArg (fun p : List U8 × ℕ × ℕ => p.2.2) hr
  simp only at ho hword hcount
  have hc0 : r.count.val = 0 := by
    rw [hcount, put, hv16, hc]
    simp [flush4]
  have hbits0 : r.bits.val = 0 := by
    have hb := put_word_bound w.out.val w.bits.val w.count.val v.val (16#u32).val hw' (by rw [hv16]; omega)
    rw [← hword, ← hcount, hc0] at hb
    omega
  have hpb := put_bits w.out.val w.bits.val w.count.val v.val (16#u32).val hw' (by omega)
  rw [← ho, ← hword, ← hcount, hc0, hbits0, hv16, hc] at hpb
  have hnil : lowBits 0 0 = [] := List.eq_nil_of_length_eq_zero (by simp)
  rw [hnil, List.append_nil] at hpb
  have hbb : byteBits r.out.val = byteBits (w.out.val ++ le16 w.bits.val ++ le16 v.val) := by
    rw [byteBits_append, byteBits_append, le16_bits, le16_bits, hpb]
  exact ⟨byteBits_injective hbb, hc0, hbits0⟩

end Gzip.Proofs.Runtime
