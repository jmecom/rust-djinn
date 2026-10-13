import Gzip.Proofs.Decode.FastSymbol
import Gzip.Proofs.Decode.MatchImpl
import Gzip.Proofs.Decode.WideFacts
import Gzip.Proofs.Decode.WindowImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.BaseImpl Gzip.Proofs.Decode.TablesImpl
open Gzip.Proofs.Decode.CodewordTable Gzip.Proofs.Decode.DecodeTable Gzip.Proofs.Decode.PeekFacts
open Gzip.Proofs.Decode.WideFacts Gzip.Proofs.Decode.MatchImpl Gzip.Proofs.Decode.WindowFacts Gzip.Proofs.Decode.WindowImpl

namespace Gzip.Proofs.Decode.TokenImpl

/-- A table entry that names a symbol (in its bits 6..15) is the symbol at the window's
position, and its other fields are the symbol's. -/
theorem symbol_of_window (s lens : List U8) (codes table : List U32) (isd : Bool) (bits size : Nat)
    (i : ℤ) (p : Nat) (htable : Entries lens codes) (hlen : codes.length = lens.length)
    (ht : Hints lens codes table isd bits) (hbits : bits ≤ 11) (hsize : size = 2 ^ bits)
    (hbitsp : ∀ k : Nat, k < 11 → bit_spec s (i + k) ((p / 2 ^ k % 2 : Nat) : ℤ))
    (hsym : (table[p % size]!).val / 64 % 512 < lens.length) :
    symbol_spec s i lens (((table[p % size]!).val / 64 % 512 : Nat) : ℤ) ∧
      1 ≤ (lens[(table[p % size]!).val / 64 % 512]!).val ∧
      (lens[(table[p % size]!).val / 64 % 512]!).val ≤ bits ∧
      EntryOf isd ((table[p % size]!).val / 64 % 512) (lens[(table[p % size]!).val / 64 % 512]!).val
        (table[p % size]!).val := by
  have hpb : 2 ^ bits ≤ 2048 := calc
    _ ≤ 2 ^ 11 := Nat.pow_le_pow_right (by omega) hbits
    _ = _ := by norm_num
  have hidx : p % size < 2 ^ bits := by
    rw [hsize]
    exact Nat.mod_lt _ (by positivity)
  obtain ⟨h1, h11, hrev, hent⟩ := ht.2.1 (p % size) hidx hsym
  generalize hsy : (table[p % size]!).val / 64 % 512 = sy at *
  have hcode := code_of_bits s i p (lens[sy]!).val (fun k hk => hbitsp k (by omega))
  have hr : rev p (lens[sy]!).val = (codes[sy]!).val := by
    have hm := rev_mod p bits (lens[sy]!).val h11
    rw [← hrev, hsize, hm]
  refine ⟨⟨trivial, ⟨by omega, by omega⟩, ?_, (codes[sy]!).val, htable sy (by omega), ?_⟩,
    h1, h11, hent⟩
  · simp only [Int.toNat_natCast]
    omega
  · simp only [Int.toNat_natCast, ← hr]
    exact hcode

/-- The fields of a literal/length table entry of a literal: it takes its codeword's bits, which
are both its low five and its low six bits, and its symbol is in bits 6..14. -/
theorem literal_fields (sym n e : Nat) (h : EntryOf false sym n e) (hlt : sym < 256) (hn : n < 32) :
    e % 32 = n ∧ e % 64 = n ∧ e / 64 % 256 = sym := by
  obtain ⟨hs, extra, ht, _, hz, _, _⟩ := h
  have hz0 := hz rfl hlt
  omega

/-- The fields of a literal/length table entry of a length symbol: its base is in bits 15..24
and its codeword length in bits 24..28. -/
theorem length_fields (sym n e : Nat) (h : EntryOf false sym n e) (h257 : 257 ≤ sym)
    (h285 : sym ≤ 285) (hn : n < 16) :
    lextra_spec ((sym : ℤ) - 257) ((e % 32 - n : Nat) : ℤ) ∧ e % 32 - n ≤ 5 ∧ n ≤ e % 32 ∧
      e % 64 = e % 32 ∧
      lbase_spec ((sym : ℤ) - 257) ((e / 32768 % 512 : Nat) : ℤ) ∧ 3 ≤ e / 32768 % 512 ∧
      e / 32768 % 512 ≤ 258 ∧ e / 16777216 = n := by
  obtain ⟨_, extra, ht, hx, _, hlen, _⟩ := h
  simp only [ExtraBase, EntryBase, Bool.false_eq_true, if_false] at hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx.1 h257 h285
  have he : e % 32 - n = extra := by omega
  rw [he]
  exact ⟨h1, h2, by omega, by omega, h3, h4, h5, hlen rfl h257 h285⟩

/-- The fields of a distance table entry of a distance symbol. -/
theorem distance_fields (sym n e : Nat) (h : EntryOf true sym n e) (h29 : sym ≤ 29) (hn : n < 16) :
    dextra_spec sym ((e % 32 - n : Nat) : ℤ) ∧ e % 32 - n ≤ 13 ∧ n ≤ e % 32 ∧
      e % 64 = e % 32 ∧
      dbase_spec sym ((e / 32768 : Nat) : ℤ) ∧ 1 ≤ e / 32768 ∧ e / 32768 ≤ 24577 := by
  obtain ⟨_, extra, ht, hx, _⟩ := h
  simp only [ExtraBase, EntryBase, if_true] at hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx.1 h29
  have he : e % 32 - n = extra := by omega
  rw [he]
  exact ⟨h1, h2, by omega, by omega, h3, h4, h5⟩

/-- A literal/length entry with a bit at or above 15 names a length code. -/
theorem length_of_base (sym n e : Nat) (h : EntryOf false sym n e) (hb : 32768 ≤ e) :
    257 ≤ sym ∧ sym ≤ 285 := by
  obtain ⟨_, extra, _, _, _, _, hlow⟩ := h
  by_contra hc
  have h0 := hlow rfl (by omega)
  omega

/-- A distance entry with a nonzero base names a distance code. -/
theorem distance_of_base (sym n e : Nat) (h : EntryOf true sym n e) (hb : 32768 ≤ e) :
    sym ≤ 29 := by
  obtain ⟨_, extra, _, hx, _⟩ := h
  simp only [ExtraBase, EntryBase, if_true] at hx
  by_contra hc
  have h0 := hx.2 (by omega)
  omega

/-- An entry whose bit 14 is clear names a literal. -/
theorem literal_of_bit (sym n e : Nat) (h : EntryOf false sym n e) (hb : e % 32768 < 16384) :
    sym < 256 := by
  obtain ⟨hs, _⟩ := h
  omega

/-- The bits `n..t` of `p`: `p >> n` less `p >> t` shifted back, which is also the remainder. -/
theorem extra_sub (p n t : Nat) (hnt : n ≤ t) :
    (p / 2 ^ t) * 2 ^ (t - n) ≤ p / 2 ^ n ∧
    p / 2 ^ n - (p / 2 ^ t) * 2 ^ (t - n) = (p / 2 ^ n) % 2 ^ (t - n) := by
  have ht : 2 ^ t = 2 ^ n * 2 ^ (t - n) := by
    rw [← pow_add]; congr 1; omega
  have hq : p / 2 ^ t = (p / 2 ^ n) / 2 ^ (t - n) := by
    rw [ht, Nat.div_div_eq_div_mul]
  rw [hq]
  have hle := Nat.div_mul_le_self (p / 2 ^ n) (2 ^ (t - n))
  constructor
  · exact hle
  · have := @Nat.mod_eq_sub_mul_div (p / 2 ^ n) (2 ^ (t - n))
    rw [this, Nat.mul_comm]

/-- The bits `n..t` of `p` as the remainder of `p` below `t` shifted down by `n`: the same bits as
`extra_sub`, which the decoder now takes with one shift of the window's remaining bits. -/
theorem extra_mod (p n t : Nat) (hnt : n ≤ t) :
    (p / 2 ^ t) * 2 ^ t ≤ p ∧
    (p - (p / 2 ^ t) * 2 ^ t) / 2 ^ n = (p / 2 ^ n) % 2 ^ (t - n) := by
  constructor
  · exact Nat.div_mul_le_self p (2 ^ t)
  · have hm : p - (p / 2 ^ t) * 2 ^ t = p % 2 ^ t := by
      have := @Nat.mod_eq_sub_mul_div p (2 ^ t)
      rw [this, Nat.mul_comm]
    rw [hm, ← Nat.mod_mul_right_div_self, ← pow_add, Nat.add_sub_cancel' hnt]

/-- What `peek_token` returns: nothing (kind 0), a literal with the bits of its codeword (at most
eleven), or a whole copy with the bits of its two codewords and their extra bits (at most 40),
and in both cases the window after the token; a token only when the window holds at least `lo`
bits, and a copy only when the output position is within the limit. -/
def TokenPost (s : Aeneas.Std.Slice U8) (P : ℤ) (p : U64) (nbits lo : U32) (lit dist : Aeneas.Std.Slice U8)
    (n_out limit : Usize) (z : U32 × U32 × U32 × U32 × U64) : Prop :=
  (z.1.val = 1 → lo.val ≤ nbits.val ∧ z.2.2.2.1.val ≤ 11 ∧
    z.2.1.val < 256 ∧ symbol_spec s.val P lit.val z.2.1.val ∧
    z.2.2.2.1.val = (lit.val[z.2.1.val]!).val ∧ z.2.2.2.2.val = p.val >>> z.2.2.2.1.val) ∧
  (z.1.val = 2 → lo.val ≤ nbits.val ∧ z.2.2.2.1.val ≤ 40 ∧ n_out.val ≤ limit.val ∧
    3 ≤ z.2.1.val ∧ z.2.1.val ≤ 289 ∧ 1 ≤ z.2.2.1.val ∧ z.2.2.2.2.val = p.val >>> z.2.2.2.1.val ∧
    ∃ sym : Nat, 257 ≤ sym ∧ sym ≤ 285 ∧ symbol_spec s.val P lit.val sym ∧
      (lit.val[sym]!).val < z.2.2.2.1.val ∧
      MatchSpec s.val (P + (lit.val[sym]!).val) dist.val ((sym : ℤ) - 257)
        z.2.1.val z.2.2.1.val (P + z.2.2.2.1.val))

theorem token_none (s : Aeneas.Std.Slice U8) (P : ℤ) (p : U64) (nbits lo : U32) (lit dist : Aeneas.Std.Slice U8)
    (n_out limit : Usize) :
    TokenPost s P p nbits lo lit dist n_out limit (0#u32, 0#u32, 0#u32, 0#u32, 0#u64) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp at h

theorem pow_sub_le (a b : Nat) (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

-- `peek_copy`, given the length symbol `sym` of the entry `e` at the window's position, whose
-- codeword length is in bits 24..28 of `e`. The distance code's codeword length comes from
-- `distq`, indexed like the distance table; the distance entry has a nonzero base, so it is
-- not the sentinel and names a distance code of the distance table.
set_option maxHeartbeats 12000000 in
theorem peek_copy_correct (s : Aeneas.Std.Slice U8) (P : ℤ) (nbits lo : U32) (p q2 : U64) (e : U32)
    (lit dist : Aeneas.Std.Slice U8) (dist_codes : Aeneas.Std.Slice U32) (dist_table : Array U32 2048#usize)
    (distq : Array U8 1024#usize) (n_out limit : Usize)
    (hdq : DistQ dist.val dist_table.val distq.val)
    (hdtl : Hints dist.val dist_codes.val dist_table.val true 10)
    (hdl : dist_codes.val.length = dist.val.length) (hdt : Entries dist.val dist_codes.val)
    (h56 : lo.val ≤ nbits.val)
    (hbits : ∀ k : Nat, k < 45 → bit_spec s.val (P + k) ((p.val / 2 ^ k % 2 : Nat) : ℤ))
    (hq2s : q2.val = p.val >>> (e.val % 64))
    (sym : Nat) (hs257 : 257 ≤ sym) (hs285 : sym ≤ 285) (hsl : sym < lit.val.length)
    (hsym : symbol_spec s.val P lit.val sym) (hn11 : (lit.val[sym]!).val ≤ 11)
    (hent : EntryOf false sym (lit.val[sym]!).val e.val) :
    peek_copy p q2 e distq dist_table n_out limit ⦃ z =>
      TokenPost s P p nbits lo lit dist n_out limit z ⦄ := by
  have hdtl1 := hdtl.1
  obtain ⟨hle, hle5, hnt, h64, hlb, hlb3, hlb258, hlen⟩ :=
    length_fields sym _ e.val hent hs257 hs285 (by omega)
  clear hent
  unfold peek_copy
  -- the length symbol's codeword length, from the entry
  step as ⟨n, n_post⟩
  have hn : n.val = (lit.val[sym]!).val := by rw [n_post, hlen]
  clear n_post
  -- the window after the length symbol's codeword and extra bits, which the caller computed
  step as ⟨t, t_post⟩
  have ht : t.val = e.val % 32 := t_post
  rw [← hn, ← ht] at hle hle5 hnt
  have hq2 : q2.val = p.val / 2 ^ t.val := by rw [hq2s, Nat.shiftRight_eq_div_pow, h64, ht]
  step as ⟨i1, i1_post⟩
  step as ⟨i2, i2_post⟩
  have hi2 : i2.val = q2.val % 1024 := by
    rw [i2_post, UScalar.cast_val_eq, i1_post]
    apply Nat.mod_eq_of_lt
    scalar_tac
  clear i2_post
  -- the distance entry
  step as ⟨e2, e2_post⟩
  all_goals try scalar_tac
  have hd : e2 = dist_table.val[q2.val % 1024]! := by
    rw [← hi2, getElem!_pos dist_table.val i2.val (by omega)]; exact e2_post
  split
  swap
  · rw [WP.spec_ok]; exact token_none s P p nbits lo lit dist n_out limit
  split
  swap
  · rw [WP.spec_ok]; exact token_none s P p nbits lo lit dist n_out limit
  -- not the sentinel (whose base is zero), so an entry of a symbol of the distance table
  have hne : dist_table.val[q2.val % 1024]! ≠ 20480#u32 := by
    rw [← hd]
    intro h
    have h20 : e2.val = 20480 := by rw [h]; simp
    scalar_tac
  -- the distance symbol of the entry
  obtain ⟨dc, hdcv⟩ : ∃ dc : Nat, dc = (dist_table.val[q2.val % 1024]!).val / 64 % 512 := ⟨_, rfl⟩
  have hq1024 : q2.val % 1024 < 2 ^ 10 :=
    Nat.lt_of_lt_of_eq (Nat.mod_lt _ (by norm_num)) (by norm_num)
  have hdcl : dc < dist.val.length := by
    rw [hdcv]
    exact named_of_ne dist.val dist_codes.val dist_table.val true 10 hdtl (q2.val % 1024) hq1024 hne
  have hbq2 : ∀ k : Nat, k < 29 →
      bit_spec s.val (P + t.val + k) ((q2.val / 2 ^ k % 2 : Nat) : ℤ) := by
    rw [hq2]
    exact window_shift s.val P p.val t.val 29 (fun k hk => hbits k (by omega))
  have hwd := symbol_of_window s.val dist.val dist_codes.val dist_table.val true 10 1024
    (P + t.val) q2.val hdt hdl hdtl (by norm_num) (by norm_num)
    (fun k hk => hbq2 k (by omega)) (by rw [← hdcv]; exact hdcl)
  rw [← hdcv, ← hd] at hwd
  obtain ⟨hdsym, hdn1, hdn11, hdent⟩ := hwd
  have hdc29 : dc ≤ 29 := distance_of_base _ _ _ hdent (by scalar_tac)
  obtain ⟨hde, hde13, hdnt, hd64, hdb, hdb1, hdb24577⟩ :=
    distance_fields dc _ e2.val hdent hdc29 (by omega)
  clear hdent
  -- the distance code's codeword length, from distq at the same index
  step as ⟨i3, i3_post⟩
  have hi3 : i3.val = q2.val % 1024 := by
    rw [i3_post, UScalar.cast_val_eq, i1_post]
    apply Nat.mod_eq_of_lt
    scalar_tac
  clear i3_post
  step as ⟨i4, i4_post⟩
  all_goals try scalar_tac
  have hi4 : i4 = dist.val[dc]! := by
    rw [hdcv, ← hdq (q2.val % 1024) (Nat.mod_lt _ (by norm_num)) (by rw [← hdcv]; exact hdcl),
      ← hi3, getElem!_pos distq.val i3.val (by scalar_tac)]
    exact i4_post
  step as ⟨dn, dn_post⟩
  have hdn : dn.val = (dist.val[dc]!).val := by
    rw [dn_post, cast_byte, hi4]
  clear hi4 i4_post
  step as ⟨t2, t2_post⟩
  have ht2 : t2.val = e2.val % 32 := t2_post
  rw [← hdn, ← ht2] at hde hde13 hdnt
  step as ⟨i7, i7_post⟩
  have hi7 : i7.val = t2.val := by rw [i7_post, ht2]; exact hd64
  step as ⟨rest, rest_post⟩
  all_goals try scalar_tac
  have hrest : rest.val = q2.val / 2 ^ t2.val := by
    rw [rest_post, Nat.shiftRight_eq_div_pow, hi7]
  -- the length: base plus the extra bits n..t of p, the remainder of p below t shifted down
  step as ⟨i8, i8_post⟩
  step as ⟨i9, i9_post⟩
  have h9 : i9.val = e.val / 32768 % 512 := by rw [i9_post, i8_post]
  rw [← h9] at hlb hlb3 hlb258
  have hsub := extra_mod p.val n.val t.val hnt
  step as ⟨i10, i10_post⟩
  all_goals try scalar_tac
  have h10 : i10.val = (p.val / 2 ^ t.val) * 2 ^ t.val := by
    rw [i10_post, Nat.shiftLeft_eq, hq2, u64_size]
    apply Nat.mod_eq_of_lt
    have := hsub.1
    scalar_tac
  have h10le : i10.val ≤ p.val := by rw [h10]; exact hsub.1
  step as ⟨i11, i11_post⟩
  all_goals try scalar_tac
  have h11 : i11.val = p.val - (p.val / 2 ^ t.val) * 2 ^ t.val := by rw [i11_post, h10]
  step as ⟨i12, i12_post⟩
  all_goals try scalar_tac
  have h12 : i12.val = (p.val / 2 ^ n.val) % 2 ^ (t.val - n.val) := by
    rw [i12_post, Nat.shiftRight_eq_div_pow, h11]; exact hsub.2
  have hlt12 : i12.val < 2 ^ (t.val - n.val) := by rw [h12]; exact Nat.mod_lt _ (by positivity)
  have hple : 2 ^ (t.val - n.val) ≤ 2 ^ 5 := pow_sub_le _ _ hle5
  step as ⟨i13, i13_post⟩
  have h13 : i13.val = i12.val := by
    rw [i13_post, UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  step as ⟨len, len_post⟩
  all_goals try scalar_tac
  -- the distance: base plus the extra bits dn..t2 of q2, the same way
  step as ⟨i14, i14_post⟩
  have h14 : i14.val = e2.val / 32768 := i14_post
  rw [← h14] at hdb hdb1 hdb24577
  have hsub2 := extra_mod q2.val dn.val t2.val hdnt
  step as ⟨i15, i15_post⟩
  all_goals try scalar_tac
  have h15 : i15.val = (q2.val / 2 ^ t2.val) * 2 ^ t2.val := by
    rw [i15_post, Nat.shiftLeft_eq, hrest, u64_size]
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt hsub2.1 (by scalar_tac)
  have h15le : i15.val ≤ q2.val := by rw [h15]; exact hsub2.1
  step as ⟨i16, i16_post⟩
  all_goals try scalar_tac
  have h16 : i16.val = q2.val - (q2.val / 2 ^ t2.val) * 2 ^ t2.val := by rw [i16_post, h15]
  step as ⟨i17, i17_post⟩
  all_goals try scalar_tac
  have h17 : i17.val = (q2.val / 2 ^ dn.val) % 2 ^ (t2.val - dn.val) := by
    rw [i17_post, Nat.shiftRight_eq_div_pow, h16]; exact hsub2.2
  have hlt17 : i17.val < 2 ^ (t2.val - dn.val) := by rw [h17]; exact Nat.mod_lt _ (by positivity)
  have hpde : 2 ^ (t2.val - dn.val) ≤ 2 ^ 13 := pow_sub_le _ _ hde13
  step as ⟨i18, i18_post⟩
  have h18 : i18.val = i17.val := by
    rw [i18_post, UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  step as ⟨d, d_post⟩
  all_goals try scalar_tac
  step as ⟨i19, i19_post⟩
  all_goals try scalar_tac
  -- the token
  have hbq : ∀ k : Nat, k < t.val - n.val →
      bit_spec s.val (P + n.val + k) ((p.val / 2 ^ n.val / 2 ^ k % 2 : Nat) : ℤ) :=
    window_shift s.val P p.val n.val (t.val - n.val) (fun k hk => hbits k (by omega))
  have hbq3 : ∀ k : Nat, k < t2.val - dn.val →
      bit_spec s.val (P + t.val + dn.val + k) ((q2.val / 2 ^ dn.val / 2 ^ k % 2 : Nat) : ℤ) :=
    window_shift s.val (P + t.val) q2.val dn.val (t2.val - dn.val)
      (fun k hk => hbq2 k (by omega))
  have hf1 := field_of_bits s.val (t.val - n.val) (P + n.val) (p.val / 2 ^ n.val) hbq
  rw [← h12] at hf1
  have hf2 := field_of_bits s.val (t2.val - dn.val) (P + t.val + dn.val) (q2.val / 2 ^ dn.val) hbq3
  rw [← h17] at hf2
  have h25 : i19.val = t.val + t2.val := i19_post
  have hrest2 : rest.val = p.val >>> i19.val := by
    rw [hrest, hq2, h25, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h32 : (2 : Nat) ^ 5 = 32 := by norm_num
  refine ⟨fun h => by simp at h, fun _ => ⟨h56, ?_, by scalar_tac, ?_, ?_, ?_, hrest2, sym,
    hs257, hs285, hsym, ?_, ?_⟩⟩
  · show i19.val ≤ 40
    omega
  · show 3 ≤ len.val
    omega
  · show len.val ≤ 289
    omega
  · show 1 ≤ d.val
    omega
  · show (lit.val[sym]!).val < i19.val
    omega
  · show MatchSpec s.val (P + (lit.val[sym]!).val) dist.val ((sym : ℤ) - 257)
      len.val d.val (P + i19.val)
    rw [← hn]
    refine ⟨P + t.val, dc, ?_, ?_, hdsym, ?_, ?_⟩
    · exact ⟨i9.val, hlb, ((t.val - n.val : Nat) : ℤ), hle, i12.val, hf1, by omega⟩
    · exact ⟨((t.val - n.val : Nat) : ℤ), hle, by omega⟩
    · refine ⟨i14.val, hdb, ((t2.val - dn.val : Nat) : ℤ), hde, i17.val, ?_, by omega⟩
      simp only [Int.toNat_natCast, ← hdn]
      exact hf2
    · refine ⟨((t2.val - dn.val : Nat) : ℤ), hde, ?_⟩
      simp only [Int.toNat_natCast, ← hdn]
      omega

-- `e` is the entry at the window's position whenever the window holds `lo` bits (the decoding
-- loop's invariant); it is not the sentinel in either branch (bit 14 of the sentinel is set and
-- its base is zero), so it names a symbol of the table by `Named`.
set_option maxHeartbeats 12000000 in
theorem peek_token_correct (s : Aeneas.Std.Slice U8) (P : ℤ) (p q : U64) (nbits lo e : U32)
    (lit dist : Aeneas.Std.Slice U8) (lit_codes dist_codes : Aeneas.Std.Slice U32)
    (table dist_table : Array U32 2048#usize) (distq : Array U8 1024#usize)
    (n_out limit : Usize)
    (hdq : DistQ dist.val dist_table.val distq.val)
    (ht : Hints lit.val lit_codes.val table.val false 11)
    (hdtl : Hints dist.val dist_codes.val dist_table.val true 10)
    (hll : lit_codes.val.length = lit.val.length) (hdl : dist_codes.val.length = dist.val.length)
    (hlt : Entries lit.val lit_codes.val) (hdt : Entries dist.val dist_codes.val)
    (hlo : 45 ≤ lo.val)
    (hbw : ∀ k : Nat, k < 64 → k < nbits.val → bit_spec s.val (P + k) ((p.val / 2 ^ k % 2 : Nat) : ℤ))
    (he : lo.val ≤ nbits.val → e = table.val[p.val % 2048]!)
    (hq : q.val = p.val >>> (e.val % 64)) :
    peek_token p q nbits lo e distq dist_table n_out limit ⦃ z =>
      TokenPost s P p nbits lo lit dist n_out limit z ⦄ := by
  have htl := ht.1
  unfold peek_token
  step*
  all_goals try exact token_none s P p nbits lo lit dist n_out limit
  all_goals
    have h56 : lo.val ≤ nbits.val := by scalar_tac
    have hbits : ∀ k : Nat, k < 45 → bit_spec s.val (P + k) ((p.val / 2 ^ k % 2 : Nat) : ℤ) :=
      fun k hk => hbw k (by omega) (by omega)
    have hev := he h56
    have hne : table.val[p.val % 2048]! ≠ 20480#u32 := by
      rw [← hev]
      intro h
      have h20 : e.val = 20480 := by rw [h]; simp
      scalar_tac
    have hsl : (table.val[p.val % 2048]!).val / 64 % 512 < lit.val.length :=
      named_of_ne lit.val lit_codes.val table.val false 11 ht (p.val % 2048)
        (Nat.lt_of_lt_of_eq (Nat.mod_lt _ (by norm_num)) (by norm_num)) hne
    have hw := symbol_of_window s.val lit.val lit_codes.val table.val false 11 2048 P p.val hlt hll
      ht (by norm_num) (by norm_num) (fun k hk => hbits k (by omega)) hsl
    rw [← hev] at hw hsl
    obtain ⟨hsym, hn1, hn11, hent⟩ := hw
  · -- a literal
    have hlit : e.val / 64 % 512 < 256 := literal_of_bit _ _ _ hent (by scalar_tac)
    obtain ⟨h32, h64, h256⟩ := literal_fields _ _ e.val hent hlit (by omega)
    have hi2 : i2.val = e.val / 64 % 512 := by
      rw [i2_post, i1_post]
      omega
    refine ⟨fun _ => ⟨h56, ?_, ?_, ?_, ?_, ?_⟩, fun h => by simp at h⟩
    · show i3.val ≤ 11
      omega
    · show i2.val < 256
      omega
    · rw [hi2]
      exact hsym
    · show i3.val = (lit.val[i2.val]!).val
      rw [hi2, i3_post]
      exact h32
    · show q.val = p.val >>> i3.val
      rw [hq, i3_post, h64, h32]
  · -- a copy
    obtain ⟨hs257, hs285⟩ := length_of_base _ _ _ hent (by scalar_tac)
    exact peek_copy_correct s P nbits lo p q e lit dist dist_codes dist_table distq n_out limit
      hdq hdtl hdl hdt h56 hbits hq _ hs257 hs285 hsl hsym hn11 hent

end Gzip.Proofs.Decode.TokenImpl
