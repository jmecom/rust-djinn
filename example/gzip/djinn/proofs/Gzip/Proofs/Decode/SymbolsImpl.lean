import Gzip.Proofs.Decode.SymbolsFacts
import Gzip.Proofs.Decode.FastSymbol
import Gzip.Proofs.Decode.LongHints
import Gzip.Proofs.Decode.TokenImpl
import Gzip.Proofs.Decode.StoredImpl
import Gzip.Proofs.Decode.EntryInv

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.SymbolImpl Gzip.Proofs.Decode.MatchImpl
open Gzip.Proofs.Decode.CopyImpl Gzip.Proofs.Decode.StoredImpl Gzip.Proofs.Decode.SymbolsFacts
open Gzip.Proofs.Decode.LongHints
open Gzip.Proofs.Decode.CodewordTable Gzip.Proofs.Decode.FastSymbol Gzip.Proofs.Decode.DecodeTable
open Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.RoundTrip Gzip.Proofs.Decode.TokenImpl
open Gzip.Proofs.Decode.WindowFacts Gzip.Proofs.Decode.WindowImpl Gzip.Proofs.Decode.EntryInv

namespace Gzip.Proofs.Decode.SymbolsImpl

theorem inv_pos_bound (s : Aeneas.Std.Slice U8) (r : Reader) (h : Inv s r) :
    0 ≤ pos r ∧ pos r ≤ 8 * s.val.length := by
  unfold ReaderImpl.Inv pos at *
  omega

/-- The loop's state: the window is in bounds, the entry it carries is the one at the window's
position (`EInv`), the buffer keeps its length, and the block's relation from the start is the
relation from the window's position on the prefix written so far. The reader in the state is
scratch. -/
def SymInv (s lit dist : Aeneas.Std.Slice U8) (table : Array U32 2048#usize)
    (R : List U8 → ℤ → Prop) (len0 : Nat)
    (st : Reader × alloc.vec.Vec U8 × Usize × U64 × U32 × Usize × U32) : Prop :=
  WInv s st.2.2.2.1 st.2.2.2.2.1 st.2.2.2.2.2.1 ∧
  EInv s table st.2.2.2.1 st.2.2.2.2.1 st.2.2.2.2.2.1 st.2.2.2.2.2.2 ∧
  st.2.2.1.val ≤ st.2.1.val.length ∧
  st.2.1.val.length = len0 ∧
  ∀ v j, R v j ↔ symbols_spec s.val (wpos st.2.2.2.2.2.1 st.2.2.2.2.1) lit.val dist.val
    (st.2.1.val.take st.2.2.1.val) v j

/-- The window after a token of `bits` bits. -/
theorem winv_skip (s : Aeneas.Std.Slice U8) (w buf1 : U64) (nb nbits1 bits : U32) (c : Usize)
    (h : WInv s w nb c) (hb : buf1.val = w.val >>> bits.val) (hn : nbits1.val = nb.val - bits.val)
    (hle : bits.val ≤ nb.val) :
    WInv s buf1 nbits1 c ∧ wpos c nbits1 = wpos c nb + bits.val := by
  obtain ⟨hc, hn63, hnc, hw⟩ := h
  have hpos : wpos c nbits1 = wpos c nb + bits.val := by unfold wpos; omega
  refine ⟨⟨hc, by omega, by omega, ?_⟩, hpos⟩
  rw [hb, hn, hpos]
  exact window_skip s.val w.val nb.val bits.val (wpos c nb) hw (by scalar_tac) (by omega) hle

/-- The loop's state and measure after fast tokens of `k > 0` bits in all, from `advance`. -/
theorem syminv_cont (s lit dist : Aeneas.Std.Slice U8) (table : Array U32 2048#usize)
    (R : List U8 → ℤ → Prop) (len0 : Nat) (r : Reader) (out1 : alloc.vec.Vec U8) (n1 : Usize)
    (nbits : U32) (cpos : Usize) (w : U64) (nb : U32) (c : Usize) (e1 : U32) (k : Nat) (hk : 0 < k)
    (hwin3 : WInv s w nb c) (hpos3 : wpos c nb = wpos cpos nbits + k)
    (heinv3 : EInv s table w nb c e1)
    (hn1 : n1.val ≤ out1.val.length) (hlen1 : out1.val.length = len0)
    (hiff1 : ∀ v j, R v j ↔ symbols_spec s.val (wpos cpos nbits + k) lit.val dist.val
      (out1.val.take n1.val) v j) :
    SymInv s lit dist table R len0 (r, out1, n1, w, nb, c, e1) ∧
      (8 * (s.val.length : ℤ) - wpos c nb).toNat < (8 * (s.val.length : ℤ) - wpos cpos nbits).toNat := by
  have hend := (winv_pos_bound s w nb c hwin3).2
  refine ⟨⟨hwin3, heinv3, hn1, hlen1, fun v j => by rw [hpos3]; exact hiff1 v j⟩, ?_⟩
  apply bit_measure_decreases
  · rw [hpos3]; omega
  · exact hend

set_option maxHeartbeats 40000000 in
theorem decode_symbols_body (s : Aeneas.Std.Slice U8) (lit dist : Aeneas.Std.Slice U8)
    (lit_codes dist_codes : Aeneas.Std.Slice U32) (table dist_table : Array U32 2048#usize)
    (distq : Array U8 1024#usize) (hints : Array U16 512#usize) (limit : Usize)
    (R : List U8 → ℤ → Prop) (cap len0 : Nat) (r : Reader) (out : alloc.vec.Vec U8) (n : Usize)
    (buf : U64) (nbits : U32) (cpos : Usize) (e : U32)
    (hdq : DistQ dist.val dist_table.val distq.val)
    (ht : Hints lit.val lit_codes.val table.val false 11) (hdtl : Hints dist.val dist_codes.val dist_table.val true 10)
    (hll : lit_codes.val.length = lit.val.length) (hdl : dist_codes.val.length = dist.val.length)
    (hlt : Entries lit.val lit_codes.val) (hdt : Entries dist.val dist_codes.val)
    (hl : lit.val.length ≤ 320) (hd : dist.val.length ≤ 320)
    (hbl : ∀ j, j < lit.val.length → (lit.val[j]!).val ≤ 15)
    (hbd : ∀ j, j < dist.val.length → (dist.val[j]!).val ≤ 15)
    (hcap : cap + 24 ≤ len0)
    -- positions up to the limit have room for any copy (at most 289 bytes) and the chunk slack
    (hlim : limit.val + 320 ≤ len0 ∨ (limit.val = 0 ∧ len0 < 320))
    (h : SymInv s lit dist table R len0 (r, out, n, buf, nbits, cpos, e)) :
    decode_symbols_cached_loop.body s lit dist lit_codes dist_codes table dist_table distq
      hints limit r out n buf nbits cpos e ⦃ z =>
      match z with
      | .done res => ParsePost s cap len0 R res
      | .cont st => SymInv s lit dist table R len0 st ∧
          (8 * (s.val.length : ℤ) - wpos st.2.2.2.2.2.1 st.2.2.2.2.1).toNat <
            (8 * (s.val.length : ℤ) - wpos cpos nbits).toNat ⦄ := by
  obtain ⟨hwin, heinv, hn, hlen, hiff⟩ := h
  simp only at hwin heinv hn hlen hiff
  have hprev : (out.val.take n.val).length = n.val := List.length_take_of_le hn
  have hol := alloc.vec.Vec.len_val out
  have htl := ht.1
  have hc1 : cpos.val ≤ s.val.length := hwin.1
  have hn1 : nbits.val ≤ 63 := hwin.2.1
  have hnc1 : nbits.val ≤ 8 * cpos.val := hwin.2.2.1
  have hend0 := (winv_pos_bound s buf nbits cpos hwin).2
  have hbw : ∀ k : Nat, k < 64 → k < nbits.val →
      bit_spec s.val (wpos cpos nbits + k) ((buf.val / 2 ^ k % 2 : Nat) : ℤ) :=
    window_bits _ _ _ _ hwin.2.2.2
  have he : (56#u32).val ≤ nbits.val → e = table.val[buf.val % 2048]! :=
    einv_entry s table buf nbits cpos e heinv 56#u32 (by simp)
  -- the distance table's mask on the slow path
  have hmask10 : (1023#u32).val = 2 ^ 10 - 1 := by simp
  have hb10 : (10 : Nat) ≤ 11 := by norm_num
  unfold decode_symbols_cached_loop.body
  -- the window past the entry's bits, before the token's kind is known
  step as ⟨j0, hj0⟩
  step as ⟨q, hq⟩
  all_goals try scalar_tac
  have hq' : q.val = buf.val >>> (e.val % 64) := by rw [hq, hj0]
  have htok := peek_token_correct s (wpos cpos nbits) buf q nbits 56#u32 e lit dist lit_codes dist_codes
    table dist_table distq n limit hdq ht hdtl hll hdl hlt hdt (by simp) hbw he hq'
  step with htok as ⟨kind, a, b, bits, rest, htp⟩
  simp only [TokenPost] at htp
  split
  · -- a whole copy from the window
    have hk : kind.val = 2 := by scalar_tac
    obtain ⟨h56, hb40, hnlim, hlen3, hlen289, hd1, hrest, sym, hs257, hs285, hsym, hlt2, hmatch⟩ :=
      htp.2 hk
    have hbits := symbol_bounds _ _ _ _ hsym
    simp only [Int.toNat_natCast] at hbits
    have hview (v : List U8) (j : ℤ) := symbols_at s.val lit.val dist.val (out.val.take n.val) v
      (wpos cpos nbits) j sym (wpos cpos nbits + (lit.val[sym]!).val) hsym
      (by simp only [Int.toNat_natCast])
    step as ⟨len, len_post⟩
    step as ⟨d, d_post⟩
    step as ⟨start, start_post⟩
    have hlenv : len.val = a.val := by
      rw [len_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
    have hdv : d.val = b.val := by
      rw [d_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
    split
    · -- the distance reaches before the start of the content: no content
      try rw [WP.spec_ok]
      intro v j hs _
      rw [hiff, hview] at hs
      simp only [if_neg (by omega : (sym : ℤ) ≠ 256),
        if_neg (by omega : ¬ (sym : ℤ) < 256)] at hs
      obtain ⟨len', d', c, hm', _, p, hp, _⟩ := hs
      have he := match_unique _ _ _ _ _ _ _ _ _ _ hmatch hm'
      have hdp := hp.2.1
      rw [hprev] at hdp
      scalar_tac
    · rename_i hdn0
      have hdn : d.val ≤ n.val := by
        by_contra hc
        apply hdn0
        scalar_tac
      -- room for the copy: the position is within the limit, or the limit is zero and so is
      -- the position, which a copy of distance at least one contradicts
      have hroom : n.val + len.val + 24 ≤ out.val.length := by
        rcases hlim with hlim | ⟨hlim0, _⟩
        · scalar_tac
        · exfalso
          omega
      step as ⟨i, i_post⟩
      all_goals try scalar_tac
      have hi : i.val = nbits.val - bits.val := by scalar_tac
      obtain ⟨hwin2, hpos2⟩ := winv_skip s buf rest nbits i bits cpos hwin hrest hi (by omega)
      obtain ⟨nv, hnv1, hnv2, hnvw, hnvf⟩ := einv_skip s table buf nbits cpos e heinv rest bits.val hrest (by omega)
      step with (advance_correct s table rest i cpos nv hwin2 (by rw [hpos2]; exact hnvw) (by omega) hnv2
        (fun hle => by have := hnvf hle; omega)) as ⟨e1, w, nb, c, hwin3, hpos3, heinv3⟩
      step with (copy_at_correct out start n d len
        (by rw [start_post]; exact usize_wrapping_sub_of_le n d hdn) (by omega) hdn hroom)
        as ⟨out1, hout1, hcopy⟩
      step as ⟨n1, n1_post⟩
      all_goals try scalar_tac
      try rw [WP.spec_ok]
      rw [hpos2] at hpos3
      have hend := (winv_pos_bound s w nb c hwin3).2
      rw [hpos3] at hend
      apply syminv_cont s lit dist table R len0 r out1 n1 nbits cpos w nb c e1 bits.val (by omega) hwin3 hpos3 heinv3
      · rw [n1_post, hout1]; scalar_tac
      · rw [hout1]; exact hlen
      · intro v j
        rw [hiff, n1_post]
        apply symbols_match_iff _ _ _ _ _ _ _ _ _ _ _ _ _ hsym
          (by simp only [Int.toNat_natCast]) (by omega) (by omega) hmatch ?_ ?_
        · exact ⟨by omega, by omega⟩
        · try simp only
          rw [hlenv]
          rw [hdv, hlenv] at hcopy
          exact hcopy
  split
  · -- a literal from the window, then a second token without a refill
    have hk : kind.val = 1 := by scalar_tac
    obtain ⟨h56, hb11, ha, hsym, hbn, hrest⟩ := htp.1 hk
    have hbits := symbol_bounds _ _ _ _ hsym
    simp only [Int.toNat_natCast] at hbits
    have hview (v : List U8) (j : ℤ) := symbols_at s.val lit.val dist.val (out.val.take n.val) v
      (wpos cpos nbits) j a.val (wpos cpos nbits + bits.val) hsym
      (by simp only [Int.toNat_natCast]; omega)
    split
    · -- the buffer is full: the content is longer than the trailer claims
      try rw [WP.spec_ok]
      intro v j hs hv
      rw [hiff, hview] at hs
      simp only [if_neg (by scalar_tac : (a.val : ℤ) ≠ 256),
        if_pos (by scalar_tac : (a.val : ℤ) < 256)] at hs
      obtain ⟨p, hp, hrec⟩ := hs
      have hpv := symbols_length _ _ _ _ _ _ _ hrec
      have hlen := hp.2.1
      rw [hprev] at hlen
      scalar_tac
    · rename_i hnl0
      have hnl : n.val < out.val.length := by scalar_tac
      step as ⟨_, index_mut_back, _, index_mut_back_post⟩
      step as ⟨i1, i1_post⟩
      have hcast : i1.val = a.val := by
        rw [i1_post, UScalar.cast_val_eq]
        apply Nat.mod_eq_of_lt
        scalar_tac
      step as ⟨n1, n1_post⟩
      all_goals try scalar_tac
      step as ⟨nb2, nb2_post⟩
      all_goals try scalar_tac
      have hnb2 : nb2.val = nbits.val - bits.val := by scalar_tac
      -- the first literal is in place
      have happ : append_spec (out.val.take n.val) a.val ((out.val.set n.val i1).take (n.val + 1)) := by
        rw [take_set_succ _ _ _ hnl, ← hcast]
        exact append_byte _ i1
      have hiff1 : ∀ v j, R v j ↔ symbols_spec s.val (wpos cpos nbits + bits.val) lit.val dist.val
          ((out.val.set n.val i1).take (n.val + 1)) v j := by
        intro v j
        rw [hiff]
        exact symbols_literal_iff _ _ _ _ _ _ _ _ _ _ hsym
          (by simp only [Int.toNat_natCast]; omega) (by scalar_tac) (by scalar_tac) happ
      have hprev1 : ((out.val.set n.val i1).take (n.val + 1)).length = n.val + 1 := by
        rw [List.length_take_of_le]
        simp only [List.length_set]
        omega
      -- the window after the literal
      obtain ⟨hwin2, hpos2⟩ := winv_skip s buf rest nbits nb2 bits cpos hwin hrest hnb2 (by omega)
      obtain ⟨nv, hnv1, hnv2, hnvw, hnvf⟩ := einv_skip s table buf nbits cpos e heinv rest bits.val hrest (by omega)
      have hbw2 : ∀ k : Nat, k < 64 → k < nb2.val →
          bit_spec s.val (wpos cpos nbits + bits.val + k) ((rest.val / 2 ^ k % 2 : Nat) : ℤ) := by
        rw [← hpos2]
        exact window_bits _ _ _ _ hwin2.2.2.2
      -- the second entry, looked up from the window as it is
      step as ⟨i2, i2_post⟩
      step as ⟨i3, i3_post⟩
      have hi3 : i3.val = rest.val % 2048 := by
        rw [i3_post, UScalar.cast_val_eq, i2_post]
        apply Nat.mod_eq_of_lt
        scalar_tac
      clear i3_post
      step as ⟨e2, e2_post⟩
      have he2 : (45#u32).val ≤ nb2.val → e2 = table.val[rest.val % 2048]! := by
        intro _
        rw [← hi3, getElem!_pos table.val i3.val (by scalar_tac)]
        exact e2_post
      -- the window past the second entry's bits
      step as ⟨j1, hj1⟩
      step as ⟨q2, hq2⟩
      all_goals try scalar_tac
      have hq2' : q2.val = rest.val >>> (e2.val % 64) := by rw [hq2, hj1]
      have htok2 := peek_token_correct s (wpos cpos nbits + bits.val) rest q2 nb2 45#u32 e2 lit dist
        lit_codes dist_codes table dist_table distq n1 limit hdq ht hdtl hll hdl hlt hdt
        (by simp) hbw2 he2 hq2'
      step with htok2 as ⟨kind2, a2, b2, bits2, rest2, htp2⟩
      simp only [TokenPost] at htp2
      split
      · -- a second literal
        have hk2 : kind2.val = 1 := by scalar_tac
        obtain ⟨h45, hb11', ha2, hsym2, hbn2, hrest2⟩ := htp2.1 hk2
        have hbits2 := symbol_bounds _ _ _ _ hsym2
        simp only [Int.toNat_natCast] at hbits2
        have hview2 (v : List U8) (j : ℤ) := symbols_at s.val lit.val dist.val
          ((out.val.set n.val i1).take (n.val + 1)) v (wpos cpos nbits + bits.val) j a2.val
          (wpos cpos nbits + bits.val + bits2.val) hsym2 (by simp only [Int.toNat_natCast]; omega)
        try dsimp only
        generalize hout1def : index_mut_back i1 = out1
        have hout1 : out1.val = out.val.set n.val i1 := by
          rw [← hout1def, index_mut_back_post]
          simp only [alloc.vec.Vec.set_val_eq]
        have hout1l : out1.val.length = out.val.length := by rw [hout1]; simp only [List.length_set]
        have hol1 := alloc.vec.Vec.len_val out1
        split
        · try rw [WP.spec_ok]
          intro v j hs hv
          rw [hiff1, hview2] at hs
          simp only [if_neg (by scalar_tac : (a2.val : ℤ) ≠ 256),
            if_pos (by scalar_tac : (a2.val : ℤ) < 256)] at hs
          obtain ⟨p, hp, hrec⟩ := hs
          have hpv := symbols_length _ _ _ _ _ _ _ hrec
          have hlen := hp.2.1
          rw [hprev1] at hlen
          scalar_tac
        · rename_i hnl1
          have hnl1' : n1.val < out1.val.length := by scalar_tac
          step as ⟨_, index_mut_back1, _, index_mut_back1_post⟩
          step as ⟨i5, i5_post⟩
          have hcast2 : i5.val = a2.val := by
            rw [i5_post, UScalar.cast_val_eq]
            apply Nat.mod_eq_of_lt
            scalar_tac
          step as ⟨n2, n2_post⟩
          all_goals try scalar_tac
          step as ⟨i6, i6_post⟩
          all_goals try scalar_tac
          have hi6 : i6.val = nb2.val - bits2.val := by scalar_tac
          obtain ⟨hwin4, hpos4⟩ := winv_skip s rest rest2 nb2 i6 bits2 cpos hwin2 hrest2 hi6 (by omega)
          have hrest2' : rest2.val = buf.val >>> (bits.val + bits2.val) := by
            rw [hrest2, hrest, Nat.shiftRight_add]
          obtain ⟨nv', hnv1', hnv2', hnvw', hnvf'⟩ := einv_skip s table buf nbits cpos e heinv rest2
            (bits.val + bits2.val) hrest2' (by omega)
          have hpos4' : wpos cpos i6 = wpos cpos nbits + ((bits.val + bits2.val : Nat) : ℤ) := by
            rw [hpos4, hpos2]; push_cast; ring
          have hi6' : i6.val ≤ nv' := by rw [hi6, hnb2, Nat.sub_sub]; exact hnv1'
          step with (advance_correct s table rest2 i6 cpos nv' hwin4 (by rw [hpos4']; exact hnvw')
            hi6' hnv2' (fun hle => by have := hnvf' hle; omega)) as ⟨e1, w, nb, c, hwin3, hpos3, heinv3⟩
          try rw [WP.spec_ok]
          try dsimp only
          generalize hout2def : index_mut_back1 i5 = out2
          have hout2 : out2.val = out1.val.set n1.val i5 := by
            rw [← hout2def, index_mut_back1_post]
            simp only [alloc.vec.Vec.set_val_eq]
          have happ2 : append_spec (out1.val.take n1.val) a2.val (out2.val.take (n1.val + 1)) := by
            rw [hout2, take_set_succ _ _ _ hnl1', ← hcast2]
            exact append_byte _ i5
          rw [hpos4] at hpos3
          apply syminv_cont s lit dist table R len0 r out2 n2 nbits cpos w nb c e1 (bits.val + bits2.val)
            (by omega) hwin3 (by rw [hpos3, hpos2]; push_cast; ring) heinv3
          · rw [n2_post, hout2]; simp only [List.length_set]; scalar_tac
          · rw [hout2]; simp only [List.length_set]; rw [hout1l]; exact hlen
          · intro v j
            rw [hiff1, n2_post]
            have hp1 : wpos cpos nbits + ((bits.val + bits2.val : Nat) : ℤ) =
                wpos cpos nbits + bits.val + bits2.val := by push_cast; ring
            rw [hp1]
            have hprev1' : (out.val.set n.val i1).take (n.val + 1) = out1.val.take n1.val := by
              rw [hout1, n1_post]
            rw [hprev1'] at hview2 ⊢
            exact symbols_literal_iff _ _ _ _ _ _ _ _ _ _ hsym2
              (by simp only [Int.toNat_natCast]; omega) (by scalar_tac) (by scalar_tac) happ2
      split
      · -- a literal then a copy
        have hk2 : kind2.val = 2 := by scalar_tac
        obtain ⟨h45, hb40', hnlim, hlen3, hlen289, hd1, hrest2, sym, hs257, hs285, hsym2, hlt2, hmatch⟩ :=
          htp2.2 hk2
        have hbits2 := symbol_bounds _ _ _ _ hsym2
        simp only [Int.toNat_natCast] at hbits2
        have hview2 (v : List U8) (j : ℤ) := symbols_at s.val lit.val dist.val
          ((out.val.set n.val i1).take (n.val + 1)) v (wpos cpos nbits + bits.val) j sym
          (wpos cpos nbits + bits.val + (lit.val[sym]!).val) hsym2 (by simp only [Int.toNat_natCast])
        step as ⟨len, len_post⟩
        step as ⟨d, d_post⟩
        step as ⟨start, start_post⟩
        have hlenv : len.val = a2.val := by
          rw [len_post, UScalar.cast_val_eq]
          apply Nat.mod_eq_of_lt
          scalar_tac
        have hdv : d.val = b2.val := by
          rw [d_post, UScalar.cast_val_eq]
          apply Nat.mod_eq_of_lt
          scalar_tac
        split
        · try dsimp only
          try rw [WP.spec_ok]
          intro v j hs _
          rw [hiff1, hview2] at hs
          simp only [if_neg (by omega : (sym : ℤ) ≠ 256),
            if_neg (by omega : ¬ (sym : ℤ) < 256)] at hs
          obtain ⟨len', d', c, hm', _, p, hp, _⟩ := hs
          have he := match_unique _ _ _ _ _ _ _ _ _ _ hmatch hm'
          have hdp := hp.2.1
          rw [hprev1] at hdp
          scalar_tac
        · rename_i hdn0
          have hdn : d.val ≤ n1.val := by
            by_contra hc
            apply hdn0
            scalar_tac
          have hroom : n1.val + len.val + 24 ≤ out.val.length := by
            rcases hlim with hlim | ⟨hlim0, _⟩
            · scalar_tac
            · exfalso
              omega
          step as ⟨i4, i4_post⟩
          all_goals try scalar_tac
          have hi4 : i4.val = nb2.val - bits2.val := by scalar_tac
          obtain ⟨hwin4, hpos4⟩ := winv_skip s rest rest2 nb2 i4 bits2 cpos hwin2 hrest2 hi4 (by omega)
          have hrest2' : rest2.val = buf.val >>> (bits.val + bits2.val) := by
            rw [hrest2, hrest, Nat.shiftRight_add]
          obtain ⟨nv', hnv1', hnv2', hnvw', hnvf'⟩ := einv_skip s table buf nbits cpos e heinv rest2
            (bits.val + bits2.val) hrest2' (by omega)
          have hpos4' : wpos cpos i4 = wpos cpos nbits + ((bits.val + bits2.val : Nat) : ℤ) := by
            rw [hpos4, hpos2]; push_cast; ring
          have hi4' : i4.val ≤ nv' := by rw [hi4, hnb2, Nat.sub_sub]; exact hnv1'
          step with (advance_correct s table rest2 i4 cpos nv' hwin4 (by rw [hpos4']; exact hnvw')
            hi4' hnv2' (fun hle => by have := hnvf' hle; omega)) as ⟨e1, w, nb, c, hwin3, hpos3, heinv3⟩
          try dsimp only
          generalize hout1def : index_mut_back i1 = out1
          have hout1 : out1.val = out.val.set n.val i1 := by
            rw [← hout1def, index_mut_back_post]
            simp only [alloc.vec.Vec.set_val_eq]
          have hout1l : out1.val.length = out.val.length := by rw [hout1]; simp only [List.length_set]
          have hroom1 : n1.val + len.val + 24 ≤ out1.val.length := by rw [hout1l]; exact hroom
          step with (copy_at_correct out1 start n1 d len
            (by rw [start_post]; exact usize_wrapping_sub_of_le n1 d hdn) (by omega) hdn hroom1)
            as ⟨out2, hout2, hcopy⟩
          step as ⟨n2, n2_post⟩
          all_goals try scalar_tac
          try rw [WP.spec_ok]
          rw [hpos4] at hpos3
          have hend := (winv_pos_bound s w nb c hwin3).2
          rw [hpos3, hpos2] at hend
          apply syminv_cont s lit dist table R len0 r out2 n2 nbits cpos w nb c e1 (bits.val + bits2.val)
            (by omega) hwin3 (by rw [hpos3, hpos2]; push_cast; ring) heinv3
          · rw [n2_post, hout2, hout1l]; scalar_tac
          · rw [hout2, hout1l]; exact hlen
          · intro v j
            rw [hiff1, n2_post]
            have hp1 : wpos cpos nbits + ((bits.val + bits2.val : Nat) : ℤ) =
                wpos cpos nbits + bits.val + bits2.val := by push_cast; ring
            rw [hp1]
            have hprev1' : (out.val.set n.val i1).take (n.val + 1) = out1.val.take n1.val := by
              rw [hout1, n1_post]
            rw [hprev1'] at hview2 ⊢
            apply symbols_match_iff _ _ _ _ _ _ _ _ _ _ _ _ _ hsym2
              (by simp only [Int.toNat_natCast]) (by omega) (by omega) hmatch ?_ ?_
            · exact ⟨by omega, by omega⟩
            · try simp only
              rw [hlenv]
              rw [hdv, hlenv] at hcopy
              exact hcopy
      -- nothing fast after the literal: back to the top with the window after it
      step with (advance_correct s table rest nb2 cpos nv hwin2 (by rw [hpos2]; exact hnvw)
        (by omega) hnv2 (fun hle => by have := hnvf hle; omega)) as ⟨e1, w, nb, c, hwin3, hpos3, heinv3⟩
      try rw [WP.spec_ok]
      try dsimp only
      generalize hout1def : index_mut_back i1 = out1
      have hout1 : out1.val = out.val.set n.val i1 := by
        rw [← hout1def, index_mut_back_post]
        simp only [alloc.vec.Vec.set_val_eq]
      rw [hpos2] at hpos3
      apply syminv_cont s lit dist table R len0 r out1 n1 nbits cpos w nb c e1 bits.val (by omega) hwin3 hpos3 heinv3
      · rw [n1_post, hout1]; simp only [List.length_set]; scalar_tac
      · rw [hout1]; simp only [List.length_set]; exact hlen
      · intro v j
        rw [hout1, n1_post]
        exact hiff1 v j
  -- the slow path: through a reader at the window's position
  clear htok htp
  step with (reader_at_correct s cpos nbits hc1 hn1 hnc1) as ⟨r1, hr1inv, hr1pos⟩
  rw [← hr1pos] at hiff
  step*
  all_goals try (rcases value1 with ⟨len, d⟩)
  all_goals try dsimp only
  all_goals try step*
  all_goals try simp only [SymbolPost, show o = some value by assumption] at o_post
  all_goals try simp only [SymbolPost, show o = none by assumption] at o_post
  all_goals try simp only [MatchPost, show o1 = some (len, d) by assumption] at o1_post
  all_goals try simp only [MatchPost, show o1 = none by assumption] at o1_post
  all_goals try exact o_post.1
  all_goals try exact o1_post.1
  all_goals try (
    have hsym := o_post.2.2.1
    have hpos := o_post.2.2.2
    have hbits := symbol_bounds _ _ _ _ hsym
    simp only [Int.toNat_natCast] at hbits)
  all_goals try (have hmatch := o1_post.2.2.2.2.1; have hlen := o1_post.2.1; have hdist := o1_post.2.2.1; omega)
  all_goals try (have h24 : (24#usize).val = 24 := by simp; scalar_tac)
  -- len + 24 does not overflow: the length is a 32-bit value
  all_goals try (
    show len.val + (24#usize).val ≤ Usize.max
    have hl32 := o1_post.2.2.2.2.2
    have h24 : (24#usize).val = 24 := by simp
    scalar_tac)
  -- the lookups of the next entry from the refilled window: the index is below the table's length
  all_goals try (
    show i4.val < table.val.length
    rw [show i4.val = i3.val from (by rw [i4_post, UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; scalar_tac)]
    scalar_tac)
  all_goals try (
    show i7.val < table.val.length
    rw [show i7.val = i6.val from (by rw [i7_post, UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; scalar_tac)]
    scalar_tac)
  · -- no symbol at the position: no content
    intro v j hs _
    obtain ⟨sym, a, hs, _⟩ := (symbols_unfold _ _ _ _ _ _ _).mp ((hiff v j).mp hs)
    exact o_post.2 sym (by have hp := hs.2.1; omega) hs
  all_goals
    have hview (v : List U8) (j : ℤ) := symbols_at s.val lit.val dist.val (out.val.take n.val) v
      (pos r1) j value.val (pos r2) hsym (by simpa only [Int.toNat_natCast] using hpos)
  · -- the end of the block
    refine ⟨o_post.1, hn, hlen, ?_⟩
    apply (hiff _ _).mpr
    apply (hview (out.val.take n.val) (pos r2)).mpr
    have hv : (value.val : ℤ) = 256 := by scalar_tac
    simp only [hv, if_true]
    simp
  · -- a literal into a full buffer: the content is longer than the trailer claims
    intro v j hs hv
    rw [hiff, hview] at hs
    simp only [if_neg (by scalar_tac : (value.val : ℤ) ≠ 256),
      if_pos (by scalar_tac : (value.val : ℤ) < 256)] at hs
    obtain ⟨p, hp, hrec⟩ := hs
    have hpv := symbols_length _ _ _ _ _ _ _ hrec
    have hlen := hp.2.1
    rw [hprev] at hlen
    scalar_tac
  · -- a literal: the window and the entry at the reader's position after it
    have hcast : i2.val = value.val := by
      rw [i2_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
    have hnl : n.val < out.val.length := by scalar_tac
    have happ : append_spec (out.val.take n.val) value.val ((out.val.set n.val i2).take (n.val + 1)) := by
      rw [take_set_succ _ _ _ hnl, ← hcast]
      exact append_byte _ i2
    have hend := (inv_pos_bound s r2 o_post.1).2
    have hwin3 : WInv s w3 nb3 c3 := w3_post
    have hpos3 : wpos c3 nb3 = pos r2 := by rw [w3_post1, w2_post1]
    have hi4 : i4.val = w3.val % 2048 := by
      rw [i4_post, UScalar.cast_val_eq, i3_post]
      apply Nat.mod_eq_of_lt
      scalar_tac
    have he1 : e1 = table.val[w3.val % 2048]! := by
      rw [← hi4, getElem!_pos table.val i4.val (by scalar_tac)]
      exact e1_post
    refine ⟨⟨hwin3, einv_of_lookup s table w2 nb2 c2 w3 nb3 c3 e1 hwin3 w3_post1 w3_post4 w3_post5 he1,
      ?_, ?_, ?_⟩, ?_⟩
    · rw [index_mut_back_post]
      simp only [alloc.vec.Vec.set_val_eq, List.length_set]
      scalar_tac
    · rw [index_mut_back_post]
      simp only [alloc.vec.Vec.set_val_eq, List.length_set]
      exact hlen
    · intro v j
      rw [hiff, index_mut_back_post]
      simp only [alloc.vec.Vec.set_val_eq, n1_post, hpos3]
      exact symbols_literal_iff _ _ _ _ _ _ _ _ _ _ hsym
        (by simpa only [Int.toNat_natCast] using hpos) (by scalar_tac) (by scalar_tac) happ
    · try simp only
      rw [hpos3]
      apply bit_measure_decreases
      · omega
      · exact hend
  · -- a symbol above 285: no content
    intro v j hs _
    rw [hiff, hview] at hs
    simp only [if_neg (by scalar_tac : (value.val : ℤ) ≠ 256),
      if_neg (by scalar_tac : ¬ (value.val : ℤ) < 256)] at hs
    obtain ⟨len', d', c, ⟨_, _, ⟨lb, hlb, _⟩, _⟩, _⟩ := hs
    rw [lbase_spec] at hlb
    have hb := (hlb.2 hlb.1).1
    scalar_tac
  · -- no match at the position: no content
    intro v j hs _
    rw [hiff, hview] at hs
    simp only [if_neg (by scalar_tac : (value.val : ℤ) ≠ 256),
      if_neg (by scalar_tac : ¬ (value.val : ℤ) < 256)] at hs
    obtain ⟨len', d', c, hm, _⟩ := hs
    apply o1_post len' d' c
    have hlc : (lc.val : ℤ) = (value.val : ℤ) - 257 := by omega
    rwa [hlc]
  · -- a distance reaching before the start: no content
    intro v j hs _
    rw [hiff, hview] at hs
    simp only [if_neg (by scalar_tac : (value.val : ℤ) ≠ 256),
      if_neg (by scalar_tac : ¬ (value.val : ℤ) < 256)] at hs
    obtain ⟨len', d', c, hm, _, p, hp, _⟩ := hs
    have hlc : (lc.val : ℤ) = (value.val : ℤ) - 257 := by omega
    rw [← hlc] at hm
    have he := match_unique _ _ _ _ _ _ _ _ _ _ o1_post.2.2.2.2.1 hm
    have hd := hp.2.1
    rw [hprev] at hd
    scalar_tac
  all_goals try (
    intro v j hs hv
    exfalso
    scalar_tac)
  all_goals try (
    intro v j hs hv
    rw [hiff, hview] at hs
    simp only [if_neg (by scalar_tac : (value.val : ℤ) ≠ 256),
      if_neg (by scalar_tac : ¬ (value.val : ℤ) < 256)] at hs
    obtain ⟨len', d', c, hm, _, p, hp, hrec⟩ := hs
    have hlc : (lc.val : ℤ) = (value.val : ℤ) - 257 := by omega
    rw [← hlc] at hm
    have he := match_unique _ _ _ _ _ _ _ _ _ _ o1_post.2.2.2.2.1 hm
    have hsize := hp.2.2.1
    have hgrows := symbols_length _ _ _ _ _ _ _ hrec
    rw [hprev] at hsize
    scalar_tac)
  · -- a copy: the window and the entry at the reader's position after it
    have hend := (inv_pos_bound s r3 o1_post.1).2
    have hwin3 : WInv s w3 nb3 c3 := w3_post
    have hpos3 : wpos c3 nb3 = pos r3 := by rw [w3_post1, w2_post1]
    have hi7 : i7.val = w3.val % 2048 := by
      rw [i7_post, UScalar.cast_val_eq, i6_post]
      apply Nat.mod_eq_of_lt
      scalar_tac
    have he1 : e1 = table.val[w3.val % 2048]! := by
      rw [← hi7, getElem!_pos table.val i7.val (by scalar_tac)]
      exact e1_post
    refine ⟨⟨hwin3, einv_of_lookup s table w2 nb2 c2 w3 nb3 c3 e1 hwin3 w3_post1 w3_post4 w3_post5 he1,
      ?_, ?_, ?_⟩, ?_⟩
    · rw [n1_post, out1_post]; scalar_tac
    · rw [out1_post]; exact hlen
    · intro v j
      rw [hiff, n1_post, hpos3]
      apply symbols_match_iff _ _ _ _ _ _ _ _ _ _ _ _ _ hsym
        (by simpa only [Int.toNat_natCast] using hpos) (by scalar_tac) (by scalar_tac) ?_ ?_ out1_post1
      · have hlc : (lc.val : ℤ) = (value.val : ℤ) - 257 := by omega
        simpa only [hlc] using o1_post.2.2.2.2.1
      · exact ⟨o1_post.2.2.2.1, hend⟩
    · try simp only
      rw [hpos3]
      apply bit_measure_decreases
      · have hp := o1_post.2.2.2.1; omega
      · exact hend

theorem decode_symbols_loop_correct (s : Aeneas.Std.Slice U8) (r : Reader)
    (lit dist : Aeneas.Std.Slice U8) (out : alloc.vec.Vec U8) (n : Usize)
    (buf : U64) (nbits : U32) (cpos : Usize) (e : U32)
    (lit_codes dist_codes : Aeneas.Std.Slice U32) (table dist_table : Array U32 2048#usize)
    (distq : Array U8 1024#usize) (hints : Array U16 512#usize) (limit : Usize)
    (R : List U8 → ℤ → Prop) (cap len0 : Nat)
    (hdq : DistQ dist.val dist_table.val distq.val)
    (ht : Hints lit.val lit_codes.val table.val false 11) (hdtl : Hints dist.val dist_codes.val dist_table.val true 10)
    (hll : lit_codes.val.length = lit.val.length) (hdl : dist_codes.val.length = dist.val.length)
    (hlt : Entries lit.val lit_codes.val) (hdt : Entries dist.val dist_codes.val)
    (hl : lit.val.length ≤ 320) (hd : dist.val.length ≤ 320)
    (hbl : ∀ j, j < lit.val.length → (lit.val[j]!).val ≤ 15)
    (hbd : ∀ j, j < dist.val.length → (dist.val[j]!).val ≤ 15)
    (hcap : cap + 24 ≤ len0)
    (hlim : limit.val + 320 ≤ len0 ∨ (limit.val = 0 ∧ len0 < 320))
    (h : SymInv s lit dist table R len0 (r, out, n, buf, nbits, cpos, e)) :
    decode_symbols_cached_loop s r lit dist lit_codes dist_codes table dist_table distq
      out hints n limit buf nbits cpos e ⦃ z => ParsePost s cap len0 R z ⦄ := by
  unfold decode_symbols_cached_loop
  apply loop.spec_decr_nat (fun (st : Reader × alloc.vec.Vec U8 × Usize × U64 × U32 × Usize × U32) =>
      (8 * (s.val.length : ℤ) - wpos st.2.2.2.2.2.1 st.2.2.2.2.1).toNat)
    (fun st => SymInv s lit dist table R len0 st)
  · rintro ⟨r', out', n', buf', nbits', cpos', e'⟩ hinv
    apply WP.spec_mono (decode_symbols_body s lit dist lit_codes dist_codes table dist_table
      distq hints limit R cap len0 r' out' n' buf' nbits' cpos' e' hdq ht hdtl hll hdl hlt hdt hl hd
      hbl hbd hcap hlim hinv)
    intro z hz
    cases z <;> exact hz
  · exact h

@[step]
theorem decode_symbols_cached_correct (s : Aeneas.Std.Slice U8) (r : Reader)
    (lit dist : Aeneas.Std.Slice U8) (out : alloc.vec.Vec U8) (n : Usize) (cap : Nat)
    (lit_codes dist_codes : Aeneas.Std.Slice U32) (table dist_table : Array U32 2048#usize)
    (distq : Array U8 1024#usize) (rv : Array U8 256#usize) (hrv : RevTab rv.val 256)
    (ht : Hints lit.val lit_codes.val table.val false 11) (hdtl : Hints dist.val dist_codes.val dist_table.val true 10)
    (hdq : DistQ dist.val dist_table.val distq.val)
    (hll : lit_codes.val.length = lit.val.length) (hdl : dist_codes.val.length = dist.val.length)
    (hlt : Entries lit.val lit_codes.val) (hdt : Entries dist.val dist_codes.val)
    (h : Inv s r) (hn : n.val ≤ out.val.length) (hcap : cap + 24 ≤ out.val.length)
    (hl : lit.val.length ≤ 320) (hd : dist.val.length ≤ 320)
    (hbl : ∀ j, j < lit.val.length → (lit.val[j]!).val ≤ 15)
    (hbd : ∀ j, j < dist.val.length → (dist.val[j]!).val ≤ 15) :
    decode_symbols_cached s r lit dist lit_codes dist_codes table dist_table distq rv out n ⦃ z =>
      ParsePost s cap out.val.length (symbols_spec s.val (pos r) lit.val dist.val (out.val.take n.val)) z ⦄ := by
  have htl := ht.1
  unfold decode_symbols_cached
  step with (long_hints_correct lit lit_codes rv hrv) as ⟨hints, _⟩
  -- the limit: the buffer's length less 320 when it is that long, else zero
  try dsimp only
  split
  · step as ⟨limit, limit_post⟩
    all_goals try scalar_tac
    step with (window_at_correct s r h) as ⟨w0, nb0, c0, hwin0, hpos0⟩
    step with (refill_correct s w0 nb0 c0 hwin0) as ⟨w1, nb1, c1, hwin1, hpos1, _, hfill1, hno1, hall1⟩
    step as ⟨i1, i1_post⟩
    step as ⟨i2, i2_post⟩
    have hi2 : i2.val = w1.val % 2048 := by
      rw [i2_post, UScalar.cast_val_eq, i1_post]
      apply Nat.mod_eq_of_lt
      scalar_tac
    clear i2_post
    step as ⟨e, e_post⟩
    have he : e = table.val[w1.val % 2048]! := by
      rw [← hi2, getElem!_pos table.val i2.val (by scalar_tac)]
      exact e_post
    exact decode_symbols_loop_correct s r lit dist out n w1 nb1 c1 e lit_codes dist_codes table
      dist_table distq hints limit _ cap out.val.length hdq ht hdtl hll hdl hlt hdt hl hd hbl hbd
      hcap (Or.inl (by scalar_tac))
      ⟨hwin1, einv_of_lookup s table w0 nb0 c0 w1 nb1 c1 e hwin1 hpos1 hno1 hall1 he,
        hn, rfl, fun _ _ => by simp only [hpos1, hpos0]⟩
  · step with (window_at_correct s r h) as ⟨w0, nb0, c0, hwin0, hpos0⟩
    step with (refill_correct s w0 nb0 c0 hwin0) as ⟨w1, nb1, c1, hwin1, hpos1, _, hfill1, hno1, hall1⟩
    step as ⟨i1, i1_post⟩
    step as ⟨i2, i2_post⟩
    have hi2 : i2.val = w1.val % 2048 := by
      rw [i2_post, UScalar.cast_val_eq, i1_post]
      apply Nat.mod_eq_of_lt
      scalar_tac
    clear i2_post
    step as ⟨e, e_post⟩
    have he : e = table.val[w1.val % 2048]! := by
      rw [← hi2, getElem!_pos table.val i2.val (by scalar_tac)]
      exact e_post
    exact decode_symbols_loop_correct s r lit dist out n w1 nb1 c1 e lit_codes dist_codes table
      dist_table distq hints 0#usize _ cap out.val.length hdq ht hdtl hll hdl hlt hdt hl hd hbl hbd
      hcap (Or.inr ⟨by simp, by scalar_tac⟩)
      ⟨hwin1, einv_of_lookup s table w0 nb0 c0 w1 nb1 c1 e hwin1 hpos1 hno1 hall1 he,
        hn, rfl, fun _ _ => by simp only [hpos1, hpos0]⟩

@[step]
theorem decode_symbols_correct (s : Aeneas.Std.Slice U8) (r : Reader)
    (lit dist : Aeneas.Std.Slice U8) (out : alloc.vec.Vec U8) (n : Usize) (cap : Nat)
    (h : Inv s r) (hn : n.val ≤ out.val.length) (hcap : cap + 24 ≤ out.val.length)
    (hl : lit.val.length ≤ 320) (hd : dist.val.length ≤ 320)
    (hbl : ∀ j, j < lit.val.length → (lit.val[j]!).val ≤ 15)
    (hbd : ∀ j, j < dist.val.length → (dist.val[j]!).val ≤ 15) :
    decode_symbols s r lit dist out n ⦃ z =>
      ParsePost s cap out.val.length (symbols_spec s.val (pos r) lit.val dist.val (out.val.take n.val)) z ⦄ := by
  unfold decode_symbols
  step*
  all_goals simp only [alloc.vec.Vec.deref, Slice.from_val] at *
  all_goals try assumption
  -- the distance codeword lengths by table index, then the decoder
  step with (dist_lens_correct dist_table distn dist.val distn_post) as ⟨distq, hdq⟩
  step*
  all_goals simp only [alloc.vec.Vec.deref, Slice.from_val] at *
  all_goals assumption

end Gzip.Proofs.Decode.SymbolsImpl
