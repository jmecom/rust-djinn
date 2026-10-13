import Gzip.Proofs.Decode.LengthsImpl
import Gzip.Proofs.Decode.TokenImpl

/-! # The code lengths read through the bit window

`read_lengths_fast` decodes the runs of code lengths from a 64-bit window with the seven-bit
table, and hands over to `read_lengths` (the reader) when the window is short or the table has
no entry. Its loop keeps, besides the window, the relation between what was read so far and the
block's `lengths_spec`: the specification from the start equals the specification from the
window's position on, for any completion of the list read so far. -/

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.RunImpl Gzip.Proofs.Decode.RepeatImpl Gzip.Proofs.Decode.LengthsFacts
open Gzip.Proofs.Decode.LengthsImpl Gzip.Proofs.Decode.CodewordTable Gzip.Proofs.Decode.DecodeTable
open Gzip.Proofs.Decode.PeekFacts Gzip.Proofs.Decode.WideFacts Gzip.Proofs.Decode.WindowFacts Gzip.Proofs.Decode.WindowImpl
open Gzip.Proofs.Decode.TokenImpl

namespace Gzip.Proofs.Decode.LengthsWindow

/-- What `run_window` returns for the symbol `sym` at `P`: nothing when no run can start there,
or a run with its value, count and the bits it takes (the codeword's `n` and up to seven more). -/
def RunWinPost (s : List U8) (P : ℤ) (cl prev : List U8) (n : Nat) (z : Option (U8 × Usize × U32)) : Prop :=
  match z with
  | none => ∀ value count j, ¬ RunSpec s cl prev P value count j
  | some (value, count, bits) => 1 ≤ count.val ∧ count.val ≤ 138 ∧ value.val ≤ 15 ∧
      n ≤ bits.val ∧ bits.val ≤ n + 7 ∧ bits.val ≤ 14 ∧ RunSpec s cl prev P value count.val (P + bits.val)

theorem cast_u8_val (sym : U32) (h : sym.val < 256) : (UScalar.cast .U8 sym).val = sym.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

theorem cast_usize64 (v : U64) (h : v.val < 128) : (UScalar.cast .Usize v).val = v.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

set_option maxHeartbeats 4000000 in
theorem run_window_correct (s : Aeneas.Std.Slice U8) (P : ℤ) (cl : Aeneas.Std.Slice U8)
    (sym n : U32) (q : U64) (all : Aeneas.Std.Slice U8)
    (hsym : symbol_spec s.val P cl.val sym.val) (hn31 : n.val ≤ 31) (hn7 : sym.val < 19 → n.val ≤ 7)
    (hn : sym.val < 19 → (cl.val[sym.val]!).val = n.val)
    (hq : sym.val < 19 → ∀ k : Nat, k < 7 → bit_spec s.val (P + n.val + k) ((q.val / 2 ^ k % 2 : Nat) : ℤ))
    (hp : ∀ j, j < all.val.length → (all.val[j]!).val ≤ 15) :
    run_window sym n q all ⦃ z => RunWinPost s.val P cl.val all.val n.val z ⦄ := by
  have hview (v : U8) (c j : ℤ) (h19 : sym.val < 19) :=
    run_at s.val cl.val all.val P (P + n.val) sym.val v c j hsym
      (by simp only [Int.toNat_natCast, hn h19])
  unfold run_window
  dsimp only
  split
  · -- a literal length
    step*
    all_goals try simp only [RunWinPost]
    have h19 : sym.val < 19 := by scalar_tac
    have hi : i.val = sym.val := by rw [i_post, cast_u8_val sym (by scalar_tac)]
    refine ⟨by decide, by decide, by rw [hi]; scalar_tac, Nat.le_refl _,
      by omega, by have := hn7 h19; omega, (hview _ _ _ h19).mpr ?_⟩
    simp only [RunKind, if_pos (by scalar_tac : (sym.val : ℤ) < 16)]
    refine ⟨by rw [hi], by norm_num, by norm_num⟩
  split
  · split
    · -- symbol 16 with nothing to repeat
      step*
      all_goals try simp only [RunWinPost]
      intro v c j hs
      have h19 : sym.val < 19 := by scalar_tac
      rw [hview _ _ _ h19] at hs
      have he : (sym.val : ℤ) = 16 := by scalar_tac
      simp only [RunKind, he] at hs
      norm_num at hs
      scalar_tac
    · -- symbol 16
      step*
      all_goals try scalar_tac
      all_goals try (have hc := cast_usize64 i4 (by scalar_tac); rw [← i5_post] at hc; scalar_tac)
      all_goals try simp only [RunWinPost]
      have h19 : sym.val < 19 := by scalar_tac
      have hi3 : i3 = all.val[all.val.length - 1]! := by
        have hidx : i2.val = all.val.length - 1 := by scalar_tac
        rw [← hidx, getElem!_pos all.val _ (by scalar_tac)]
        exact i3_post
      have hip := hp (all.val.length - 1) (by scalar_tac)
      have hf := field_of_bits s.val 2 (P + n.val) q.val (fun k hk => hq h19 k (by omega))
      have hi5 : i5.val = q.val % 4 := by rw [i5_post, cast_usize64 i4 (by scalar_tac), i4_post]
      refine ⟨by scalar_tac, by scalar_tac, by rw [hi3]; exact hip, by scalar_tac, by scalar_tac, by have := hn7 h19; scalar_tac,
        (hview _ _ _ h19).mpr ?_⟩
      have he : (sym.val : ℤ) = 16 := by scalar_tac
      norm_num only [RunKind, he]
      refine ⟨by scalar_tac, hi3, ((q.val % 4 : Nat) : ℤ), by simpa using hf, ?_, ?_⟩
      · rw [i6_post, hi5]; push_cast; try ring
      · rw [i7_post]; push_cast; try ring
  split
  · -- symbol 17
    step*
    all_goals try scalar_tac
    all_goals try (have hc := cast_usize64 i (by scalar_tac); rw [← i1_post] at hc; scalar_tac)
    all_goals try simp only [RunWinPost]
    have h19 : sym.val < 19 := by scalar_tac
    have hf := field_of_bits s.val 3 (P + n.val) q.val (fun k hk => hq h19 k (by omega))
    have hi1 : i1.val = q.val % 8 := by rw [i1_post, cast_usize64 i (by scalar_tac), i_post]
    refine ⟨by scalar_tac, by scalar_tac, by decide, by scalar_tac, by scalar_tac, by have := hn7 h19; scalar_tac,
      (hview _ _ _ h19).mpr ?_⟩
    have he : (sym.val : ℤ) = 17 := by scalar_tac
    norm_num only [RunKind, he]
    refine ⟨rfl, ((q.val % 8 : Nat) : ℤ), by simpa using hf, ?_, ?_⟩
    · rw [i2_post, hi1]; push_cast; try ring
    · rw [i3_post]; push_cast; try ring
  split
  · -- symbol 18
    step*
    all_goals try scalar_tac
    all_goals try (have hc := cast_usize64 i (by scalar_tac); rw [← i1_post] at hc; scalar_tac)
    all_goals try simp only [RunWinPost]
    have h19 : sym.val < 19 := by scalar_tac
    have hf := field_of_bits s.val 7 (P + n.val) q.val (fun k hk => hq h19 k (by omega))
    have hi1 : i1.val = q.val % 128 := by rw [i1_post, cast_usize64 i (by scalar_tac), i_post]
    refine ⟨by scalar_tac, by scalar_tac, by decide, by scalar_tac, by scalar_tac, by have := hn7 h19; scalar_tac,
      (hview _ _ _ h19).mpr ?_⟩
    have he : (sym.val : ℤ) = 18 := by scalar_tac
    norm_num only [RunKind, he]
    refine ⟨trivial, rfl, ((q.val % 128 : Nat) : ℤ), by simpa using hf, ?_, ?_⟩
    · rw [i2_post, hi1]; push_cast; try ring
    · rw [i3_post]; push_cast; try ring
  · -- no run starts with a symbol above 18
    step*
    all_goals try simp only [RunWinPost]
    intro v c j hs
    obtain ⟨sym', a, hs', ha, hr⟩ := hs
    have he := Huffman.symbol_unique _ _ _ _ _ hsym hs'
    rw [← he] at hr
    unfold RunKind at hr
    split_ifs at hr <;> scalar_tac

/-- The loop's knowledge about the list `cur` read so far, with the window at `P`: it is a
prefix-extension of `prev` within `total`, and the block's relation from `start` is the relation
from `P` on `cur`, for any completion of `cur`. -/
def LInvP (s cl prev : List U8) (start : ℤ) (total : Nat) (cur : List U8) (P : ℤ) : Prop :=
  cur.length ≤ total ∧ cur.take prev.length = prev ∧ Bounds cur ∧
  (∀ all j, all.length = total → all.take prev.length = prev →
    lengths_spec s start cl prev.length all j →
    all.take cur.length = cur ∧ lengths_spec s P cl cur.length all j) ∧
  (∀ all j, all.length = total → all.take cur.length = cur →
    lengths_spec s P cl cur.length all j → lengths_spec s start cl prev.length all j)

def LInv (s : Aeneas.Std.Slice U8) (cl prev : List U8) (start : ℤ) (total : Nat)
    (st : alloc.vec.Vec U8 × U64 × U32 × Usize) : Prop :=
  WInv s st.2.1 st.2.2.1 st.2.2.2 ∧ LInvP s.val cl prev start total st.1.val (wpos st.2.2.2 st.2.2.1)

theorem take_length_le (all prev : List U8) (h : all.take prev.length = prev) : prev.length ≤ all.length := by
  have hl := congrArg List.length h
  simp only [List.length_take] at hl
  omega

/-- Handing over to the reader: the window's position becomes the reader's, and the reader's
result is translated through the invariant. -/
theorem finish_correct (s : Aeneas.Std.Slice U8) (r : Reader) (cl : Aeneas.Std.Slice U8)
    (codes : Aeneas.Std.Slice U32) (table : Array U32 2048#usize)
    (all : alloc.vec.Vec U8) (total : Usize) (buf : U64) (nbits : U32) (cpos : Usize)
    (prev : List U8) (Q : alloc.vec.Vec U8 × U64 × U32 × Usize → Prop)
    (hinv : LInv s cl.val prev (pos r) total.val (all, buf, nbits, cpos))
    (ht : total.val ≤ 320) (hl : cl.val.length ≤ 320)
    (hcl : ∀ j, j < cl.val.length → (cl.val[j]!).val ≤ 15)
    (hcodes : codes.val.length = cl.val.length) (hentries : Entries cl.val codes.val)
    (hhints : Hints cl.val codes.val table.val false 7) :
    (do
      let r1 ← reader_at cpos nbits
      let (o, r2, all1) ← read_lengths s r1 cl codes table all total
      ok (ControlFlow.done (o, r2, all1))) ⦃ z =>
        match z with
        | .done res => LengthPost s r cl prev total.val res
        | .cont st => Q st ⦄ := by
  obtain ⟨hwin, hlen, hpre, hb, hfwd, hbwd⟩ := hinv
  simp only at hwin hlen hpre hb hfwd hbwd
  step with (reader_at_correct s cpos nbits hwin.1 hwin.2.1 hwin.2.2.1) as ⟨r1, hr1, hpos1⟩
  step with (read_lengths_correct s r1 cl codes table all total hr1 hlen hb ht hl hcl hcodes
    hentries hhints) as ⟨o, r2, all1, hpost⟩
  try rw [WP.spec_ok]
  try simp only
  cases o with
  | none =>
    simp only [LengthPost] at hpost ⊢
    intro all' j hlen' hpre' hs
    obtain ⟨hpre2, hs2⟩ := hfwd all' j hlen' hpre' hs
    rw [hpos1] at hpost
    exact hpost all' j hlen' hpre2 hs2
  | some u =>
    simp only [LengthPost] at hpost ⊢
    obtain ⟨hr2, hlen1, hpre1, hb1, hs1⟩ := hpost
    refine ⟨hr2, hlen1, prefix_trans all1.val all.val prev hpre1 hpre (take_length_le _ _ hpre),
      hb1, ?_⟩
    rw [hpos1] at hs1
    exact hbwd all1.val (pos r2) hlen1 hpre1 hs1

/-- The window after `bits` bits were taken. -/
theorem winv_skip (s : Aeneas.Std.Slice U8) (w buf1 : U64) (nb nbits1 bits : U32) (c : Usize)
    (h : WInv s w nb c) (hb : buf1.val = w.val >>> bits.val) (hn : nbits1.val = nb.val - bits.val)
    (hle : bits.val ≤ nb.val) :
    WInv s buf1 nbits1 c ∧ wpos c nbits1 = wpos c nb + bits.val := by
  obtain ⟨hc, hn63, hnc, hw⟩ := h
  have hpos : wpos c nbits1 = wpos c nb + bits.val := by unfold wpos; omega
  refine ⟨⟨hc, by omega, by omega, ?_⟩, hpos⟩
  rw [hb, hn, hpos]
  exact window_skip s.val w.val nb.val bits.val (wpos c nb) hw (by scalar_tac) (by omega) hle

/-- The invariant after a run of `count` values that takes `bits` bits. -/
theorem linvp_step (s cl prev : List U8) (start : ℤ) (total : Nat) (cur : List U8) (P : ℤ)
    (value : U8) (count : Nat) (bits : Nat)
    (h : LInvP s cl prev start total cur P) (hlt : cur.length < total)
    (hcount : 1 ≤ count) (hfit : cur.length + count ≤ total) (hv : value.val ≤ 15)
    (hr : RunSpec s cl cur P value count (P + bits)) :
    LInvP s cl prev start total (cur ++ List.replicate count value) (P + bits) := by
  obtain ⟨hlen, hpre, hb, hfwd, hbwd⟩ := h
  have hlen1 : (cur ++ List.replicate count value).length = cur.length + count := by
    simp only [List.length_append, List.length_replicate]
  have hprefix : (cur ++ List.replicate count value).take cur.length = cur := by simp
  refine ⟨by omega, prefix_trans _ cur prev hprefix hpre (take_length_le _ _ hpre),
    bounds_replicate cur value count hb hv, ?_, ?_⟩
  · intro all j hall hpre' hs
    obtain ⟨hpre2, hs2⟩ := hfwd all j hall hpre' hs
    have hstep := (lengths_step_iff s cl cur all P (P + bits) j value count (by omega) hpre2
      hcount hr).mp hs2
    obtain ⟨_, hpre3, hs3⟩ := hstep
    rw [hlen1]
    refine ⟨hpre3, ?_⟩
    simpa only [Nat.cast_add] using hs3
  · intro all j hall hpre' hs
    have hpre'' : all.take (cur.length + count) = cur ++ List.replicate count value := by
      rw [← hlen1]; exact hpre'
    rw [hlen1] at hs
    have hpre2 : all.take cur.length = cur :=
      prefix_trans all _ cur hpre' hprefix (by rw [hlen1]; omega)
    apply hbwd all j hall hpre2
    apply (lengths_step_iff s cl cur all P (P + bits) j value count (by omega) hpre2 hcount hr).mpr
    refine ⟨by omega, hpre'', ?_⟩
    simpa only [Nat.cast_add] using hs

set_option maxHeartbeats 12000000 in
theorem lengths_body (s : Aeneas.Std.Slice U8) (r : Reader) (cl : Aeneas.Std.Slice U8)
    (codes : Aeneas.Std.Slice U32) (table : Array U32 2048#usize) (total : Usize)
    (all : alloc.vec.Vec U8) (buf : U64) (nbits : U32) (cpos : Usize) (prev : List U8)
    (ht : total.val ≤ 320) (hl : cl.val.length ≤ 320)
    (hcl : ∀ j, j < cl.val.length → (cl.val[j]!).val ≤ 15)
    (hcodes : codes.val.length = cl.val.length) (hentries : Entries cl.val codes.val)
    (hhints : Hints cl.val codes.val table.val false 7)
    (hinv : LInv s cl.val prev (pos r) total.val (all, buf, nbits, cpos)) :
    read_lengths_fast_loop.body s r cl codes table total all buf nbits cpos ⦃ z =>
      match z with
      | .done res => LengthPost s r cl prev total.val res
      | .cont st => LInv s cl.val prev (pos r) total.val st ∧
          total.val - st.1.val.length < total.val - all.val.length ⦄ := by
  have hwin := hinv.1
  have hinvp := hinv.2
  simp only at hwin hinvp
  have htl := hhints.1
  unfold read_lengths_fast_loop.body
  dsimp only
  split
  swap
  · -- all the lengths are there
    exact finish_correct s r cl codes table all total buf nbits cpos prev _ hinv ht hl hcl hcodes
      hentries hhints
  rename_i hlt
  have hlt' : all.val.length < total.val := by scalar_tac
  step with (refill_correct s buf nbits cpos hwin) as ⟨w, nb, c, hwin1, hpos1, _, _, _, _⟩
  have hinv1 : LInv s cl.val prev (pos r) total.val (all, w, nb, c) := ⟨hwin1, by rw [hpos1]; exact hinvp⟩
  split
  · exact finish_correct s r cl codes table all total w nb c prev _ hinv1 ht hl hcl hcodes hentries hhints
  rename_i h14
  have h14' : 14 ≤ nb.val := by scalar_tac
  -- the entry at the window's position
  step as ⟨i1, i1_post⟩
  step as ⟨i2, i2_post⟩
  have hi2 : i2.val = w.val % 128 := by rw [i2_post, cast_usize64 i1 (by scalar_tac), i1_post]
  clear i2_post
  step as ⟨e, e_post⟩
  all_goals try scalar_tac
  have he : e = table.val[w.val % 128]! := by
    rw [← hi2, getElem!_pos table.val i2.val (by scalar_tac)]; exact e_post
  step as ⟨i3, i3_post⟩
  step as ⟨sym, sym_post⟩
  have hsymv : sym.val = (table.val[w.val % 128]!).val / 64 % 512 := by rw [sym_post, i3_post, he]
  step as ⟨i5, i5_post⟩
  have hi5 : i5.val = cl.val.length := by
    rw [i5_post, UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  split
  · exact finish_correct s r cl codes table all total w nb c prev _ hinv1 ht hl hcl hcodes hentries hhints
  rename_i hsl
  have hsl' : sym.val < cl.val.length := by scalar_tac
  -- the symbol at the window's position
  have hP : wpos c nb = wpos cpos nbits := hpos1
  have hbw : ∀ k : Nat, k < 14 → bit_spec s.val (wpos c nb + k) ((w.val / 2 ^ k % 2 : Nat) : ℤ) :=
    fun k hk => window_bits _ _ _ _ hwin1.2.2.2 k (by omega) (by omega)
  have hwd := symbol_of_window s.val cl.val codes.val table.val false 7 128 (wpos c nb) w.val
    hentries hcodes hhints (by norm_num) (by norm_num) (fun k hk => hbw k (by omega))
    (by rw [← hsymv]; exact hsl')
  rw [← hsymv] at hwd
  obtain ⟨hsym, hn1, hn7, hent⟩ := hwd
  step as ⟨n, n_post⟩
  have hn : sym.val < 19 → (cl.val[sym.val]!).val = n.val := by
    intro h19
    have hent' : EntryOf false sym.val (cl.val[sym.val]!).val e.val := by rw [he]; exact hent
    have h256 : sym.val < 256 := by omega
    have hlt32 : (cl.val[sym.val]!).val < 32 := by omega
    obtain ⟨h32, _, _⟩ := literal_fields sym.val (cl.val[sym.val]!).val e.val hent' h256 hlt32
    rw [n_post, h32]
  have hn31 : n.val ≤ 31 := by rw [n_post]; omega
  step as ⟨i6, i6_post⟩
  all_goals try scalar_tac
  have hi6 : i6.val = w.val / 2 ^ n.val := by rw [i6_post, Nat.shiftRight_eq_div_pow]
  have hq : sym.val < 19 → ∀ k : Nat, k < 7 →
      bit_spec s.val (wpos c nb + n.val + k) ((i6.val / 2 ^ k % 2 : Nat) : ℤ) := by
    intro h19
    have hne := hn h19
    rw [hi6]
    exact window_shift s.val (wpos c nb) w.val n.val 7 (fun k hk => hbw k (by omega))
  have hbounds : ∀ j, j < all.val.length → (all.val[j]!).val ≤ 15 := hinvp.2.2.1
  step with (run_window_correct s (wpos c nb) cl sym n i6 (alloc.vec.Vec.deref all) hsym hn31 (fun h19 => by have := hn h19; omega) hn hq
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using hbounds)) as ⟨o, o_post⟩
  simp only [alloc.vec.Vec.deref, Slice.from_val] at o_post
  rcases o with _ | ⟨value1, count, bits⟩
  · -- no run: nothing parses from here
    simp only [RunWinPost] at o_post
    simp only
    rw [WP.spec_ok]
    simp only [LengthPost]
    intro all' j hall hpre hs
    obtain ⟨hpre2, hs2⟩ := hinvp.2.2.2.1 all' j hall hpre hs
    rw [← hP] at hs2
    have hlt2 : all.val.length < all'.length := by omega
    obtain ⟨v, m, a, hr, _⟩ := (lengths_unfold _ _ _ _ _ _ hlt2 hpre2).mp hs2
    exact o_post v m a hr
  simp only [RunWinPost] at o_post
  simp only
  obtain ⟨hc1, hc138, hv15, hnb, hb7, hb14, hrun⟩ := o_post
  step as ⟨i8, i8_post⟩
  all_goals try scalar_tac
  split
  · -- the run would overflow the table: nothing parses from here
    rename_i hover
    rw [WP.spec_ok]
    simp only [LengthPost]
    intro all' j hall hpre hs
    obtain ⟨hpre2, hs2⟩ := hinvp.2.2.2.1 all' j hall hpre hs
    rw [← hP] at hs2
    have hlt2 : all.val.length < all'.length := by omega
    have hstep := (lengths_step_iff s.val cl.val all.val all' (wpos c nb) (wpos c nb + bits.val) j
      value1 count.val hlt2 hpre2 (by omega) hrun).mp hs2
    have hfit := hstep.1
    scalar_tac
  rename_i hfits
  have hfit : all.val.length + count.val ≤ total.val := by scalar_tac
  step with (repeat_value_correct all value1 count (by omega)) as ⟨all1, hall1⟩
  step as ⟨buf1, buf1_post⟩
  step as ⟨nbits1, nbits1_post⟩
  all_goals try scalar_tac
  try rw [WP.spec_ok]
  try simp only
  obtain ⟨hwin2, hpos2⟩ := winv_skip s w buf1 nb nbits1 bits c hwin1 buf1_post (by scalar_tac)
    (by omega)
  have hstep := linvp_step s.val cl.val prev (pos r) total.val all.val (wpos c nb) value1 count.val
    bits.val (by rw [hP]; exact hinvp) hlt' hc1 hfit hv15 hrun
  refine ⟨⟨hwin2, ?_⟩, ?_⟩
  · try simp only
    rw [hpos2, hall1]
    exact hstep
  · try simp only
    rw [hall1, List.length_append, List.length_replicate]
    omega

theorem lengths_loop_correct (s : Aeneas.Std.Slice U8) (r : Reader) (cl : Aeneas.Std.Slice U8)
    (codes : Aeneas.Std.Slice U32) (table : Array U32 2048#usize) (total : Usize)
    (all : alloc.vec.Vec U8) (buf : U64) (nbits : U32) (cpos : Usize) (prev : List U8)
    (ht : total.val ≤ 320) (hl : cl.val.length ≤ 320)
    (hcl : ∀ j, j < cl.val.length → (cl.val[j]!).val ≤ 15)
    (hcodes : codes.val.length = cl.val.length) (hentries : Entries cl.val codes.val)
    (hhints : Hints cl.val codes.val table.val false 7)
    (hinv : LInv s cl.val prev (pos r) total.val (all, buf, nbits, cpos)) :
    read_lengths_fast_loop s r cl codes table all total buf nbits cpos ⦃ z =>
      LengthPost s r cl prev total.val z ⦄ := by
  unfold read_lengths_fast_loop
  apply loop.spec_decr_nat (fun (st : alloc.vec.Vec U8 × U64 × U32 × Usize) => total.val - st.1.val.length)
    (fun st => LInv s cl.val prev (pos r) total.val st)
  · rintro ⟨all', buf', nbits', cpos'⟩ hinv'
    apply WP.spec_mono (lengths_body s r cl codes table total all' buf' nbits' cpos' prev ht hl hcl
      hcodes hentries hhints hinv')
    intro z hz
    cases z <;> exact hz
  · exact hinv

@[step]
theorem read_lengths_fast_correct (s : Aeneas.Std.Slice U8) (r : Reader) (cl : Aeneas.Std.Slice U8)
    (codes : Aeneas.Std.Slice U32) (table : Array U32 2048#usize)
    (out : alloc.vec.Vec U8) (total : Usize) (h : Inv s r) (ho : out.val.length ≤ total.val)
    (hb : Bounds out.val) (ht : total.val ≤ 320) (hl : cl.val.length ≤ 320)
    (hcl : ∀ j, j < cl.val.length → (cl.val[j]!).val ≤ 15)
    (hcodes : codes.val.length = cl.val.length) (hentries : Entries cl.val codes.val)
    (hhints : Hints cl.val codes.val table.val false 7) :
    read_lengths_fast s r cl codes table out total ⦃ z => LengthPost s r cl out.val total.val z ⦄ := by
  unfold read_lengths_fast
  step with (window_at_correct s r h) as ⟨w0, nb0, c0, hwin0, hpos0⟩
  apply lengths_loop_correct s r cl codes table total out w0 nb0 c0 out.val ht hl hcl hcodes
    hentries hhints
  refine ⟨hwin0, ?_⟩
  simp only
  rw [hpos0]
  refine ⟨ho, by simp, hb, fun all j _ hpre hs => ⟨hpre, hs⟩, fun all j _ _ hs => hs⟩

end Gzip.Proofs.Decode.LengthsWindow
