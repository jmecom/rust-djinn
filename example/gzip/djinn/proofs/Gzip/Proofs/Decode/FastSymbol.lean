import Gzip.Proofs.Decode.SymbolImpl
import Gzip.Proofs.Decode.DecodeTable
import Gzip.Proofs.Decode.PeekImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.BaseImpl Gzip.Proofs.Decode.CodewordTable
open Gzip.Proofs.Decode.SymbolImpl Gzip.Proofs.Decode.DecodeTable Gzip.Proofs.Decode.PeekImpl

namespace Gzip.Proofs.Decode.FastSymbol

/-- `find_long` only proposes a symbol, so all it owes is to return. -/
theorem find_long_body (lens : Aeneas.Std.Slice U8) (codes : Aeneas.Std.Slice U32) (rv : U32)
    (sym : Usize) :
    find_long_loop.body lens codes rv sym ⦃ z => match z with
      | .done _ => True
      | .cont sym1 => True ∧ lens.val.length - sym1.val < lens.val.length - sym.val ⦄ := by
  unfold find_long_loop.body
  step*

@[step]
theorem find_long_loop_correct (lens : Aeneas.Std.Slice U8) (codes : Aeneas.Std.Slice U32)
    (rv : U32) (sym : Usize) : find_long_loop lens codes rv sym ⦃ _ => True ⦄ := by
  unfold find_long_loop
  apply loop.spec_decr_nat (fun sym => lens.val.length - sym.val) (fun _ => True)
  · intro sym1 _
    apply WP.spec_mono (find_long_body lens codes rv sym1)
    intro z hz
    cases z <;> exact hz
  · trivial

@[step]
theorem find_long_correct (lens : Aeneas.Std.Slice U8) (codes : Aeneas.Std.Slice U32) (p : U32) :
    find_long lens codes p ⦃ _ => True ⦄ := by
  unfold find_long
  step*

/-- The hinted symbol is taken only when the stream starts with its codeword; otherwise the
symbol search decides, as before. -/
@[step]
theorem read_symbol_slow_correct (s : Aeneas.Std.Slice U8) (r : Reader)
    (lens : Aeneas.Std.Slice U8) (codes : Aeneas.Std.Slice U32)
    (h : Inv s r) (hl : lens.val.length ≤ 320)
    (hb : ∀ j, j < lens.val.length → (lens.val[j]!).val ≤ 15)
    (hlen : codes.val.length = lens.val.length) (htable : Entries lens.val codes.val) :
    read_symbol_slow s r lens codes ⦃ z => SymbolPost s r lens 0 z ⦄ := by
  unfold read_symbol_slow
  step*
  all_goals simp only [PeekPost, show o = some p by assumption] at o_post
  all_goals try scalar_tac
  have hsym : sym.val < lens.val.length := by scalar_tac
  have hn : n.val = (lens.val[sym.val]!).val := by
    rw [n_post, cast_byte, i2_post, getElem!_pos lens.val sym.val hsym]
  have hi5 : i5.val = sym.val := by
    rw [i5_post, UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  have hcode := PeekFacts.code_of_bits s.val (pos r) p.val n.val
    (fun k hk => o_post.2.2 k (by scalar_tac))
  have hrev : PeekFacts.rev p.val n.val = (codes.val[sym.val]!).val := by
    rw [← i3_post, show i3 = i4 by assumption, i4_post,
      getElem!_pos codes.val sym.val (by scalar_tac)]
  simp only [SymbolPost]
  refine ⟨skip_inv s r r1 o_post.1 (by assumption) (by assumption), by omega, ?_, ?_⟩
  · rw [hi5]
    refine ⟨trivial, ⟨by omega, by omega⟩, ?_, (codes.val[sym.val]!).val,
      htable sym.val (by omega), ?_⟩
    · simp only [Int.toNat_natCast]
      scalar_tac
    · simp only [Int.toNat_natCast, ← hn, ← hrev]
      exact hcode
  · rw [hi5, ← hn]
    assumption

-- The table lookup with the index masked to the table's `bits`: the entry at the stream's
-- first `bits` bits.
set_option maxHeartbeats 2000000 in
@[step]
theorem read_symbol_fast_correct(s : Aeneas.Std.Slice U8) (r : Reader)
    (lens : Aeneas.Std.Slice U8) (codes : Aeneas.Std.Slice U32) (table : Array U32 2048#usize)
    (mask : U32) (isd : Bool) (bits : Nat)
    (h : Inv s r) (hl : lens.val.length ≤ 320)
    (hb : ∀ j, j < lens.val.length → (lens.val[j]!).val ≤ 15)
    (hlen : codes.val.length = lens.val.length) (htable : Entries lens.val codes.val)
    (hbits : bits ≤ 11) (hmask : mask.val = 2 ^ bits - 1)
    (ht : Hints lens.val codes.val table.val isd bits) :
    read_symbol_fast s r lens codes table mask ⦃ z => SymbolPost s r lens 0 z ⦄ := by
  have htl := ht.1
  have hpb : 2 ^ bits ≤ 2048 := calc
    _ ≤ 2 ^ 11 := Nat.pow_le_pow_right (by omega) hbits
    _ = _ := by norm_num
  unfold read_symbol_fast
  step*
  all_goals simp only [PeekPost, show o = some p by assumption] at o_post
  all_goals try scalar_tac
  all_goals
    have hi1 : i1.val = p.val % 2 ^ bits := by
      have h1 : i1.val = i.val &&& mask.val := by simpa using i1_post
      rw [h1, i_post, hmask, Nat.and_two_pow_sub_one_eq_mod, show (2048 : Nat) = 2 ^ 11 by norm_num]
      exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hbits)
    have hi1lt : i1.val < 2048 := by
      rw [hi1]
      exact _root_.lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hpb
    have hi2 : i2.val = i1.val := by
      rw [i2_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
  -- the lookup's bounds goal
  all_goals try scalar_tac
  all_goals
    have hidx : i2.val < 2048 := by omega
    have hi3 : i3 = table.val[i2.val]! := by
      rw [getElem!_pos table.val i2.val (by omega)]
      exact i3_post
    have hsymv : sym.val = (table.val[i2.val]!).val / 64 % 512 := by
      rw [← hi3, ← i4_post, ← i5_post, sym_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
    have hsym : sym.val < lens.val.length := by scalar_tac
    have hidxb : i2.val < 2 ^ bits := by
      rw [hi2, hi1]
      exact Nat.mod_lt _ (by positivity)
    have hhint := ht.2.1 i2.val hidxb (by omega)
    rw [← hsymv] at hhint
    have hh1 := hhint.1
    have hh11 := hhint.2.1
    have hhrev := Keep.intro hhint.2.2.1
    clear hhint
    have hn : i8.val = (lens.val[sym.val]!).val := by
      rw [i8_post, cast_byte, i7_post, getElem!_pos lens.val sym.val hsym]
  · omega
  have hi9 : i9.val = sym.val := by
    clear hhrev hh1 hh11 hn hsymv i5_post i4_post hi3 i3_post hidx hi2 hi1 i1_post hi1lt
    rw [i9_post, UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  have hcode := PeekFacts.code_of_bits s.val (pos r) p.val i8.val
    (fun k hk => o_post.2.2 k (by omega))
  have hrev : PeekFacts.rev p.val i8.val = (codes.val[sym.val]!).val := by
    rw [← hhrev.out, ← hn, ← PeekFacts.rev_mod p.val bits i8.val (by omega)]
    congr 1
    rw [hi2, hi1]
  simp only [SymbolPost]
  refine ⟨skip_inv s r r1 o_post.1 (by assumption) (by assumption), by omega, ?_, ?_⟩
  · rw [hi9]
    refine ⟨trivial, ⟨by omega, by omega⟩, ?_, (codes.val[sym.val]!).val,
      htable sym.val (by omega), ?_⟩
    · simp only [Int.toNat_natCast]
      omega
    · simp only [Int.toNat_natCast, ← hn, ← hrev]
      exact hcode
  · rw [hi9, ← hn]
    assumption

end Gzip.Proofs.Decode.FastSymbol
