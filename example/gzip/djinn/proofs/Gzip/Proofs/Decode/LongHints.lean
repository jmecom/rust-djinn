import Gzip.Proofs.Decode.FastSymbol

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.BaseImpl Gzip.Proofs.Decode.CodewordTable
open Gzip.Proofs.Decode.SymbolImpl Gzip.Proofs.Decode.DecodeTable Gzip.Proofs.Decode.PeekImpl
open Gzip.Proofs.Decode.FastSymbol

namespace Gzip.Proofs.Decode.LongHints

/-! The cache is only a source of candidate symbols. Its construction owes termination and
bounds safety; the decoder validates every candidate before changing the reader. -/

theorem hints_fill_body (sym step : Usize) (hints : Array U16 512#usize) (k : Usize)
    (hs : 1 ≤ step.val) (hb : step.val ≤ 32768) :
    long_hints_loop0_loop0.body sym step hints k ⦃ z => match z with
      | .done _ => True
      | .cont (_, k1) => True ∧ 32768 - k1.val < 32768 - k.val ⦄ := by
  unfold long_hints_loop0_loop0.body
  step*
  all_goals try scalar_tac

@[step]
theorem hints_fill_correct (sym step : Usize) (hints : Array U16 512#usize) (k : Usize)
    (hs : 1 ≤ step.val) (hb : step.val ≤ 32768) :
    long_hints_loop0_loop0 hints sym step k ⦃ _ => True ⦄ := by
  unfold long_hints_loop0_loop0
  apply loop.spec_decr_nat (fun (_, k) => 32768 - k.val) (fun _ => True)
  · rintro ⟨hints1, k1⟩ _
    apply WP.spec_mono (hints_fill_body sym step hints1 k1 hs hb)
    intro z hz
    cases z <;> exact hz
  · trivial

theorem shift_usize_one (n : Nat) (hn : n ≤ 16) :
    1 <<< n % Usize.size = 2 ^ n := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt]
  have hb := pow_two_le n hn
  scalar_tac

theorem hints_build_body (lens : Aeneas.Std.Slice U8) (codes : Aeneas.Std.Slice U32)
    (r : Array U8 256#usize) (hints : Array U16 512#usize) (sym : Usize)
    (hr : RevTab r.val 256) :
    long_hints_loop0.body lens codes r hints sym ⦃ z => match z with
      | .done _ => True
      | .cont (_, sym1) => True ∧ 320 - sym1.val < 320 - sym.val ⦄ := by
  unfold long_hints_loop0.body
  step*
  all_goals try scalar_tac
  · rcases System.Platform.numBits_eq with hbits | hbits <;> rw [hbits] <;> scalar_tac
  · rw [step_post, shift_usize_one n.val (by scalar_tac)]
    have hp : 0 < 2 ^ n.val := Nat.pow_pos (by omega)
    omega
  · rw [step_post, shift_usize_one n.val (by scalar_tac)]
    calc
      _ ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by scalar_tac)
      _ = _ := by norm_num

@[step]
theorem hints_build_correct (lens : Aeneas.Std.Slice U8) (codes : Aeneas.Std.Slice U32)
    (r : Array U8 256#usize) (hints : Array U16 512#usize) (sym : Usize)
    (hr : RevTab r.val 256) :
    long_hints_loop0 lens codes r hints sym ⦃ _ => True ⦄ := by
  unfold long_hints_loop0
  apply loop.spec_decr_nat (fun (_, sym) => 320 - sym.val) (fun _ => True)
  · rintro ⟨hints1, sym1⟩ _
    apply WP.spec_mono (hints_build_body lens codes r hints1 sym1 hr)
    intro z hz
    cases z <;> exact hz
  · trivial

/-- The cache from a given reversal table. -/
@[step]
theorem long_hints_correct (lens : Aeneas.Std.Slice U8) (codes : Aeneas.Std.Slice U32)
    (r : Array U8 256#usize) (hr : RevTab r.val 256) :
    long_hints lens codes r ⦃ _ => True ⦄ := by
  unfold long_hints
  exact hints_build_correct lens codes r _ 0#usize hr

set_option maxHeartbeats 2000000 in
@[step]
theorem read_symbol_hinted_correct (s : Aeneas.Std.Slice U8) (r : Reader)
    (lens : Aeneas.Std.Slice U8) (codes : Aeneas.Std.Slice U32) (table : Array U32 2048#usize)
    (hints : Array U16 512#usize) (isd : Bool)
    (h : Inv s r) (hl : lens.val.length ≤ 320)
    (hb : ∀ j, j < lens.val.length → (lens.val[j]!).val ≤ 15)
    (hlen : codes.val.length = lens.val.length) (htable : Entries lens.val codes.val)
    (ht : Hints lens.val codes.val table.val isd 11) :
    read_symbol_hinted s r lens codes table hints ⦃ z => SymbolPost s r lens 0 z ⦄ := by
  have hmask : (2047#u32).val = 2 ^ 11 - 1 := by simp
  have hb11 : (11 : Nat) ≤ 11 := Nat.le_refl _
  unfold read_symbol_hinted
  step*
  all_goals simp only [PeekPost, show o = some p by assumption] at o_post
  all_goals try scalar_tac
  have hsym : sym.val < lens.val.length := by scalar_tac
  have hn : n.val = (lens.val[sym.val]!).val := by
    rw [n_post, cast_byte, i6_post, getElem!_pos lens.val sym.val hsym]
  have hi9 : i9.val = sym.val := by
    rw [i9_post, UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  have hcode := PeekFacts.code_of_bits s.val (pos r) p.val n.val
    (fun k hk => o_post.2.2 k (by scalar_tac))
  have hrev : PeekFacts.rev p.val n.val = (codes.val[sym.val]!).val := by
    rw [← i7_post, show i7 = i8 by assumption, i8_post,
      getElem!_pos codes.val sym.val (by scalar_tac)]
  simp only [SymbolPost]
  refine ⟨skip_inv s r r1 o_post.1 (by assumption) (by assumption), by omega, ?_, ?_⟩
  · rw [hi9]
    refine ⟨trivial, ⟨by omega, by omega⟩, ?_, (codes.val[sym.val]!).val,
      htable sym.val (by omega), ?_⟩
    · simp only [Int.toNat_natCast]
      scalar_tac
    · simp only [Int.toNat_natCast, ← hn, ← hrev]
      exact hcode
  · rw [hi9, ← hn]
    assumption

end Gzip.Proofs.Decode.LongHints
