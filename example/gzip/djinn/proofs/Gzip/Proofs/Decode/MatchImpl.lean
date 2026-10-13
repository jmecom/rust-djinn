import Gzip.Proofs.Decode.FastSymbol
import Gzip.Proofs.Decode.CopyImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.BaseImpl Gzip.Proofs.Decode.CodewordImpl Gzip.Proofs.Decode.SymbolImpl
open Gzip.Proofs.Decode.FastSymbol Gzip.Proofs.Decode.DecodeTable Gzip.Proofs.Decode.PeekImpl
open Gzip.Proofs.Decode.CodewordTable
open Gzip.Proofs.Decode.Decoding Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.RoundTrip

namespace Gzip.Proofs.Decode.MatchImpl

def MatchSpec (s : List U8) (i : ℤ) (dist : List U8) (lc len d j : ℤ) : Prop :=
  ∃ b dc,
    (∃ lb, lbase_spec lc lb ∧ ∃ le, lextra_spec lc le ∧ ∃ v, field_spec s i le v ∧ len = lb + v) ∧
    (∃ le, lextra_spec lc le ∧ b = i + le) ∧
    symbol_spec s b dist dc ∧
    (∃ db, dbase_spec dc db ∧ ∃ de, dextra_spec dc de ∧
      ∃ v, field_spec s (b + (dist[dc.toNat]!).val) de v ∧ d = db + v) ∧
    (∃ de, dextra_spec dc de ∧ j = b + (dist[dc.toNat]!).val + de)

def MatchPost (s : Aeneas.Std.Slice U8) (r : Reader) (dist : Aeneas.Std.Slice U8) (lc : U32)
    (z : Option (Usize × Usize) × Reader) : Prop := match z.1 with
  | none => ∀ len d j, ¬ MatchSpec s.val (pos r) dist.val lc.val len d j
  | some (len, d) => Inv s z.2 ∧ 3 ≤ len.val ∧ 1 ≤ d.val ∧ pos r < pos z.2 ∧
      MatchSpec s.val (pos r) dist.val lc.val len.val d.val (pos z.2) ∧ len.val ≤ 289

@[step]
theorem read_match_correct (s : Aeneas.Std.Slice U8) (r : Reader) (dist : Aeneas.Std.Slice U8)
    (codes : Aeneas.Std.Slice U32) (table : Array U32 2048#usize) (isd : Bool)
    (ht : Hints dist.val codes.val table.val isd 10) (hlen : codes.val.length = dist.val.length) (htable : Entries dist.val codes.val)
    (lc : U32) (h : Inv s r) (hl : dist.val.length ≤ 320)
    (hb : ∀ j, j < dist.val.length → (dist.val[j]!).val ≤ 15) (hc : lc.val ≤ 28) :
    read_match s r dist codes table lc ⦃ z => MatchPost s r dist lc z ⦄ := by
  -- the distance table has ten index bits
  have hmask : (1023#u32).val = 2 ^ 10 - 1 := by simp
  have hb10 : (10 : Nat) ≤ 11 := by norm_num
  unfold read_match
  step*
  all_goals try simp only [FieldPost, show o = some value by assumption] at o_post
  all_goals try simp only [FieldPost, show o = none by assumption] at o_post
  all_goals try simp only [SymbolPost, show o1 = some value1 by assumption] at o1_post
  all_goals try simp only [SymbolPost, show o1 = none by assumption] at o1_post
  all_goals try simp only [FieldPost, show o2 = some value2 by assumption] at o2_post
  all_goals try simp only [FieldPost, show o2 = none by assumption] at o2_post
  all_goals try exact o_post.1
  all_goals try exact o1_post.1
  all_goals try (
    have hv := o_post.2.2.2
    have hp := pow_two_le i1.val (by omega)
    scalar_tac)
  all_goals try (
    have hv := o2_post.2.2.2
    have hp := pow_two_le i4.val (by omega)
    scalar_tac)
  · intro len' d' j' hs
    obtain ⟨b, dc, ⟨lb, hlb, le, hle, v, hf, he⟩, _⟩ := hs
    have heq := lextra_unique _ _ _ i1_post hle
    apply o_post.2 v
    rwa [heq]
  · intro len' d' j' hs
    obtain ⟨b, dc, _, ⟨le, hle, he⟩, hdc, _⟩ := hs
    have heq := lextra_unique _ _ _ i1_post hle
    have hpos : b = pos r1 := by omega
    rw [hpos] at hdc
    exact o1_post.2 dc (by have hd := hdc.2.1; omega) hdc
  · intro len' d' j' hs
    obtain ⟨b, dc, _, ⟨le, hle, he⟩, hdc, ⟨db, hdb, _⟩, _⟩ := hs
    have heq := lextra_unique _ _ _ i1_post hle
    have hpos : b = pos r1 := by omega
    rw [hpos] at hdc
    have hsym := Huffman.symbol_unique _ _ _ _ _ o1_post.2.2.1 hdc
    rw [dbase_spec] at hdb
    have hdc29 := (hdb.2 hdb.1).1
    scalar_tac
  · intro len' d' j' hs
    obtain ⟨b, dc, _, ⟨le, hle, he⟩, hdc, ⟨db, hdb, de, hde, v, hf, hd⟩, _⟩ := hs
    have heq := lextra_unique _ _ _ i1_post hle
    have hpos : b = pos r1 := by omega
    rw [hpos] at hdc hf
    have hsym := Huffman.symbol_unique _ _ _ _ _ o1_post.2.2.1 hdc
    rw [← hsym] at hde hf
    have heq' := dextra_unique _ _ _ i4_post hde
    apply o2_post.2 v
    rw [heq']
    have hpos' : pos r2 = pos r1 + (dist.val[(value1.val : ℤ).toNat]!).val := by
      simpa only [Int.toNat_natCast] using o1_post.2.2.2
    rwa [hpos']
  · have hlen : len.val = i2.val := by
      rw [len_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
    have hd : d.val = i5.val := by
      rw [d_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
    refine ⟨o2_post.1, by omega, by omega, ?_, ?_, ?_⟩
    rotate_right
    · -- the length is the base (at most 258) plus at most five extra bits
      have hv := o_post.2.2.2
      have hp : 2 ^ i1.val ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) i1_post1
      scalar_tac
    · change pos r < pos r3
      have hstep := symbol_bounds _ _ _ _ o1_post.2.2.1
      have hp := o1_post.2.2.2
      simp only [Int.toNat_natCast] at hstep
      omega
    · refine ⟨pos r1, value1.val, ?_, ?_, o1_post.2.2.1, ?_, ?_⟩
      · exact ⟨i.val, i_post, i1.val, i1_post, value.val, o_post.2.1, by omega⟩
      · exact ⟨i1.val, i1_post, o_post.2.2.1⟩
      · refine ⟨i3.val, i3_post, i4.val, i4_post, value2.val, ?_, by omega⟩
        simpa only [Int.toNat_natCast, ← o1_post.2.2.2] using o2_post.2.1
      · refine ⟨i4.val, i4_post, ?_⟩
        simp only [Int.toNat_natCast]
        omega

end Gzip.Proofs.Decode.MatchImpl
