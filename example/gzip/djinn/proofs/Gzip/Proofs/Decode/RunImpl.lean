import Gzip.Proofs.Decode.SymbolsImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.SymbolImpl Gzip.Proofs.Decode.BaseImpl
open Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.RoundTrip
open Gzip.Proofs.Decode.CodewordTable Gzip.Proofs.Decode.DecodeTable Gzip.Proofs.Decode.FastSymbol

namespace Gzip.Proofs.Decode.RunImpl

def RunKind (s prev : List U8) (a sym : ℤ) (value : U8) (count j : ℤ) : Prop :=
  if sym < 16 then (value.val : ℤ) = sym ∧ count = 1 ∧ j = a
  else if sym = 16 then 1 ≤ prev.length ∧ value = prev[prev.length - 1]! ∧
    ∃ v, field_spec s a 2 v ∧ count = 3 + v ∧ j = a + 2
  else if sym = 17 then value.val = 0 ∧ ∃ v, field_spec s a 3 v ∧ count = 3 + v ∧ j = a + 3
  else sym = 18 ∧ value.val = 0 ∧ ∃ v, field_spec s a 7 v ∧ count = 11 + v ∧ j = a + 7

def RunSpec (s cl prev : List U8) (i : ℤ) (value : U8) (count j : ℤ) : Prop :=
  ∃ sym a, symbol_spec s i cl sym ∧ a = i + (cl[sym.toNat]!).val ∧ RunKind s prev a sym value count j

theorem run_at (s cl prev : List U8) (i a sym : ℤ) (value : U8) (count j : ℤ)
    (hs : symbol_spec s i cl sym) (ha : a = i + (cl[sym.toNat]!).val) :
    RunSpec s cl prev i value count j ↔ RunKind s prev a sym value count j := by
  constructor
  · rintro ⟨sym', a', hs', ha', hr⟩
    have he := Huffman.symbol_unique _ _ _ _ _ hs hs'
    rw [← he] at ha' hr
    have he' : a' = a := ha'.trans ha.symm
    rwa [he'] at hr
  · intro hr; exact ⟨sym, a, hs, ha, hr⟩

theorem cast_usize (v : U32) : (UScalar.cast .Usize v).val = v.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

def RunPost (s : Aeneas.Std.Slice U8) (r : Reader) (cl prev : Aeneas.Std.Slice U8)
    (z : Option (U8 × Usize) × Reader) : Prop := match z.1 with
  | none => ∀ value count j, ¬ RunSpec s.val cl.val prev.val (pos r) value count j
  | some (value, count) => Inv s z.2 ∧ 1 ≤ count.val ∧ count.val ≤ 138 ∧ value.val ≤ 15 ∧
      RunSpec s.val cl.val prev.val (pos r) value count.val (pos z.2)

@[step]
theorem read_length_run_correct (s : Aeneas.Std.Slice U8) (r : Reader) (cl : Aeneas.Std.Slice U8)
    (codes : Aeneas.Std.Slice U32) (table : Array U32 2048#usize) (prev : Aeneas.Std.Slice U8)
    (h : Inv s r) (hl : cl.val.length ≤ 320)
    (hb : ∀ j, j < cl.val.length → (cl.val[j]!).val ≤ 15)
    (hcodes : codes.val.length = cl.val.length) (hentries : Entries cl.val codes.val)
    (hhints : Hints cl.val codes.val table.val false 7)
    (hp : ∀ j, j < prev.val.length → (prev.val[j]!).val ≤ 15) :
    read_length_run s r cl codes table prev ⦃ z => RunPost s r cl prev z ⦄ := by
  have hmask : (127#u32).val = 2 ^ 7 - 1 := by simp
  have hb7 : (7 : Nat) ≤ 11 := by norm_num
  unfold read_length_run
  step*
  all_goals try simp only [SymbolPost, show o = some value by assumption] at o_post
  all_goals try simp only [SymbolPost, show o = none by assumption] at o_post
  all_goals try simp only [FieldPost, show o1 = some value1 by assumption] at o1_post
  all_goals try simp only [FieldPost, show o1 = none by assumption] at o1_post
  all_goals try exact o_post.1
  all_goals try (have hv := o1_post.2.2.2; norm_num at hv)
  all_goals try (have hcast : i4.val = value1.val := by rw [i4_post, cast_usize])
  all_goals try (have hcast : i.val = value1.val := by rw [i_post, cast_usize])
  all_goals try scalar_tac
  · intro v n j hs
    obtain ⟨sym, a, hs, _⟩ := hs
    exact o_post.2 sym (by have hp := hs.2.1; omega) hs
  all_goals
    have hview (v : U8) (n j : ℤ) := run_at s.val cl.val prev.val (pos r) (pos r1) value.val v n j
      o_post.2.2.1 (by simpa only [Int.toNat_natCast] using o_post.2.2.2)
  · have hi : i.val = value.val := by
      rw [i_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
    refine ⟨o_post.1, by decide, by decide, by scalar_tac, (hview _ _ _).mpr ?_⟩
    simp only [RunKind, if_pos (by scalar_tac : (value.val : ℤ) < 16)]
    exact ⟨by omega, rfl, trivial⟩
  · intro v n j hs
    rw [hview] at hs
    have he : (value.val : ℤ) = 16 := by scalar_tac
    simp only [RunKind, he] at hs
    norm_num at hs
    scalar_tac
  · intro v n j hs
    rw [hview] at hs
    have he : (value.val : ℤ) = 16 := by scalar_tac
    norm_num only [RunKind, he] at hs
    obtain ⟨_, _, v', hv', _⟩ := hs
    exact o1_post.2 v' hv'
  · have hi : i3 = prev.val[prev.val.length - 1]! := by
      have hiidx : i2.val = prev.val.length - 1 := by scalar_tac
      rw [← hiidx, getElem!_pos prev.val _ (by scalar_tac)]
      exact i3_post
    have hip := hp (prev.val.length - 1) (by scalar_tac)
    refine ⟨o1_post.1, by scalar_tac, by scalar_tac, by rw [hi]; exact hip, (hview _ _ _).mpr ?_⟩
    have he : (value.val : ℤ) = 16 := by scalar_tac
    norm_num only [RunKind, he]
    exact ⟨by scalar_tac, hi, value1.val, o1_post.2.1, by scalar_tac, o1_post.2.2.1⟩
  · intro v n j hs
    rw [hview] at hs
    have he : (value.val : ℤ) = 17 := by scalar_tac
    norm_num only [RunKind, he] at hs
    obtain ⟨_, v', hv', _⟩ := hs
    exact o1_post.2 v' hv'
  · refine ⟨o1_post.1, by scalar_tac, by scalar_tac, by decide, (hview _ _ _).mpr ?_⟩
    have he : (value.val : ℤ) = 17 := by scalar_tac
    norm_num only [RunKind, he]
    exact ⟨rfl, value1.val, o1_post.2.1, by scalar_tac, o1_post.2.2.1⟩
  · intro v n j hs
    rw [hview] at hs
    have he : (value.val : ℤ) = 18 := by scalar_tac
    norm_num only [RunKind, he] at hs
    obtain ⟨_, _, v', hv', _⟩ := hs
    exact o1_post.2 v' hv'
  · refine ⟨o1_post.1, by scalar_tac, by scalar_tac, by decide, (hview _ _ _).mpr ?_⟩
    have he : (value.val : ℤ) = 18 := by scalar_tac
    norm_num only [RunKind, he]
    exact ⟨trivial, rfl, value1.val, o1_post.2.1, by scalar_tac, o1_post.2.2.1⟩
  · intro v n j hs
    rw [hview] at hs
    unfold RunKind at hs
    split_ifs at hs <;> scalar_tac

end Gzip.Proofs.Decode.RunImpl
