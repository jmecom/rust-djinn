import Gzip.Proofs.Decode.ReaderImpl
import Gzip.Proofs.Decode.BaseImpl
import Gzip.Proofs.Decode.PeekFacts

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.BaseImpl Gzip.Proofs.Decode.PeekFacts

namespace Gzip.Proofs.Decode.PeekImpl

/-- What `peek` returns holds the next 17 bits of the stream, the first one lowest. -/
def PeekPost (s : Aeneas.Std.Slice U8) (r : Reader) (o : Option U32) : Prop := match o with
  | none => True
  | some p => r.byte.val + 3 ≤ s.val.length ∧ r.bit.val < 8 ∧
      ∀ k : Nat, k < 17 → bit_spec s.val (pos r + k) ((p.val / 2 ^ k % 2 : Nat) : ℤ)

@[step]
theorem peek_correct (s : Aeneas.Std.Slice U8) (r : Reader) :
    peek s r ⦃ o => PeekPost s r o ⦄ := by
  unfold peek
  step*
  all_goals try exact trivial
  all_goals
    have hb : r.byte.val + 3 ≤ s.val.length := by scalar_tac
    have hv4 : i4.val = i3.val := by rw [i4_post, cast_byte]
    have hv7 : i7.val = i6.val := by rw [i7_post, cast_byte]
    have hv12 : i12.val = i11.val := by rw [i12_post, cast_byte]
  have hi0 : i3 = s.val[r.byte.val]! := by rw [getElem!_pos _ _ (by omega)]; exact i3_post
  have hi1 : i6 = s.val[r.byte.val + 1]! := by
    rw [← i5_post, getElem!_pos _ _ (by omega)]; exact i6_post
  have hi2 : i11 = s.val[r.byte.val + 2]! := by
    rw [← i10_post, getElem!_pos _ _ (by omega)]; exact i11_post
  refine ⟨hb, by scalar_tac, ?_⟩
  intro k hk
  have hbit := peek_bit s.val r.byte.val (r.bit.val + k) hb (by scalar_tac)
  have hw : w.val = (s.val[r.byte.val]!).val + 256 * (s.val[r.byte.val + 1]!).val +
      65536 * (s.val[r.byte.val + 2]!).val := by
    rw [← hi0, ← hi1, ← hi2]; scalar_tac
  have hp : i14.val / 2 ^ k = w.val / 2 ^ (r.bit.val + k) := by
    rw [i14_post, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
  have hpos : pos r + (k : ℤ) = 8 * (r.byte.val : ℤ) + ((r.bit.val + k : Nat) : ℤ) := by
    unfold pos; push_cast; ring
  rw [hp, hw, hpos]
  exact hbit

@[step]
theorem skip_bits_correct (r : Reader) (n : U32)
    (hb : r.byte.val + 3 ≤ Usize.max) (hbit : r.bit.val < 8) (hn : n.val ≤ 16) :
    skip_bits r n ⦃ r1 => r1.byte.val ≤ r.byte.val + 2 ∧ r1.bit.val < 8 ∧
      pos r1 = pos r + n.val ⦄ := by
  unfold skip_bits
  step*
  have hi1 : i1.val = i.val := by
    rw [i1_post, UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  unfold pos
  simp only
  refine ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩

theorem skip_inv (s : Aeneas.Std.Slice U8) (r r1 : Reader)
    (hb : r.byte.val + 3 ≤ s.val.length) (h1 : r1.byte.val ≤ r.byte.val + 2)
    (h2 : r1.bit.val < 8) : Inv s r1 := by
  unfold ReaderImpl.Inv
  exact ⟨by omega, h2, by omega⟩

@[step]
theorem read_field_fast_correct (s : Aeneas.Std.Slice U8) (r : Reader) (n : U32)
    (h : Inv s r) (hn : n.val ≤ 31) : read_field_fast s r n ⦃ z => FieldPost s r n z ⦄ := by
  unfold read_field_fast
  step*
  · have hz : n.val = 0 := by scalar_tac
    simp only [FieldPost, Prod.fst, Prod.snd, UScalar.ofNatCore_val_eq]
    refine ⟨h, ?_, by simp, by decide⟩
    change field_spec s.val (pos r) 0 0
    rw [field_spec]
    simp [field_pre]
  all_goals simp only [PeekPost, show o = some p by assumption] at o_post
  all_goals try scalar_tac
  all_goals
    have hshift : i.val = 2 ^ n.val := by rw [i_post, shift_one _ (by scalar_tac)]
    have hpos : 0 < 2 ^ n.val := Nat.pos_of_ne_zero (by positivity)
  · omega
  have hfield := field_of_bits s.val n.val (pos r) p.val (fun k hk => o_post.2.2 k (by scalar_tac))
  have hlt : p.val % 2 ^ n.val < 2 ^ n.val := Nat.mod_lt _ hpos
  simp only [FieldPost]
  refine ⟨skip_inv s r r1 o_post.1 (by assumption) (by assumption), ?_, by assumption, ?_⟩
  · rw [i1_post, hshift]
    exact hfield
  · rw [i1_post, hshift]
    exact hlt

end Gzip.Proofs.Decode.PeekImpl
