import Gzip.Code.Funs
import Gzip.Proofs.Decode.WideFacts

/-! # Eight bytes at a time through subslices

`load8`, `load8s` and `store8` take their eight bytes through one range index (`&v[i..i + 8]`),
so that a single bounds check covers them and the compiler keeps the load or store whole. The
range index is modeled by `List.slice`, the write-back of a mutable range by `List.setSlice!`,
and `copy_from_slice` yields its source. -/

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.WideFacts

namespace Gzip.Proofs.Decode.SubsliceImpl

/-- A range of eight elements of a vector, read through `Index<Range<usize>>`. -/
@[step]
theorem vec_range8 (v : alloc.vec.Vec U8) (i i1 : Usize) (h : i1.val = i.val + 8)
    (hb : i.val + 8 ≤ v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8) v { start := i, «end» := i1 }
      ⦃ b => b.val.length = 8 ∧ ∀ k, k < 8 → b.val[k]! = v.val[i.val + k]! ⦄ := by
  have hv : v.slice.val.length = v.val.length := rfl
  unfold alloc.vec.Vec.index
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index]
  split
  · rw [WP.spec_ok]
    simp only [Slice.from_val, List.slice_length]
    refine ⟨by omega, ?_⟩
    intro k hk
    rw [List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩]
    rfl
  · exfalso
    rename_i hc
    apply hc
    refine ⟨?_, ?_⟩
    · rw [UScalar.le_equiv]; omega
    · simp only [Slice.length]; omega

/-- A range of eight elements of a vector, borrowed mutably: writing a slice back through the
back function replaces those eight elements. -/
@[step]
theorem vec_range8_mut (v : alloc.vec.Vec U8) (i i1 : Usize) (h : i1.val = i.val + 8)
    (hb : i.val + 8 ≤ v.val.length) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8) v { start := i, «end» := i1 }
      ⦃ b back => b.val.length = 8 ∧ (∀ k, k < 8 → b.val[k]! = v.val[i.val + k]!) ∧
        ∀ s', (back s').val = v.val.setSlice! i.val s'.val ⦄ := by
  have hv : v.slice.val.length = v.val.length := rfl
  unfold alloc.vec.Vec.index_mut
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index_mut]
  split
  · step*
    first
    | (show Result.ok _ ⦃ _ ⦄
       rw [WP.spec_ok])
    | (rw [WP.spec_equiv_exists]
       refine ⟨_, rfl, ?_⟩)
    simp only [WP.uncurry', Slice.from_val, List.slice_length]
    refine ⟨by omega, ?_, ?_⟩
    · intro k hk
      rw [List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩]
      rfl
    · intro s'
      simp only [alloc.vec.Vec.val, Slice.from_val]
  · exfalso
    rename_i hc
    apply hc
    refine ⟨?_, ?_⟩
    · rw [UScalar.le_equiv]; omega
    · simp only [Slice.length]; omega

/-- Any range of a vector, borrowed mutably: the subslice's elements and the write-back. Not a
`step` lemma, so that `vec_range8_mut` keeps serving the eight-byte ranges; use it with
`step with`. -/
theorem vec_range_mut (v : alloc.vec.Vec U8) (i j : Usize) (h : i.val ≤ j.val)
    (hb : j.val ≤ v.val.length) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8) v { start := i, «end» := j }
      ⦃ b back => b.val.length = j.val - i.val ∧ (∀ k, k < j.val - i.val → b.val[k]! = v.val[i.val + k]!) ∧
        ∀ s', (back s').val = v.val.setSlice! i.val s'.val ⦄ := by
  have hv : v.slice.val.length = v.val.length := rfl
  unfold alloc.vec.Vec.index_mut
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index_mut]
  split
  · step*
    first
    | (show Result.ok _ ⦃ _ ⦄
       rw [WP.spec_ok])
    | (rw [WP.spec_equiv_exists]
       refine ⟨_, rfl, ?_⟩)
    simp only [WP.uncurry', Slice.from_val, List.slice_length]
    refine ⟨by omega, ?_, ?_⟩
    · intro k hk
      rw [List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩]
      rfl
    · intro s'
      simp only [alloc.vec.Vec.val, Slice.from_val]
  · exfalso
    rename_i hc
    apply hc
    refine ⟨?_, ?_⟩
    · rw [UScalar.le_equiv]; omega
    · simp only [Slice.length]; omega

/-- `copy_from_slice` between slices of the same length yields the source. -/
@[step]
theorem copy_from_slice_eq (s s1 : Aeneas.Std.Slice U8) (h : s.val.length = s1.val.length) :
    core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1 ⦃ r => r = s1 ⦄ := by
  unfold core.slice.Slice.copy_from_slice
  split <;> step*

theorem cast_byte64 (x : U8) : (UScalar.cast .U64 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

theorem cast_u8_of_lt (x : U64) (h : x.val < 256) : (UScalar.cast .U8 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

/-- `load8s` reads eight bytes as a little-endian number. -/
@[step]
theorem load8s_correct (s : Aeneas.Std.Slice U8) (i : Usize) (hb : i.val + 8 ≤ s.val.length) :
    load8s s i ⦃ w => w.val = le [(s.val[i.val]!).val, (s.val[i.val + 1]!).val,
      (s.val[i.val + 2]!).val, (s.val[i.val + 3]!).val, (s.val[i.val + 4]!).val,
      (s.val[i.val + 5]!).val, (s.val[i.val + 6]!).val, (s.val[i.val + 7]!).val] ⦄ := by
  unfold load8s
  step*
  have hb8 : b.val.length = 8 := by rw [b_post, List.slice_length]; omega
  have hk : ∀ k, k < 8 → b.val[k]! = s.val[i.val + k]! := by
    intro k hk
    rw [b_post, List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩]
  have e0 : i2 = s.val[i.val]! := by
    have h0 := hk 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [← h0, getElem!_pos _ _ (by omega)]; exact i2_post
  have e1 : i4 = s.val[i.val + 1]! := by
    rw [← hk 1 (by omega), getElem!_pos _ _ (by omega)]; exact i4_post
  have e2 : i8 = s.val[i.val + 2]! := by
    rw [← hk 2 (by omega), getElem!_pos _ _ (by omega)]; exact i8_post
  have e3 : i12 = s.val[i.val + 3]! := by
    rw [← hk 3 (by omega), getElem!_pos _ _ (by omega)]; exact i12_post
  have e4 : i16 = s.val[i.val + 4]! := by
    rw [← hk 4 (by omega), getElem!_pos _ _ (by omega)]; exact i16_post
  have e5 : i20 = s.val[i.val + 5]! := by
    rw [← hk 5 (by omega), getElem!_pos _ _ (by omega)]; exact i20_post
  have e6 : i24 = s.val[i.val + 6]! := by
    rw [← hk 6 (by omega), getElem!_pos _ _ (by omega)]; exact i24_post
  have e7 : i28 = s.val[i.val + 7]! := by
    rw [← hk 7 (by omega), getElem!_pos _ _ (by omega)]; exact i28_post
  have hv3 : i3.val = i2.val := by rw [i3_post, cast_byte64]
  have hv5 : i5.val = i4.val := by rw [i5_post, cast_byte64]
  have hv9 : i9.val = i8.val := by rw [i9_post, cast_byte64]
  have hv13 : i13.val = i12.val := by rw [i13_post, cast_byte64]
  have hv17 : i17.val = i16.val := by rw [i17_post, cast_byte64]
  have hv21 : i21.val = i20.val := by rw [i21_post, cast_byte64]
  have hv25 : i25.val = i24.val := by rw [i25_post, cast_byte64]
  have hv29 : i29.val = i28.val := by rw [i29_post, cast_byte64]
  rw [← e0, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7]
  simp only [le]
  scalar_tac

/-- `load8a` reads eight bytes as a little-endian number, through an array. -/
@[step]
theorem load8a_correct (s : Aeneas.Std.Slice U8) (i : Usize) (hb : i.val + 8 ≤ s.val.length) :
    load8a s i ⦃ w => w.val = le [(s.val[i.val]!).val, (s.val[i.val + 1]!).val,
      (s.val[i.val + 2]!).val, (s.val[i.val + 3]!).val, (s.val[i.val + 4]!).val,
      (s.val[i.val + 5]!).val, (s.val[i.val + 6]!).val, (s.val[i.val + 7]!).val] ⦄ := by
  unfold load8a
  step as ⟨s1, back, hs1, hback⟩
  step as ⟨i1, hi1⟩
  step as ⟨s2, hs2⟩
  have hs2l : s2.val.length = 8 := by rw [hs2, List.slice_length]; omega
  have hs1l : s1.val.length = 8 := by rw [hs1, Array.repeat_val]; simp
  step with (copy_from_slice_eq s1 s2 (by rw [hs1l, hs2l])) as ⟨s3, hs3⟩
  have hb1 : (back s3).val = s2.val := by rw [hback, Array.from_slice_val _ _ (by rw [hs3, hs2l]; rfl), hs3]
  have hk : ∀ k, k < 8 → (back s3).val[k]! = s.val[i.val + k]! := by
    intro k hk
    rw [hb1, hs2, List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩]
  have hbl : (back s3).val.length = 8 := by rw [hb1, hs2l]
  step*
  have e0 : i2 = s.val[i.val]! := by
    have h0 := hk 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [← h0, getElem!_pos _ _ (by omega)]; exact i2_post
  have e1 : i4 = s.val[i.val + 1]! := by
    rw [← hk 1 (by omega), getElem!_pos _ _ (by omega)]; exact i4_post
  have e2 : i8 = s.val[i.val + 2]! := by
    rw [← hk 2 (by omega), getElem!_pos _ _ (by omega)]; exact i8_post
  have e3 : i12 = s.val[i.val + 3]! := by
    rw [← hk 3 (by omega), getElem!_pos _ _ (by omega)]; exact i12_post
  have e4 : i16 = s.val[i.val + 4]! := by
    rw [← hk 4 (by omega), getElem!_pos _ _ (by omega)]; exact i16_post
  have e5 : i20 = s.val[i.val + 5]! := by
    rw [← hk 5 (by omega), getElem!_pos _ _ (by omega)]; exact i20_post
  have e6 : i24 = s.val[i.val + 6]! := by
    rw [← hk 6 (by omega), getElem!_pos _ _ (by omega)]; exact i24_post
  have e7 : i28 = s.val[i.val + 7]! := by
    rw [← hk 7 (by omega), getElem!_pos _ _ (by omega)]; exact i28_post
  have hv3 : i3.val = i2.val := by rw [i3_post, cast_byte64]
  have hv5 : i5.val = i4.val := by rw [i5_post, cast_byte64]
  have hv9 : i9.val = i8.val := by rw [i9_post, cast_byte64]
  have hv13 : i13.val = i12.val := by rw [i13_post, cast_byte64]
  have hv17 : i17.val = i16.val := by rw [i17_post, cast_byte64]
  have hv21 : i21.val = i20.val := by rw [i21_post, cast_byte64]
  have hv25 : i25.val = i24.val := by rw [i25_post, cast_byte64]
  have hv29 : i29.val = i28.val := by rw [i29_post, cast_byte64]
  rw [← e0, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7]
  simp only [le]
  scalar_tac

/-- What `store8` leaves: the eight bytes of `w` at `i`, everything else as it was. -/
def Stored (v v' : List U8) (i : Nat) (w : Nat) : Prop :=
  v'.length = v.length ∧
  (∀ k, k < v.length → (k < i ∨ i + 8 ≤ k) → v'[k]! = v[k]!) ∧
  (v'[i]!).val = w % 256 ∧ (v'[i + 1]!).val = w / 256 % 256 ∧ (v'[i + 2]!).val = w / 65536 % 256 ∧
  (v'[i + 3]!).val = w / 16777216 % 256 ∧ (v'[i + 4]!).val = w / 4294967296 % 256 ∧
  (v'[i + 5]!).val = w / 1099511627776 % 256 ∧ (v'[i + 6]!).val = w / 281474976710656 % 256 ∧
  (v'[i + 7]!).val = w / 72057594037927936 % 256

@[step]
theorem store8_correct (v : alloc.vec.Vec U8) (i : Usize) (w : U64) (h : i.val + 8 ≤ v.val.length) :
    store8 v i w ⦃ v' => Stored v.val v'.val i.val w.val ⦄ := by
  unfold store8
  step*
  rw [s_post2, s2_post, s1_post, Array.val_to_slice, Array.make_val]
  have hb2 : i2.val = w.val % 256 := by rw [i2_post, cast_u8_of_lt _ (by omega)]; exact i1_post
  have hb5 : i5.val = w.val / 256 % 256 := by rw [i5_post, cast_u8_of_lt _ (by omega), i4_post, i3_post]
  have hb8 : i8.val = w.val / 65536 % 256 := by rw [i8_post, cast_u8_of_lt _ (by omega), i7_post, i6_post]
  have hb11 : i11.val = w.val / 16777216 % 256 := by rw [i11_post, cast_u8_of_lt _ (by omega), i10_post, i9_post]
  have hb14 : i14.val = w.val / 4294967296 % 256 := by rw [i14_post, cast_u8_of_lt _ (by omega), i13_post, i12_post]
  have hb17 : i17.val = w.val / 1099511627776 % 256 := by rw [i17_post, cast_u8_of_lt _ (by omega), i16_post, i15_post]
  have hb20 : i20.val = w.val / 281474976710656 % 256 := by rw [i20_post, cast_u8_of_lt _ (by omega), i19_post, i18_post]
  have hb23 : i23.val = w.val / 72057594037927936 % 256 := by rw [i23_post, cast_u8_of_lt _ (by omega), i22_post, i21_post]
  have hl : ([i2, i5, i8, i11, i14, i17, i20, i23] : List U8).length = 8 := rfl
  refine ⟨List.length_setSlice! _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk hout
    rw [List.getElem!_setSlice!_same _ _ _ _ (by rw [hl]; omega)]
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.sub_self, List.getElem!_cons_zero]
    exact hb2
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact hb5
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact hb8
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact hb11
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact hb14
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact hb17
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact hb20
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact hb23

/-- `store8w` on a slice: the eight bytes of `w` at `i`, everything else as it was. -/
@[step]
theorem store8w_correct (b : Aeneas.Std.Slice U8) (i : Usize) (w : U64) (h : i.val + 8 ≤ b.val.length) :
    store8w b i w ⦃ b' => Stored b.val b'.val i.val w.val ⦄ := by
  unfold store8w
  step*
  -- the range index on a slice is handled by the library's lemma, whose write-back is
  -- `Slice.setSlice!`
  rw [s_post2, s2_post, s1_post, Slice.setSlice!_val, Array.val_to_slice, Array.make_val]
  have hb2 : i2.val = w.val % 256 := by rw [i2_post, cast_u8_of_lt _ (by omega)]; exact i1_post
  have hb5 : i5.val = w.val / 256 % 256 := by rw [i5_post, cast_u8_of_lt _ (by omega), i4_post, i3_post]
  have hb8 : i8.val = w.val / 65536 % 256 := by rw [i8_post, cast_u8_of_lt _ (by omega), i7_post, i6_post]
  have hb11 : i11.val = w.val / 16777216 % 256 := by rw [i11_post, cast_u8_of_lt _ (by omega), i10_post, i9_post]
  have hb14 : i14.val = w.val / 4294967296 % 256 := by rw [i14_post, cast_u8_of_lt _ (by omega), i13_post, i12_post]
  have hb17 : i17.val = w.val / 1099511627776 % 256 := by rw [i17_post, cast_u8_of_lt _ (by omega), i16_post, i15_post]
  have hb20 : i20.val = w.val / 281474976710656 % 256 := by rw [i20_post, cast_u8_of_lt _ (by omega), i19_post, i18_post]
  have hb23 : i23.val = w.val / 72057594037927936 % 256 := by rw [i23_post, cast_u8_of_lt _ (by omega), i22_post, i21_post]
  have hl : ([i2, i5, i8, i11, i14, i17, i20, i23] : List U8).length = 8 := rfl
  refine ⟨List.length_setSlice! _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk hout
    rw [List.getElem!_setSlice!_same _ _ _ _ (by rw [hl]; omega)]
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.sub_self, List.getElem!_cons_zero]
    exact hb2
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact hb5
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact hb8
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact hb11
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact hb14
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact hb17
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact hb20
  · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [hl]; omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact hb23

end Gzip.Proofs.Decode.SubsliceImpl
