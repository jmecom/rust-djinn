import Gzip.Proofs.Decode.ReaderImpl
import Gzip.Proofs.Decode.WideFacts
import Gzip.Proofs.Decode.WindowFacts
import Gzip.Proofs.Decode.SubsliceImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.PeekFacts Gzip.Proofs.Decode.WideFacts Gzip.Proofs.Decode.WindowFacts
open Gzip.Proofs.Decode.SubsliceImpl

namespace Gzip.Proofs.Decode.WindowImpl

/-- The stream position of a window: `cpos` bytes have been loaded, `nbits` of them not used. -/
def wpos (cpos : Usize) (nbits : U32) : ℤ := 8 * (cpos.val : ℤ) - nbits.val

/-- The window state of the decoding loop. -/
def WInv (s : Aeneas.Std.Slice U8) (buf : U64) (nbits : U32) (cpos : Usize) : Prop :=
  cpos.val ≤ s.val.length ∧ nbits.val ≤ 63 ∧ nbits.val ≤ 8 * cpos.val ∧
    Window s.val buf.val nbits.val (wpos cpos nbits)

theorem winv_pos_bound (s : Aeneas.Std.Slice U8) (buf : U64) (nbits : U32) (cpos : Usize)
    (h : WInv s buf nbits cpos) : 0 ≤ wpos cpos nbits ∧ wpos cpos nbits ≤ 8 * s.val.length := by
  obtain ⟨h1, _, h3, _⟩ := h
  unfold wpos
  omega

theorem u64_size : U64.size = 2 ^ 64 := by scalar_tac

/-- Oring 56 into a count below 64 keeps its low three bits and sets the next three. -/
theorem or56_all : ∀ m, m < 64 → m ||| 56 = m % 8 + 56 := by decide

theorem or56 (n : Nat) (h : n < 64) : n ||| 56 = n % 8 + 56 := or56_all n h

/-! `load8s_correct` (the eight bytes from `i` as a little-endian number) is in `SubsliceImpl`. -/

/-- The bits of those eight bytes are the stream's from `8 * i` on. -/
theorem load8s_bits (s : Aeneas.Std.Slice U8) (i : Usize) (w : U64) (hb : i.val + 8 ≤ s.val.length)
    (hw : w.val = le [(s.val[i.val]!).val, (s.val[i.val + 1]!).val,
      (s.val[i.val + 2]!).val, (s.val[i.val + 3]!).val, (s.val[i.val + 4]!).val,
      (s.val[i.val + 5]!).val, (s.val[i.val + 6]!).val, (s.val[i.val + 7]!).val]) :
    ∀ j : Nat, j < 64 → bit_spec s.val (8 * (i.val : ℤ) + j) ((w.val / 2 ^ j % 2 : Nat) : ℤ) := by
  intro j hj
  rw [hw]
  exact peek_bit8 s.val i.val j hb hj

/-- Oring anything in above `nbits` leaves the low `nbits` bits alone. -/
theorem or_shift_low (buf x nbits : Nat) :
    (buf ||| (x <<< nbits) % 2 ^ 64) % 2 ^ nbits = buf % 2 ^ nbits := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hk : k < nbits
  · have hd : decide (k ≥ nbits) = false := by simp; omega
    simp [hk, hd]
  · simp [hk]

/-- Refilling keeps the window's position, its invariant and its low `nbits` bits; when the
eight bytes were there, every one of the 64 bits is the stream's. -/
@[step]
theorem refill_correct (s : Aeneas.Std.Slice U8) (buf : U64) (nbits : U32) (cpos : Usize)
    (h : WInv s buf nbits cpos) :
    refill s buf nbits cpos ⦃ z => WInv s z.1 z.2.1 z.2.2 ∧ wpos z.2.2 z.2.1 = wpos cpos nbits ∧
      z.1.val % 2 ^ nbits.val = buf.val % 2 ^ nbits.val ∧
      (cpos.val + 8 ≤ s.val.length → 56 ≤ z.2.1.val) ∧
      (s.val.length < cpos.val + 8 → z.1 = buf ∧ z.2.1 = nbits ∧ z.2.2 = cpos) ∧
      (cpos.val + 8 ≤ s.val.length →
        ∀ k : Nat, k < 64 → bit_spec s.val (wpos cpos nbits + k) ((z.1.val / 2 ^ k % 2 : Nat) : ℤ)) ⦄ := by
  obtain ⟨hc, hn, hnc, hw⟩ := h
  unfold refill
  step*
  all_goals try scalar_tac
  · have h4 : i4.val = (i3.val <<< nbits.val) % 2 ^ 64 := by rw [i4_post, u64_size]
    have hb5 : i5.val = buf.val ||| i4.val := by rw [i5_post, UScalar.val_or]
    have hlow : i5.val % 2 ^ nbits.val = buf.val % 2 ^ nbits.val := by
      rw [hb5, h4]
      exact or_shift_low buf.val i3.val nbits.val
    have h6 : i6.val = nbits.val % 8 + 56 := by
      rw [i6_post, UScalar.val_or]
      exact or56 nbits.val (by omega)
    have hv9 : i9.val = i8.val := by
      rw [i9_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
    have hb8 : cpos.val + 8 ≤ s.val.length := by scalar_tac
    have hi3 := load8s_bits s cpos i3 hb8 i3_post
    have hall := window_refill s.val buf.val nbits.val i3.val i4.val (wpos cpos nbits) hw
      (fun j hj => by
        have hb := hi3 j hj
        have he : wpos cpos nbits + (nbits.val : ℤ) + (j : ℤ) = 8 * (cpos.val : ℤ) + j := by
          unfold wpos; ring
        rw [he]
        exact hb)
      (by omega) h4
    have hpos : wpos i10 i6 = wpos cpos nbits := by
      unfold wpos
      scalar_tac
    have hwin : Window s.val i5.val i6.val (wpos i10 i6) := by
      rw [hb5, hpos]
      intro k hk
      exact Or.inl (hall k hk)
    show WInv s i5 i6 i10 ∧ wpos i10 i6 = wpos cpos nbits ∧ i5.val % 2 ^ nbits.val = buf.val % 2 ^ nbits.val ∧
      (cpos.val + 8 ≤ s.val.length → 56 ≤ i6.val) ∧
      (s.val.length < cpos.val + 8 → i5 = buf ∧ i6 = nbits ∧ i10 = cpos) ∧
      (cpos.val + 8 ≤ s.val.length →
        ∀ k : Nat, k < 64 → bit_spec s.val (wpos cpos nbits + k) ((i5.val / 2 ^ k % 2 : Nat) : ℤ))
    refine ⟨⟨by scalar_tac, by scalar_tac, by scalar_tac, hwin⟩, hpos, hlow, fun _ => by scalar_tac,
      fun hlt => by exfalso; scalar_tac, fun _ k hk => ?_⟩
    rw [hb5]
    exact hall k hk
  all_goals
    refine ⟨⟨hc, hn, hnc, hw⟩, ?_⟩
    repeat' constructor
    all_goals first | rfl | (intro hle; first | trivial | rfl | exact ⟨rfl, rfl, rfl⟩ | (exfalso; scalar_tac))

/-- The window at a reader's position. -/
@[step]
theorem window_at_correct (s : Aeneas.Std.Slice U8) (r : Reader) (h : Inv s r) :
    window_at s r ⦃ z => WInv s z.1 z.2.1 z.2.2 ∧ wpos z.2.2 z.2.1 = pos r ⦄ := by
  obtain ⟨hb, hbit, hend⟩ := h
  unfold window_at
  step*
  · have hbl : r.byte.val < s.val.length := by scalar_tac
    have hi1 : i1 = s.val[r.byte.val]! := by rw [getElem!_pos s.val r.byte.val hbl]; exact i1_post
    have hv : i2.val = i1.val := by rw [i2_post, cast_byte64]
    have h3 : i3.val = (s.val[r.byte.val]!).val / 2 ^ r.bit.val := by
      rw [i3_post, Nat.shiftRight_eq_div_pow, hv, hi1]
    have h4 : i4.val = 8 - r.bit.val := by scalar_tac
    have h5 : i5.val = r.byte.val + 1 := by scalar_tac
    have hpos : wpos i5 i4 = 8 * (r.byte.val : ℤ) + r.bit.val := by
      unfold wpos; omega
    have hwin : Window s.val i3.val i4.val (wpos i5 i4) := by
      rw [h3, hpos, h4]
      exact window_byte s.val r.byte.val r.bit.val hbl hbit
    show WInv s i3 i4 i5 ∧ wpos i5 i4 = pos r
    refine ⟨⟨by omega, by omega, by omega, hwin⟩, ?_⟩
    rw [hpos]; unfold pos; rfl
  · have hbe : r.byte.val = s.val.length := by scalar_tac
    have hb0 : r.bit.val = 0 := hend hbe
    have hwin : Window s.val (0#u64).val (0#u32).val (wpos r.byte 0#u32) := by
      simpa using window_empty s.val (wpos r.byte 0#u32)
    show WInv s 0#u64 0#u32 r.byte ∧ wpos r.byte 0#u32 = pos r
    refine ⟨⟨by omega, by simp, by simp, hwin⟩, ?_⟩
    unfold wpos pos; simp [hb0]

/-- The reader at a window's position. -/
@[step]
theorem reader_at_correct (s : Aeneas.Std.Slice U8) (cpos : Usize) (nbits : U32)
    (hc : cpos.val ≤ s.val.length) (hn : nbits.val ≤ 63) (hnc : nbits.val ≤ 8 * cpos.val) :
    reader_at cpos nbits ⦃ r => Inv s r ∧ pos r = wpos cpos nbits ⦄ := by
  unfold reader_at
  step*
  have hi2 : i2.val = i1.val := by
    rw [i2_post, UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  unfold ReaderImpl.Inv pos wpos
  simp only
  refine ⟨⟨by omega, by omega, fun h => by omega⟩, by omega⟩

end Gzip.Proofs.Decode.WindowImpl
