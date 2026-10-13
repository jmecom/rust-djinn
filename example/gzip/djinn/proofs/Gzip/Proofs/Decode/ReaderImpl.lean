import Gzip.Proofs.Decode.CrcImpl
import Gzip.Proofs.Decode.Encoding

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.Decoding Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.RoundTrip

namespace Gzip.Proofs.Decode.ReaderImpl

def pos (r : Reader) : ℤ := 8 * r.byte.val + r.bit.val

def Inv (s : Aeneas.Std.Slice U8) (r : Reader) : Prop :=
  r.byte.val ≤ s.val.length ∧ r.bit.val < 8 ∧ (r.byte.val = s.val.length → r.bit.val = 0)

def BitPost (s : Aeneas.Std.Slice U8) (r : Reader) (z : Option U32 × Reader) : Prop :=
  Inv s z.2 ∧ match z.1 with
  | none => ∀ v, ¬ bit_spec s.val (pos r) v
  | some v => bit_spec s.val (pos r) v.val ∧ pos z.2 = pos r + 1

theorem cast_byte (x : U8) : (UScalar.cast .U32 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

@[step]
theorem read_bit_correct (s : Aeneas.Std.Slice U8) (r : Reader) (h : Inv s r) :
    read_bit s r ⦃ z => BitPost s r z ⦄ := by
  obtain ⟨hb, hn, hend⟩ := h
  unfold read_bit
  step*
  · refine ⟨⟨hb, hn, hend⟩, ?_⟩
    intro v hv
    have hb := hv.2.1
    unfold pos at hb
    scalar_tac
  all_goals
    have hbyte : r.byte.val < s.val.length := by scalar_tac
    have hspec : bit_spec s.val (pos r) b.val := by
      have hdiv : pos r / 8 = r.byte.val := by unfold pos; omega
      have hmod : pos r % 8 = r.bit.val := by unfold pos; omega
      refine ⟨trivial, ⟨by unfold pos; omega, by unfold pos; omega⟩, ?_⟩
      rw [hdiv, hmod, Int.toNat_natCast, Int.toNat_natCast, getElem!_pos s.val r.byte.val hbyte]
      rw [i3_post, Nat.shiftRight_eq_div_pow, i2_post, cast_byte, i1_post] at b_post
      exact_mod_cast b_post
    refine ⟨?_, hspec, ?_⟩
    · unfold Inv
      simp only
      refine ⟨by scalar_tac, by scalar_tac, ?_⟩
      intro he
      scalar_tac
    · unfold pos
      simp only
      scalar_tac

theorem field_range (s : List U8) (i n v : ℤ) (h : field_spec s i n v) :
    0 ≤ v ∧ v < 2 ^ n.toNat := by
  generalize hm : n.toNat = m
  induction m using Nat.strong_induction_on generalizing i n v with
  | h m ih =>
    rw [← hm]
    rw [field_spec] at h
    have hp := h.1
    change 0 ≤ n at hp
    by_cases hn : n = 0
    · have hv := (h.2 hp).1 hn
      simp [hn, hv]
    obtain ⟨b, hb, hrest⟩ := (h.2 hp).2 hn
    obtain ⟨w, hw, he⟩ := hrest hb
    have hrange := Encoding.bit_range s i b hb
    have hrec := ih (n - 1).toNat (hm ▸ int_step_decreases n hp hn) (i + 1) (n - 1) w hw rfl
    have hexp : n.toNat = (n - 1).toNat + 1 := by omega
    rw [hexp, pow_succ]
    constructor <;> omega

def FieldPost (s : Aeneas.Std.Slice U8) (r : Reader) (n : U32) (z : Option U32 × Reader) : Prop :=
  Inv s z.2 ∧ match z.1 with
  | none => ∀ v, ¬ field_spec s.val (pos r) n.val v
  | some v => field_spec s.val (pos r) n.val v.val ∧ pos z.2 = pos r + n.val ∧ v.val < 2 ^ n.val

@[step]
theorem read_field_correct (s : Aeneas.Std.Slice U8) (r : Reader) (n : U32)
    (h : Inv s r) (hn : n.val ≤ 31) : read_field s r n ⦃ z => FieldPost s r n z ⦄ := by
  generalize hm : n.val = m
  induction m using Nat.strong_induction_on generalizing r n with
  | h m ih =>
    unfold read_field
    step*
    all_goals simp_all only [BitPost, FieldPost, Prod.fst, Prod.snd]
    · have hm0 : m = 0 := by simpa only [UScalar.ofNatCore_val_eq] using hm.symm
      subst m
      refine ⟨trivial, ?_, by simp, by decide⟩
      change field_spec s.val (pos r) 0 0
      rw [field_spec]
      exact ⟨show 0 ≤ (0 : ℤ) from by omega, fun _ => ⟨fun _ => rfl, fun hn => (hn rfl).elim⟩⟩
    · refine ⟨trivial, ?_⟩
      intro v hv
      have hm0 : m ≠ 0 := by
        intro hz
        have he : n = 0#u32 := by apply UScalar.eq_of_val_eq; change n.val = 0; omega
        contradiction
      rw [field_spec] at hv
      obtain ⟨b, hb, _⟩ := (hv.2 (by omega)).2 (by omega)
      exact o_post.2 b hb
    · refine ⟨trivial, ?_⟩
      intro v hv
      rw [field_spec] at hv
      obtain ⟨b, hb, hrest⟩ := (hv.2 (by omega)).2 (by omega)
      obtain ⟨w, hw, _⟩ := hrest hb
      apply o1_post.2 w
      convert hw using 1 <;> omega
    · have hb := o1_post.2.2.2
      have hp : (2 : Nat) ^ (m - 1) ≤ 1073741824 := calc
        _ ≤ 2 ^ 30 := Nat.pow_le_pow_right (by omega) (by omega)
        _ = _ := by norm_num
      scalar_tac
    · have hb := o1_post.2.2.2
      have hv := Encoding.bit_range _ _ _ o_post.2.1
      have hp : (2 : Nat) ^ (m - 1) ≤ 1073741824 := calc
        _ ≤ 2 ^ 30 := Nat.pow_le_pow_right (by omega) (by omega)
        _ = _ := by norm_num
      scalar_tac
    · refine ⟨trivial, ?_, by omega, ?_⟩
      · rw [field_spec]
        refine ⟨show 0 ≤ (m : ℤ) from by omega, fun _ => ⟨?_, ?_⟩⟩
        · intro hz; omega
        · intro _
          refine ⟨value.val, o_post.2.1, fun _ => ⟨value1.val, ?_, ?_⟩⟩
          · convert o1_post.2.1 using 1 <;> omega
          · push_cast; rfl
      · have hb := o1_post.2.2.2
        have hv := Encoding.bit_range _ _ _ o_post.2.1
        have hp : (2 : Nat) ^ m = 2 ^ (m - 1) * 2 := by
          conv_lhs => rw [show m = (m - 1) + 1 by omega]
          rw [pow_succ]
        rw [hp]
        omega

def NumPost (P : ℤ → Prop) (o : Option U32) : Prop := match o with
  | none => ∀ v, ¬ P v
  | some v => P v.val

@[step]
theorem read_u16_correct (s : Aeneas.Std.Slice U8) (p : Usize) :
    read_u16 s p ⦃ o => NumPost (u16le_spec s.val p.val) o ⦄ := by
  unfold read_u16
  step*
  · intro v hv
    have hb := hv.2.1
    scalar_tac
  · intro v hv
    have hb := hv.2.1
    scalar_tac
  · have hb : p.val + 2 ≤ s.val.length := by scalar_tac
    have hi0 : i3 = s.val[p.val]! := by rw [getElem!_pos _ _ (by omega)]; exact i3_post
    have hi1 : i6 = s.val[p.val + 1]! := by
      rw [← i5_post, getElem!_pos _ _ (by omega)]; exact i6_post
    have hv4 : i4.val = i3.val := by rw [i4_post, cast_byte]
    have hv7 : i7.val = i6.val := by rw [i7_post, cast_byte]
    refine ⟨trivial, ⟨by omega, by omega⟩, ?_⟩
    have hp1 : ((p.val : ℤ) + 1).toNat = p.val + 1 := by omega
    rw [Int.toNat_natCast, hp1, ← hi0, ← hi1]
    omega

@[step]
theorem read_u32_correct (s : Aeneas.Std.Slice U8) (p : Usize) :
    read_u32 s p ⦃ o => NumPost (u32le_spec s.val p.val) o ⦄ := by
  unfold read_u32
  step*
  · intro v hv
    obtain ⟨_, a, ha, b, hb, _⟩ := hv
    have hb := hb.2.1
    scalar_tac
  · intro v hv
    obtain ⟨_, a, ha, b, hb, _⟩ := hv
    have hb := hb.2.1
    scalar_tac
  · have hb : p.val + 4 ≤ s.val.length := by scalar_tac
    have hi0 : i3 = s.val[p.val]! := by rw [getElem!_pos _ _ (by omega)]; exact i3_post
    have hi1 : i6 = s.val[p.val + 1]! := by
      rw [← i5_post, getElem!_pos _ _ (by omega)]; exact i6_post
    have hi2 : i11 = s.val[p.val + 2]! := by
      rw [← i10_post, getElem!_pos _ _ (by omega)]; exact i11_post
    have hi3 : i16 = s.val[p.val + 3]! := by
      rw [← i15_post, getElem!_pos _ _ (by omega)]; exact i16_post
    have hv4 : i4.val = i3.val := by rw [i4_post, cast_byte]
    have hv7 : i7.val = i6.val := by rw [i7_post, cast_byte]
    have hv12 : i12.val = i11.val := by rw [i12_post, cast_byte]
    have hv17 : i17.val = i16.val := by rw [i17_post, cast_byte]
    refine ⟨trivial, (i3.val : ℤ) + 256 * i6.val, ?_, (i11.val : ℤ) + 256 * i16.val, ?_, ?_⟩
    · refine ⟨trivial, ⟨by omega, by omega⟩, ?_⟩
      have hp1 : ((p.val : ℤ) + 1).toNat = p.val + 1 := by omega
      rw [Int.toNat_natCast, hp1, ← hi0, ← hi1]
    · refine ⟨trivial, ⟨by omega, by omega⟩, ?_⟩
      have hp2 : ((p.val : ℤ) + 2).toNat = p.val + 2 := by omega
      have hp3 : ((p.val : ℤ) + 2 + 1).toNat = p.val + 3 := by omega
      rw [hp2, hp3, ← hi2, ← hi3]
    · omega

end Gzip.Proofs.Decode.ReaderImpl
