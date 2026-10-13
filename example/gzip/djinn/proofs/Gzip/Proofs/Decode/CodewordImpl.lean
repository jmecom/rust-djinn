import Gzip.Proofs.Decode.BaseImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.BaseImpl

namespace Gzip.Proofs.Decode.CodewordImpl

theorem shorter_zero (lens : List U8) (n : Nat) : shorter_spec lens 0 n 0 := by
  rw [shorter_spec]
  simp [shorter_pre]

theorem earlier_zero (lens : List U8) (n : Nat) : earlier_spec lens 0 n 0 := by
  rw [earlier_spec]
  simp [earlier_pre]

theorem shorter_next (lens : List U8) (i n c : Nat)
    (hi : i < lens.length) (hc : shorter_spec lens i n c) :
    shorter_spec lens (i + 1) n
      (c + if 0 < (lens[i]!).val ∧ (lens[i]!).val < n then 2 ^ (n - (lens[i]!).val) else 0) := by
  rw [shorter_spec]
  have hidx : ((i : ℤ) + 1 - 1).toNat = i := by omega
  simp only [hidx]
  refine ⟨⟨by omega, by omega⟩, fun _ => ⟨?_, fun _ => ⟨?_, ?_⟩⟩⟩
  · intro hz; omega
  · intro he
    refine ⟨c, ?_, ?_⟩
    · convert hc using 1 <;> omega
    · rw [if_pos (by omega)]
      have hn : ((n : ℤ) - (lens[i]!).val).toNat = n - (lens[i]!).val := by omega
      rw [hn]
  · intro he
    rw [if_neg (by omega), add_zero]
    convert hc using 1 <;> omega

theorem earlier_next (lens : List U8) (i n c : Nat)
    (hi : i < lens.length) (hc : earlier_spec lens i n c) :
    earlier_spec lens (i + 1) n (c + if (lens[i]!).val = n then 1 else 0) := by
  rw [earlier_spec]
  have hidx : ((i : ℤ) + 1 - 1).toNat = i := by omega
  simp only [hidx]
  refine ⟨⟨by omega, by omega⟩, fun _ => ⟨?_, fun _ => ⟨?_, ?_⟩⟩⟩
  · intro hz; omega
  · intro he
    refine ⟨c, ?_, ?_⟩
    · convert hc using 1 <;> omega
    · rw [if_pos (by omega)]
  · intro he
    rw [if_neg (by omega), add_zero]
    convert hc using 1 <;> omega

def ShorterInv (lens : List U8) (k n : Nat) (i : Usize) (c : U32) : Prop :=
  i.val ≤ k ∧ shorter_spec lens i.val n c.val ∧ c.val ≤ i.val * 2 ^ n

def EarlierInv (lens : List U8) (k n : Nat) (i : Usize) (c : U32) : Prop :=
  i.val ≤ k ∧ earlier_spec lens i.val n c.val ∧ c.val ≤ i.val

theorem shorter_body (lens : Aeneas.Std.Slice U8) (k : Usize) (n : U32) (i : Usize) (c : U32)
    (hk : k.val ≤ lens.val.length) (hk320 : k.val ≤ 320) (hn : n.val ≤ 16)
    (h : ShorterInv lens.val k.val n.val i c) :
    count_shorter_loop.body lens k n i c ⦃ r => match r with
      | .done v => shorter_spec lens.val k.val n.val v.val ∧ v.val ≤ k.val * 2 ^ n.val
      | .cont (j, v) => ShorterInv lens.val k.val n.val j v ∧ k.val - j.val < k.val - i.val ⦄ := by
  obtain ⟨hi, hc, hbound⟩ := h
  have hp := pow_two_le n.val hn
  unfold count_shorter_loop.body
  step*
  all_goals try (split <;> step*)
  all_goals try (split <;> step*)
  · have hu : x.val ≤ 65536 := by
      rw [x_post, shift_one _ (by scalar_tac)]
      apply pow_two_le
      scalar_tac
    have hb : c.val ≤ 320 * 65536 := _root_.le_trans hbound (Nat.mul_le_mul (by omega) hp)
    scalar_tac
  · have hget : l.val = (lens.val[i.val]!).val := by
      rw [l_post, cast_byte, i1_post, getElem!_pos lens.val i.val (by scalar_tac)]
    have hnext := shorter_next lens.val i.val n.val c.val (by scalar_tac) hc
    rw [if_pos (by scalar_tac), ← hget] at hnext
    have he : x.val = 2 ^ (n.val - l.val) := by
      rw [x_post, shift_one _ (by scalar_tac)]
      congr 1
    refine ⟨⟨by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
    · convert hnext using 1 <;> push_cast <;> scalar_tac
    · have hepow : 2 ^ (n.val - l.val) ≤ 2 ^ n.val := Nat.pow_le_pow_right (by omega) (by omega)
      rw [i2_post, Nat.add_mul, Nat.one_mul]
      scalar_tac
  all_goals
    have hget : l.val = (lens.val[i.val]!).val := by
      rw [l_post, cast_byte, i1_post, getElem!_pos lens.val i.val (by scalar_tac)]
    have hnext := shorter_next lens.val i.val n.val c.val (by scalar_tac) hc
    rw [if_neg (by scalar_tac), add_zero] at hnext
    refine ⟨⟨by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
    · convert hnext using 1 <;> scalar_tac
    · exact _root_.le_trans hbound (Nat.mul_le_mul_right _ (by scalar_tac))

@[step]
theorem count_shorter_correct (lens : Aeneas.Std.Slice U8) (k : Usize) (n : U32)
    (hk : k.val ≤ lens.val.length) (hk320 : k.val ≤ 320) (hn : n.val ≤ 16) :
    count_shorter lens k n ⦃ c => shorter_spec lens.val k.val n.val c.val ∧ c.val ≤ k.val * 2 ^ n.val ⦄ := by
  unfold count_shorter count_shorter_loop
  apply loop.spec_decr_nat (fun (i, _) => k.val - i.val)
    (fun (i, c) => ShorterInv lens.val k.val n.val i c)
  · rintro ⟨i, c⟩ hinv
    apply WP.spec_mono (shorter_body lens k n i c hk hk320 hn hinv)
    intro r hr
    cases r <;> exact hr
  · exact ⟨by simp, shorter_zero _ _, by simp⟩

theorem earlier_body (lens : Aeneas.Std.Slice U8) (k : Usize) (n : U32) (i : Usize) (c : U32)
    (hk : k.val ≤ lens.val.length) (hk320 : k.val ≤ 320)
    (h : EarlierInv lens.val k.val n.val i c) :
    count_earlier_loop.body lens k n i c ⦃ r => match r with
      | .done v => earlier_spec lens.val k.val n.val v.val ∧ v.val ≤ k.val
      | .cont (j, v) => EarlierInv lens.val k.val n.val j v ∧ k.val - j.val < k.val - i.val ⦄ := by
  obtain ⟨hi, hc, hbound⟩ := h
  unfold count_earlier_loop.body
  step*
  all_goals try (split <;> step*)
  · have hget : i2.val = (lens.val[i.val]!).val := by
      rw [i2_post, cast_byte, i1_post, getElem!_pos lens.val i.val (by scalar_tac)]
    have hnext := earlier_next lens.val i.val n.val c.val (by scalar_tac) hc
    rw [if_pos (by scalar_tac)] at hnext
    refine ⟨⟨by scalar_tac, ?_, by scalar_tac⟩, by scalar_tac⟩
    convert hnext using 1 <;> scalar_tac
  · have hget : i2.val = (lens.val[i.val]!).val := by
      rw [i2_post, cast_byte, i1_post, getElem!_pos lens.val i.val (by scalar_tac)]
    have hnext := earlier_next lens.val i.val n.val c.val (by scalar_tac) hc
    rw [if_neg (by scalar_tac), add_zero] at hnext
    refine ⟨⟨by scalar_tac, ?_, by scalar_tac⟩, by scalar_tac⟩
    convert hnext using 1 <;> scalar_tac

@[step]
theorem count_earlier_correct (lens : Aeneas.Std.Slice U8) (k : Usize) (n : U32)
    (hk : k.val ≤ lens.val.length) (hk320 : k.val ≤ 320) :
    count_earlier lens k n ⦃ c => earlier_spec lens.val k.val n.val c.val ∧ c.val ≤ k.val ⦄ := by
  unfold count_earlier count_earlier_loop
  apply loop.spec_decr_nat (fun (i, _) => k.val - i.val)
    (fun (i, c) => EarlierInv lens.val k.val n.val i c)
  · rintro ⟨i, c⟩ hinv
    apply WP.spec_mono (earlier_body lens k n i c hk hk320 hinv)
    intro r hr
    cases r <;> exact hr
  · exact ⟨by simp, earlier_zero _ _, by simp⟩

@[step]
theorem codeword_correct (lens : Aeneas.Std.Slice U8) (sym : Usize)
    (hs : sym.val < lens.val.length) (hl : lens.val.length ≤ 320)
    (hn : (lens.val[sym.val]!).val ≤ 16) :
    codeword lens sym ⦃ c => codeword_spec lens.val sym.val c.val ⦄ := by
  unfold codeword
  step*
  · rw [n_post, cast_byte, i_post]
    rwa [getElem!_pos lens.val sym.val hs] at hn
  · have hn' : n.val ≤ 16 := by
      rw [n_post, cast_byte, i_post]
      rwa [getElem!_pos lens.val sym.val hs] at hn
    have hp := pow_two_le n.val hn'
    have hc : i2.val ≤ 320 * 65536 := calc
      _ ≤ lens.val.length * 2 ^ n.val := i2_post1
      _ ≤ 320 * 65536 := Nat.mul_le_mul hl hp
    scalar_tac
  · have hn' : n.val = (lens.val[sym.val]!).val := by
      rw [n_post, cast_byte, i_post, getElem!_pos lens.val sym.val hs]
    refine ⟨trivial, ⟨by omega, by omega⟩, i2.val, ?_, i3.val, ?_, ?_⟩
    · simpa only [Int.toNat_natCast, ← hn', Slice.len_val] using i2_post
    · simpa only [Int.toNat_natCast, ← hn'] using i3_post
    · omega

@[step]
theorem lengths_bounded_correct (lens : Aeneas.Std.Slice U8) (k : Usize) (max : U32)
    (hk : k.val ≤ lens.val.length) : lengths_bounded lens k max
      ⦃ b => b = true ↔ ∀ j, j < k.val → (lens.val[j]!).val ≤ max.val ⦄ := by
  generalize hm : k.val = m
  induction m using Nat.strong_induction_on generalizing k with
  | h m ih =>
    unfold lengths_bounded
    step*
    all_goals
      have hl : i2.val = (lens.val[i.val]!).val := by
        rw [i2_post, cast_byte, i1_post, getElem!_pos lens.val i.val (by omega)]
    · constructor
      · intro hb j hj
        by_cases he : j = i.val
        · rw [he, ← hl]; scalar_tac
        · exact (b_post.mp hb) j (by omega)
      · intro hb
        apply b_post.mpr
        intro j hj
        exact hb j (by omega)
    · constructor
      · intro hf; contradiction
      · intro hb
        have hv := hb i.val (by omega)
        scalar_tac

theorem lengths_bound_iff (lens : List U8) (n : Nat) :
    (∀ j, j < lens.length → (lens[j]!).val ≤ n) ↔ (∀ l ∈ lens, (l.val : ℤ) ≤ n) := by
  constructor
  · intro h l hl
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hl
    have hv := h i hi
    rw [getElem!_pos lens i hi, he] at hv
    omega
  · intro h j hj
    have hv := h lens[j] (List.getElem_mem hj)
    rw [getElem!_pos lens j hj]
    omega

@[step]
theorem valid_correct (lens : Aeneas.Std.Slice U8) (max : U32)
    (hl : lens.val.length ≤ 320) (hm : max.val ≤ 15) :
    valid lens max ⦃ b => valid_spec lens.val max.val b ⦄ := by
  unfold valid
  step*
  · have he : (i2.val : ℤ) = (max.val : ℤ) + 1 := by omega
    have hc : shorter_spec lens.val lens.val.length ((max.val : ℤ) + 1) i3.val := by
      simpa only [Slice.len_val, he] using i3_post
    have hbound : ∀ l ∈ lens.val, (l.val : ℤ) ≤ max.val := by
      apply (lengths_bound_iff _ _).mp
      simpa only [Slice.len_val] using b_post.mp (by assumption)
    have hp : (i4.val : ℤ) = 2 ^ ((max.val : ℤ) + 1).toNat := by
      rw [i4_post, shift_one _ (by omega)]
      have hn : ((max.val : ℤ) + 1).toNat = i2.val := by omega
      rw [hn]
      push_cast
      rfl
    refine ⟨show 0 ≤ (max.val : ℤ) from by omega, ?_⟩
    simp only [decide_eq_true_eq]
    constructor
    · intro hv
      refine ⟨hbound, i3.val, hc, ?_⟩
      rw [← hp]
      scalar_tac
    · rintro ⟨_, v, hv, hle⟩
      have heq := Decoding.shorter_unique _ _ _ _ _ hc hv
      rw [← heq, ← hp] at hle
      scalar_tac
  · refine ⟨show 0 ≤ (max.val : ℤ) from by omega, ?_⟩
    constructor
    · intro hf; contradiction
    · rintro ⟨hb, _⟩
      have h := (lengths_bound_iff _ _).mpr hb
      have he : b = true := b_post.mpr (by simpa only [Slice.len_val] using h)
      contradiction

end Gzip.Proofs.Decode.CodewordImpl
