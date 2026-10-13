import Gzip.Proofs.Decode.FourHistogramFacts

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.CodewordImpl Gzip.Proofs.Decode.FourHistogramFacts

namespace Gzip.Proofs.Decode.FourHistogramImpl

def inc (a : Array U32 16#usize) (n : Usize) : Result (Array U32 16#usize) := do
  let v ← Array.index_usize a n
  let w ← v + 1#u32
  Array.update a n w

theorem inc_def (a : Array U32 16#usize) (n : Usize) : inc a n = (do
  let v ← Array.index_usize a n
  let w ← v + 1#u32
  Array.update a n w) := rfl

theorem cast_usize8_val (x : U8) : (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

@[step]
theorem inc_correct (a : Array U32 16#usize) (n : Usize) (hn : n.val < 16)
    (ha : (a.val[n.val]!).val ≤ 320) :
    inc a n ⦃ b => ∃ w : U32, w.val = (a.val[n.val]!).val + 1 ∧
      b.val = a.val.set n.val w ⦄ := by
  unfold inc
  step as ⟨v, hv⟩
  have he : v = a.val[n.val]! := by
    rw [Djinn.Vocab.val_getElem! a.val n.val (by scalar_tac)]
    exact hv
  rw [← he] at ha
  step as ⟨w, hw⟩
  step as ⟨b, hb⟩
  refine ⟨w, by scalar_tac, ?_⟩
  rw [hb, Array.set_val_eq]

theorem four_body (lens : Aeneas.Std.Slice U8) (a b c d : Array U32 16#usize) (i : Usize)
    (hl : lens.val.length ≤ 320)
    (hb : ∀ j, j < lens.val.length → (lens.val[j]!).val ≤ 15)
    (h : SummedSeen lens.val a.val b.val c.val d.val i.val) :
    codeword_table_loop0.body lens a b c d i ⦃ r => match r with
    | .done (a', b', c', d', j) => SummedSeen lens.val a'.val b'.val c'.val d'.val j.val
    | .cont (a', b', c', d', j) => SummedSeen lens.val a'.val b'.val c'.val d'.val j.val ∧
        lens.val.length - j.val < lens.val.length - i.val ⦄ := by
  unfold codeword_table_loop0.body
  simp only [← inc_def]
  step as ⟨i2, i2_post⟩
  split
  · step*
    have hi : i.val + 4 ≤ lens.val.length := by scalar_tac
    have hn0 : n0.val = (lens.val[i.val]!).val := by
      rw [n0_post, cast_usize8_val, i3_post, ← getElem!_pos lens.val i.val (by omega)]
    have hn1 : n1.val = (lens.val[i.val + 1]!).val := by
      rw [n1_post, cast_usize8_val, i5_post, ← getElem!_pos lens.val i4.val (by scalar_tac), i4_post]
    have hn2 : n2.val = (lens.val[i.val + 2]!).val := by
      rw [n2_post, cast_usize8_val, i7_post, ← getElem!_pos lens.val i6.val (by scalar_tac), i6_post]
    have hn3 : n3.val = (lens.val[i.val + 3]!).val := by
      rw [n3_post, cast_usize8_val, i9_post, ← getElem!_pos lens.val i8.val (by scalar_tac), i8_post]
    have hb0 := hb i.val (by omega)
    have hb1 := hb (i.val + 1) (by omega)
    have hb2 := hb (i.val + 2) (by omega)
    have hb3 := hb (i.val + 3) (by omega)
    have ht0 : n0 < 16#usize := by scalar_tac
    have ht1 : n1 < 16#usize := by scalar_tac
    have ht2 : n2 < 16#usize := by scalar_tac
    have ht3 : n3 < 16#usize := by scalar_tac
    simp only [if_pos ht0, if_pos ht1, if_pos ht2, if_pos ht3]
    have ha0 := (individual_bounds a.val b.val c.val d.val n0.val i.val (h.2 n0.val (by scalar_tac)).2).1
    have hb0 := (individual_bounds a.val b.val c.val d.val n1.val i.val (h.2 n1.val (by scalar_tac)).2).2.1
    have hc0 := (individual_bounds a.val b.val c.val d.val n2.val i.val (h.2 n2.val (by scalar_tac)).2).2.2.1
    have hd0 := (individual_bounds a.val b.val c.val d.val n3.val i.val (h.2 n3.val (by scalar_tac)).2).2.2.2
    step with (inc_correct a n0 (by scalar_tac) (by omega)) as ⟨a1, wa, hwa, ha1⟩
    step with (inc_correct b n1 (by scalar_tac) (by omega)) as ⟨b1, wb, hwb, hb1⟩
    step with (inc_correct c n2 (by scalar_tac) (by omega)) as ⟨c1, wc, hwc, hc1⟩
    step with (inc_correct d n3 (by scalar_tac) (by omega)) as ⟨d1, wd, hwd, hd1⟩
    step as ⟨j, hj⟩
    step*
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    intro m hm
    have hsum : total4 a1.val b1.val c1.val d1.val m = total4 a.val b.val c.val d.val m +
        delta lens.val i.val m + delta lens.val (i.val + 1) m +
        delta lens.val (i.val + 2) m + delta lens.val (i.val + 3) m := by
      rw [ha1, hb1, hc1, hd1]
      rw [total4_increment_first _ _ _ _ _ _ _ (by scalar_tac) hwa]
      rw [total4_increment_second _ _ _ _ _ _ _ (by scalar_tac) hwb]
      rw [total4_increment_third _ _ _ _ _ _ _ (by scalar_tac) hwc]
      rw [total4_increment_fourth _ _ _ _ _ _ _ (by scalar_tac) hwd]
      simp only [delta, hn0, hn1, hn2, hn3]
      omega
    obtain ⟨he, heBound⟩ := h.2 m hm
    rw [hsum, hj]
    refine ⟨earlier_four lens.val i.val m _ hi he, ?_⟩
    unfold delta
    split_ifs <;> omega
  · step*

theorem four_loop_correct (lens : Aeneas.Std.Slice U8) (a b c d : Array U32 16#usize) (i : Usize)
    (hl : lens.val.length ≤ 320)
    (hb : ∀ j, j < lens.val.length → (lens.val[j]!).val ≤ 15)
    (h : SummedSeen lens.val a.val b.val c.val d.val i.val) :
    codeword_table_loop0 lens a b c d i ⦃ z =>
      SummedSeen lens.val z.1.val z.2.1.val z.2.2.1.val z.2.2.2.1.val z.2.2.2.2.val ⦄ := by
  unfold codeword_table_loop0
  apply loop.spec_decr_nat (fun (_, _, _, _, j) => lens.val.length - j.val)
    (fun (a', b', c', d', j) => SummedSeen lens.val a'.val b'.val c'.val d'.val j.val)
  · rintro ⟨a', b', c', d', j⟩ hinv
    apply WP.spec_mono (four_body lens a' b' c' d' j hl hb hinv)
    intro r hr
    cases r <;> exact hr
  · exact h

theorem tail_body (lens : Aeneas.Std.Slice U8) (a b c d : Array U32 16#usize) (i : Usize)
    (hl : lens.val.length ≤ 320)
    (hb : ∀ j, j < lens.val.length → (lens.val[j]!).val ≤ 15)
    (h : SummedSeen lens.val a.val b.val c.val d.val i.val) :
    codeword_table_loop1.body lens a i ⦃ r => match r with
    | .done a' => SummedSeen lens.val a'.val b.val c.val d.val lens.val.length
    | .cont (a', j) => SummedSeen lens.val a'.val b.val c.val d.val j.val ∧
        lens.val.length - j.val < lens.val.length - i.val ⦄ := by
  have hle := h.1
  unfold codeword_table_loop1.body
  simp only [← inc_def]
  step*
  · have hi : i.val < lens.val.length := by scalar_tac
    have hn : n.val = (lens.val[i.val]!).val := by
      rw [n_post, cast_usize8_val, i2_post, ← getElem!_pos lens.val i.val hi]
    have hb0 := hb i.val hi
    have ht : n < 16#usize := by scalar_tac
    simp only [if_pos ht]
    have ha0 := (individual_bounds a.val b.val c.val d.val n.val i.val (h.2 n.val (by scalar_tac)).2).1
    step with (inc_correct a n (by scalar_tac) (by omega)) as ⟨a1, w, hw, ha1⟩
    step as ⟨j, hj⟩
    step*
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    intro m hm
    obtain ⟨he, heb⟩ := h.2 m hm
    have hs : total4 a1.val b.val c.val d.val m = total4 a.val b.val c.val d.val m + delta lens.val i.val m := by
      rw [ha1, total4_increment_first _ _ _ _ _ _ _ (by scalar_tac) hw]
      simp only [delta, hn]
    rw [hs, hj]
    refine ⟨earlier_next_nat lens.val i.val m _ hi he, ?_⟩
    unfold delta
    split_ifs <;> omega

theorem tail_loop_correct (lens : Aeneas.Std.Slice U8) (a b c d : Array U32 16#usize) (i : Usize)
    (hl : lens.val.length ≤ 320)
    (hb : ∀ j, j < lens.val.length → (lens.val[j]!).val ≤ 15)
    (h : SummedSeen lens.val a.val b.val c.val d.val i.val) :
    codeword_table_loop1 lens a i ⦃ a' =>
      SummedSeen lens.val a'.val b.val c.val d.val lens.val.length ⦄ := by
  unfold codeword_table_loop1
  apply loop.spec_decr_nat (fun (_, j) => lens.val.length - j.val)
    (fun (a', j) => SummedSeen lens.val a'.val b.val c.val d.val j.val)
  · rintro ⟨a', j⟩ hinv
    apply WP.spec_mono (tail_body lens a' b c d j hl hb hinv)
    intro r hr
    cases r <;> exact hr
  · exact h

end Gzip.Proofs.Decode.FourHistogramImpl
