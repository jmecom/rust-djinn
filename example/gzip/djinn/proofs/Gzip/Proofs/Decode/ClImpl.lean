import Gzip.Proofs.Decode.LengthsImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.RoundTrip

namespace Gzip.Proofs.Decode.ClImpl

def order (k : Nat) : Nat := (clOrder[k]!).val

theorem order_bound : ∀ k : Fin 19, order k.val < 19 := by decide

theorem order_injective : ∀ k j : Fin 19, order k.val = order j.val → k.val = j.val := by decide

def ClSpec (s : List U8) (i : ℤ) (n : Nat) (cl : List U8) : Prop :=
  cl.length = 19 ∧ ∀ k, k < 19 →
    if k < n then field_spec s (i + 3 * k) 3 (cl[order k]!).val else (cl[order k]!).val = 0

theorem get_set (l : List U8) (i j : Nat) (v : U8) (hj : j < l.length) :
    (l.set i v)[j]! = if i = j then v else l[j]! := by
  rw [getElem!_pos (l.set i v) j (by simpa only [List.length_set] using hj), List.getElem_set]
  split_ifs
  · rfl
  · rw [getElem!_pos l j hj]

theorem cl_step (s cl : List U8) (i : ℤ) (k : Nat) (value : U8) (hk : k < 19)
    (hcl : ClSpec s i k cl) (hf : field_spec s (i + 3 * k) 3 value.val) :
    ClSpec s i (k + 1) (cl.set (order k) value) := by
  obtain ⟨hlen, hvals⟩ := hcl
  refine ⟨by simpa only [List.length_set] using hlen, ?_⟩
  intro j hj
  have horder : order j < 19 := order_bound ⟨j, hj⟩
  rw [get_set cl (order k) (order j) value (by omega)]
  by_cases he : j = k
  · subst j
    simp only [if_pos, Nat.lt_succ_self]
    exact hf
  · have hne : order k ≠ order j := by
      intro heq
      have he' := order_injective ⟨k, hk⟩ ⟨j, hj⟩ heq
      exact he he'.symm
    rw [if_neg hne]
    have hv := hvals j hj
    by_cases hlt : j < k
    · simpa only [if_pos hlt, if_pos (by omega : j < k + 1)] using hv
    · simpa only [if_neg hlt, if_neg (by omega : ¬ j < k + 1)] using hv

theorem cl_zero (s : List U8) (i : ℤ) : ClSpec s i 0 (List.replicate 19 0#u8) := by
  refine ⟨by simp, ?_⟩
  intro k hk
  simp only [Nat.not_lt_zero, if_false, List.getElem!_replicate _ (order_bound ⟨k, hk⟩)]
  rfl

theorem cl_unique (s : List U8) (i : ℤ) (n : Nat) (cl cl' : List U8)
    (h : ClSpec s i n cl) (h' : ClSpec s i n cl') : cl = cl' := by
  apply list_eq cl cl' (by rw [h.1, h'.1])
  intro q hq
  obtain ⟨k, hk⟩ := clOrder_covers ⟨q, by have hb := h.1; omega⟩
  change order k.val = q at hk
  have hv := h.2 k.val k.isLt
  have hv' := h'.2 k.val k.isLt
  rw [hk] at hv hv'
  apply UScalar.eq_of_val_eq
  by_cases hkn : k.val < n
  · simp only [if_pos hkn] at hv hv'
    have he := Decoding.field_unique _ _ _ _ _ hv hv'
    omega
  · simp only [if_neg hkn] at hv hv'
    omega

theorem cl_bound (s : List U8) (i : ℤ) (n : Nat) (cl : List U8) (h : ClSpec s i n cl) :
    ∀ j, j < cl.length → (cl[j]!).val ≤ 7 := by
  intro q hq
  obtain ⟨k, hk⟩ := clOrder_covers ⟨q, by have hb := h.1; omega⟩
  change order k.val = q at hk
  have hv := h.2 k.val k.isLt
  rw [hk] at hv
  by_cases hkn : k.val < n
  · simp only [if_pos hkn] at hv
    have hr := field_range _ _ _ _ hv
    change 0 ≤ ((cl[q]!).val : ℤ) ∧ ((cl[q]!).val : ℤ) < 8 at hr
    omega
  · simp only [if_neg hkn] at hv
    omega

def orderWords : List Usize := [16#usize,17#usize,18#usize,0#usize,8#usize,7#usize,9#usize,6#usize,10#usize,5#usize,11#usize,4#usize,12#usize,3#usize,13#usize,2#usize,14#usize,1#usize,15#usize]

theorem orderWords_correct : ∀ k : Fin 19, (orderWords[k.val]!).val = order k.val ∧ (orderWords[k.val]!).val < 19 := by decide

@[step]
theorem cl_order_correct (k : Usize) (hk : k.val < 19) :
    cl_order k ⦃ j => j.val = order k.val ∧ j.val < 19 ⦄ := by
  unfold cl_order
  step*
  have hj : j = orderWords[k.val]! := by
    rw [getElem!_pos orderWords k.val (by simpa [orderWords] using hk)]
    simpa only [Array.make_val, orderWords] using j_post
  rw [hj]
  exact orderWords_correct ⟨k.val, hk⟩

def ClPost (s : Aeneas.Std.Slice U8) (i : ℤ) (nc : Nat)
    (z : Option Unit × Reader × alloc.vec.Vec U8) : Prop := match z.1 with
  | none => ∀ cl, ¬ ClSpec s.val i nc cl
  | some _ => Inv s z.2.1 ∧ pos z.2.1 = i + 3 * nc ∧ ClSpec s.val i nc z.2.2.val

@[step]
theorem read_clens_correct (s : Aeneas.Std.Slice U8) (r : Reader) (cl : alloc.vec.Vec U8)
    (k nc : Usize) (i : ℤ) (h : Inv s r) (hp : pos r = i + 3 * k.val)
    (hcl : ClSpec s.val i k.val cl.val) (hk : k.val ≤ nc.val) (hn : nc.val ≤ 19) :
    read_clens s r cl k nc ⦃ z => ClPost s i nc.val z ⦄ := by
  generalize hm : nc.val - k.val = m
  induction m using Nat.strong_induction_on generalizing r cl k with
  | h m ih =>
    have recur (r' : Reader) (cl' : alloc.vec.Vec U8) (k' : Usize) (hr' : Inv s r')
        (hp' : pos r' = i + 3 * k'.val) (hcl' : ClSpec s.val i k'.val cl'.val)
        (hk' : k'.val ≤ nc.val) (hg : k.val < k'.val) :
        read_clens s r' cl' k' nc ⦃ z => ClPost s i nc.val z ⦄ :=
      ih _ (by omega) r' cl' k' hr' hp' hcl' hk' rfl
    clear ih
    unfold read_clens
    step*
    · have he : k.val = nc.val := by scalar_tac
      exact ⟨h, by simpa only [he] using hp, by simpa only [he] using hcl⟩
    · simp only [FieldPost, show o = none by assumption] at o_post
      intro cs hcs
      have hkn : k.val < nc.val := by scalar_tac
      have hf := hcs.2 k.val (by omega)
      rw [if_pos hkn] at hf
      exact o_post.2 _ (by simpa only [hp, UScalar.ofNatCore_val_eq, Nat.cast_ofNat] using hf)
    · simp only [FieldPost, show o = some value by assumption] at o_post
      exact o_post.1
    · simp only [FieldPost, show o = some value by assumption] at o_post
      have hv : value.val < 256 := by have hb := o_post.2.2.2; scalar_tac
      have hc : i1.val = value.val := by
        rw [i1_post, UScalar.cast_val_eq]
        exact Nat.mod_eq_of_lt hv
      rw [index_mut_back_post, alloc.vec.Vec.set_val_eq, i_post, i2_post]
      apply cl_step _ _ _ _ _ (by scalar_tac) hcl
      have hf := o_post.2.1
      simpa only [hp, hc, UScalar.ofNatCore_val_eq, Nat.cast_ofNat] using hf

end Gzip.Proofs.Decode.ClImpl
