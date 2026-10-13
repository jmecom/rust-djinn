import Gzip.Proofs.Decode.ReaderImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.Parsing

namespace Gzip.Proofs.Decode.StoredImpl

theorem u16_range (s : List U8) (i v : ℤ) (h : u16le_spec s i v) : 0 ≤ v ∧ v ≤ 65535 := by
  obtain ⟨_, _, he⟩ := h
  have h0 := (s[i.toNat]!).hBounds
  have h1 := (s[(i + 1).toNat]!).hBounds
  scalar_tac

theorem stored_iff (s prev out : List U8) (i j : ℤ) :
    stored_spec s i prev out j ↔ ∃ len : ℤ,
      u16le_spec s ((i + 7) / 8) len ∧
      u16le_spec s ((i + 7) / 8 + 2) (65535 - len) ∧
      ((i + 7) / 8 + 4) + len ≤ s.length ∧
      out = prev ++ ((s.drop (((i + 7) / 8 + 4).toNat)).take len.toNat) ∧
      j = 8 * (((i + 7) / 8 + 4) + len) := by
  constructor
  · rintro ⟨_, a, len, rfl, hlen, hneg, hbound, hsize, hpre, htail, hj⟩
    refine ⟨len, hlen, hneg, hbound, ?_, hj⟩
    have hr := u16_range _ _ _ hlen
    simp only [List.drop_zero, Int.toNat_natCast] at hpre htail
    have he : ((out.length : ℤ) - prev.length).toNat = out.length - prev.length := by omega
    rw [he, ← List.length_drop, List.take_length] at htail
    have hlen' : ((i + 7) / 8 + 4 + len - ((i + 7) / 8 + 4)).toNat = len.toNat := by congr 1; omega
    rw [hlen'] at htail
    have heq := congrArg₂ (fun a b : List U8 => a ++ b) hpre htail
    simpa only [List.take_append_drop] using heq
  · rintro ⟨len, hlen, hneg, hbound, rfl, hj⟩
    have hr := u16_range _ _ _ hlen
    have ha : 0 ≤ (i + 7) / 8 := hlen.2.1.1
    have htake : len.toNat ≤ (s.drop (((i + 7) / 8 + 4).toNat)).length := by
      simp only [List.length_drop]
      omega
    refine ⟨trivial, (i + 7) / 8, len, rfl, hlen, hneg, hbound, ?_, ?_, ?_, hj⟩
    · simp only [List.length_append, List.length_take, Nat.min_eq_left htake]
      omega
    · simp only [List.drop_zero, Int.toNat_natCast, List.take_append, List.take_length,
        Nat.sub_self, List.take_zero, List.append_nil]
    · simp only [Int.toNat_natCast, List.drop_left]
      have he : (((prev ++ (s.drop (((i + 7) / 8 + 4).toNat)).take len.toNat).length : ℤ) - prev.length).toNat = len.toNat := by
        simp only [List.length_append, List.length_take, Nat.min_eq_left htake]
        omega
      rw [he, List.take_take, Nat.min_self]
      congr 1
      congr 1
      omega

@[step]
theorem align_reader_correct (s : Aeneas.Std.Slice U8) (r : Reader) (h : Inv s r) :
    align_reader r ⦃ q => Inv s q ∧ q.bit.val = 0 ∧ (q.byte.val : ℤ) = (pos r + 7) / 8 ⦄ := by
  obtain ⟨hbyte, hbit, hend⟩ := h
  unfold align_reader
  step*
  all_goals
    unfold ReaderImpl.Inv pos
    refine ⟨⟨by scalar_tac, by scalar_tac, by scalar_tac⟩, by scalar_tac, by scalar_tac⟩

/-- Writing the byte at `n` of a buffer extends its prefix of length `n` by that byte. -/
theorem take_set_succ (l : List U8) (n : Nat) (x : U8) (hn : n < l.length) :
    (l.set n x).take (n + 1) = l.take n ++ [x] := by
  rw [List.take_succ_eq_append_getElem (by simp only [List.length_set]; exact hn)]
  rw [List.take_set, List.set_eq_of_length_le (by simp only [List.length_take]; omega)]
  simp only [List.getElem_set_self]

/-- The output buffer is written in place: the parsers return the position after what they
wrote, and the buffer's length never changes. -/
def ParsePost (s : Aeneas.Std.Slice U8) (cap len0 : Nat) (R : List U8 → ℤ → Prop)
    (z : Option Usize × Reader × alloc.vec.Vec U8) : Prop := match z.1 with
  | none => ∀ v j, R v j → v.length ≤ cap → False
  | some n => Inv s z.2.1 ∧ n.val ≤ z.2.2.val.length ∧ z.2.2.val.length = len0 ∧
      R (z.2.2.val.take n.val) (pos z.2.1)

theorem parse_post_congr (s : Aeneas.Std.Slice U8) (cap len0 : Nat) (R Q : List U8 → ℤ → Prop)
    (z : Option Usize × Reader × alloc.vec.Vec U8) (h : ∀ v j, R v j ↔ Q v j)
    (hp : ParsePost s cap len0 Q z) : ParsePost s cap len0 R z := by
  cases hz : z.1 with
  | none =>
    simp only [ParsePost, hz] at hp ⊢
    intro v j hr hb
    exact hp v j ((h v j).mp hr) hb
  | some u =>
    simp only [ParsePost, hz] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1, (h _ _).mpr hp.2.2.2⟩

def CopyInv (s : Aeneas.Std.Slice U8) (start : Nat) (prev : List U8) (len0 : Nat) (n0 : Nat)
    (finish : Usize) (st : Usize × alloc.vec.Vec U8 × Usize) : Prop :=
  start ≤ st.1.val ∧ st.1.val ≤ finish.val ∧ st.2.2.val = n0 + (st.1.val - start) ∧
  st.2.1.val.length = len0 ∧ st.2.1.val.take st.2.2.val = prev ++ (s.val.drop start).take (st.1.val - start)

theorem stored_body (s : Aeneas.Std.Slice U8) (start : Nat) (prev : List U8) (len0 n0 : Nat)
    (finish i : Usize) (out : alloc.vec.Vec U8) (n : Usize) (hend : finish.val ≤ s.val.length)
    (hcap : n0 + (finish.val - start) ≤ len0)
    (h : CopyInv s start prev len0 n0 finish (i, out, n)) :
    decode_stored_loop.body s finish i out n ⦃ z => match z with
      | .done (j, v, m) => j = finish ∧ m.val = n0 + (finish.val - start) ∧ v.val.length = len0 ∧
          v.val.take m.val = prev ++ (s.val.drop start).take (finish.val - start)
      | .cont st => CopyInv s start prev len0 n0 finish st ∧ finish.val - st.1.val < finish.val - i.val ⦄ := by
  obtain ⟨hstart, hi, hn, hlen, hout⟩ := h
  simp only at hstart hi hn hlen hout
  unfold decode_stored_loop.body
  step*
  all_goals try scalar_tac
  · refine ⟨⟨by scalar_tac, by scalar_tac, by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
    · rw [index_mut_back_post]
      simp only [alloc.vec.Vec.set_val_eq, List.length_set]
      exact hlen
    · rw [index_mut_back_post]
      simp only [alloc.vec.Vec.set_val_eq]
      have hk : i.val - start < (s.val.drop start).length := by simp only [List.length_drop]; scalar_tac
      have hj : i2.val - start = (i.val - start) + 1 := by scalar_tac
      rw [n1_post, take_set_succ _ _ _ (by scalar_tac), hout, hj,
        List.take_succ_eq_append_getElem hk, List.append_assoc]
      congr 2
      rw [List.getElem_drop]
      have he : start + (i.val - start) = i.val := by omega
      simpa only [he] using congrArg (fun v : U8 => [v]) i1_post
  all_goals try (
    have hif : i = finish := by scalar_tac
    subst hif
    exact ⟨rfl, hn, hlen, hout⟩)

@[step]
theorem stored_loop_correct (s : Aeneas.Std.Slice U8) (start finish : Usize) (out : alloc.vec.Vec U8)
    (n : Usize) (hs : start.val ≤ finish.val) (hf : finish.val ≤ s.val.length)
    (hn : n.val ≤ out.val.length) (hcap : n.val + (finish.val - start.val) ≤ out.val.length) :
    decode_stored_loop s start out finish n ⦃ z => z.1 = finish ∧
      z.2.2.val = n.val + (finish.val - start.val) ∧ z.2.1.val.length = out.val.length ∧
      z.2.1.val.take z.2.2.val = out.val.take n.val ++ (s.val.drop start.val).take (finish.val - start.val) ⦄ := by
  unfold decode_stored_loop
  apply loop.spec_decr_nat (fun (i, _) => finish.val - i.val)
    (fun st => CopyInv s start.val (out.val.take n.val) out.val.length n.val finish st)
  · rintro ⟨i, v, m⟩ hinv
    apply WP.spec_mono (stored_body s start.val (out.val.take n.val) out.val.length n.val finish i v m hf hcap hinv)
    intro z hz
    cases z <;> exact hz
  · exact ⟨_root_.le_refl _, hs, by simp, rfl, by simp⟩

set_option maxHeartbeats 2000000 in
@[step]
theorem decode_stored_correct (s : Aeneas.Std.Slice U8) (r : Reader) (out : alloc.vec.Vec U8)
    (n : Usize) (cap : Nat) (h : Inv s r) (hn : n.val ≤ out.val.length)
    (hcap : cap + 24 ≤ out.val.length) :
    decode_stored s r out n ⦃ z => ParsePost s cap out.val.length (stored_spec s.val (pos r) (out.val.take n.val)) z ⦄ := by
  have halign := align_reader_correct s r h
  have hprev : (out.val.take n.val).length = n.val := List.length_take_of_le hn
  unfold decode_stored
  step*
  all_goals try simp only [NumPost, show o = some value by assumption] at o_post
  all_goals try simp only [NumPost, show o = none by assumption] at o_post
  all_goals try simp only [NumPost, show o1 = some value1 by assumption] at o1_post
  all_goals try simp only [NumPost, show o1 = none by assumption] at o1_post
  all_goals try (
    have hv := u16_range _ _ _ o_post
    have hlen : len.val = value.val := by
      rw [len_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac)
  all_goals try (
    have hv1 := u16_range _ _ _ o1_post
    have hi1 : i1.val = value.val := by
      rw [i1_post, UScalar.cast_val_eq, hlen]
      apply Nat.mod_eq_of_lt
      scalar_tac)
  all_goals try (have hbd := o_post.2.1; scalar_tac)
  all_goals try (have hbd := o1_post.2.1; scalar_tac)
  all_goals try scalar_tac
  all_goals try (
    intro v j hs hvlen
    obtain ⟨_, a, len', ha, hla, hneg, hbound, hsize, _, _, _⟩ := hs
    have ha' : a = r1.byte.val := by omega
    rw [ha'] at hla hneg hbound)
  all_goals try (
    have he := u16_unique _ _ _ _ o_post hla
    rw [hprev] at hsize
    have hl := alloc.vec.Vec.len_val out
    scalar_tac)
  · exact o_post len' hla
  · apply o1_post (65535 - len')
    have he : (i.val : ℤ) = (r1.byte.val : ℤ) + 2 := by omega
    rw [he]
    exact hneg
  · have he := u16_unique _ _ _ _ o_post hla
    have hi : (i.val : ℤ) = (r1.byte.val : ℤ) + 2 := by omega
    rw [← hi] at hneg
    have he' := u16_unique _ _ _ _ o1_post hneg
    scalar_tac
  · refine ⟨?_, ?_, ?_, (stored_iff _ _ _ _ _).mpr ?_⟩
    · unfold ReaderImpl.Inv
      simp only
      refine ⟨?_, by omega, by omega⟩
      rw [i9_post]
      scalar_tac
    · rw [i9_post2, i9_post1]
      scalar_tac
    · exact i9_post2
    · refine ⟨value.val, ?_, ?_, ?_, ?_, ?_⟩
      · rwa [← r1_post2]
      · have he : (i.val : ℤ) = (pos r + 7) / 8 + 2 := by omega
        rw [← he]
        have hsum : (value1.val : ℤ) = 65535 - value.val := by scalar_tac
        rwa [← hsum]
      · scalar_tac
      · rw [i9_post3]
        congr 2
        · omega
        · congr 1; omega
      · change 8 * (i9.val : ℤ) + r1.bit.val = 8 * ((pos r + 7) / 8 + 4 + value.val)
        rw [i9_post]
        scalar_tac

end Gzip.Proofs.Decode.StoredImpl
