import Gzip.Proofs.Decode.BlocksImpl
import Gzip.Proofs.Decode.HeaderImpl
import Gzip.Proofs.Decode.CrcImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.HeaderImpl
open Gzip.Proofs.Decode.StoredImpl Gzip.Proofs.Decode.BlockFacts Gzip.Proofs.Decode.BlocksImpl

namespace Gzip.Proofs.Decode.DecompressImpl

def DecPost (s : List U8) (res : Option (alloc.vec.Vec U8)) : Prop := match res with
  | none => ∀ out, member_spec s out → out.length ≤ 1073741824 → False
  | some out => member_spec s out.val ∧ out.val.length ≤ 1073741824

theorem dec_post_spec (s : List U8) (res : Option (alloc.vec.Vec U8)) (h : DecPost s res) :
    decompress_spec s (res.map (fun v => v.val)) := by
  cases res with
  | none =>
    refine ⟨trivial, ⟨by simp, ?_⟩, by simp⟩
    rintro ⟨_, out, hm, hcap⟩
    exact (h out hm (by omega)).elim
  | some v =>
    refine ⟨trivial, ⟨fun _ => ⟨⟨trivial, v.val, h.1⟩, v.val, h.1, by have hb := h.2; omega⟩,
      fun _ => rfl⟩, fun _ => ?_⟩
    exact h.1

@[step]
theorem crc_correct (data : Aeneas.Std.Slice U8) :
    crc32_wide data ⦃ c => crc32_spec data.val c ⦄ :=
  CrcImpl.crc32_correct data

theorem u32_unique (s : List U8) (i a b : ℤ) (ha : u32le_spec s i a) (hb : u32le_spec s i b) : a = b := by
  obtain ⟨_, x, hx, y, hy, he⟩ := ha
  obtain ⟨_, x1, hx1, y1, hy1, he1⟩ := hb
  have heq := u16_unique _ _ _ _ hx hx1
  have heq1 := u16_unique _ _ _ _ hy hy1
  omega

theorem resize_take (l : List U8) (n : Nat) (hn : n ≤ l.length) : l.resize n 0#u8 = l.take n := by
  simp only [List.resize, ge_iff_le, Nat.zero_le, if_true, Nat.sub_eq_zero_of_le hn,
    List.replicate_zero, List.append_nil]

/-- The length field of the trailer is the length of the content, when there is one. -/
theorem member_length (s final : List U8) (h : member_spec s final) (hcap : final.length ≤ 1073741824)
    (v : ℤ) (hv : u32le_spec s (s.length - 4) v) : v = final.length := by
  obtain ⟨_, start, finish, trailer, hh, hb, ht, hlen, _, hsize⟩ := h
  have he : (s.length : ℤ) - 4 = trailer + 4 := by omega
  rw [he] at hv
  have hu := u32_unique _ _ _ _ hv hsize
  omega

set_option maxHeartbeats 4000000 in
theorem decompress_correct (crc_unique : ∀ data x y, crc32_spec data x → crc32_spec data y → x = y)
    (s : Aeneas.Std.Slice U8) :
    decompress s ⦃ res => DecPost s.val res ⦄ := by
  have align (r : Reader) (h : Inv s r) := align_reader_correct s r h
  have hfrom (n : Usize) := alloc.vec.from_elem_spec core.clone.CloneU8 0#u8 n rfl
  have hresize (v : alloc.vec.Vec U8) (n : Usize) :=
    alloc.vec.Vec.resize_spec core.clone.CloneU8 v n 0#u8 rfl
  unfold decompress
  step*
  all_goals simp_all only [HeaderPost, ParsePost, NumPost, alloc.vec.Vec.deref, Slice.from_val,
    UScalar.ofNatCore_val_eq, Nat.cast_ofNat, List.take_zero]
  all_goals try (unfold ReaderImpl.Inv; simp; omega)
  all_goals try (have hb := r1_post.1; scalar_tac)
  all_goals try (
    intro final hm hcap
    obtain ⟨_, start, finish, trailer, hh, hb, ht, hlen, ⟨crc, hcrc, cval, hcval, hceq⟩, hsize⟩ := hm)
  all_goals try (
    have heh := header_unique _ _ _ o_post.1 hh
    simp only [← heh] at hb)
  all_goals try (
    have heout := blocks_unique _ _ _ _ _ _ _ o2_post.2.2.2 hb
    simp only [← heout.1, ← heout.2] at hcrc ht hsize hcap)
  all_goals try simp only [ht] at hlen hcval hsize
  all_goals try (
    have hcl : claimed.val = value1.val := by
      rw [claimed_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac)
  · exact o_post start hh
  · have h10 := o_post.1.2.1
    scalar_tac
  · apply o1_post ((final.length : ℤ) % 4294967296)
    have he : (((s.len.val - 4 : ℕ)) : ℤ) = (finish + 7) / 8 + 4 := by scalar_tac
    rw [he]
    exact hsize
  · have hcv : (UScalar.cast UScalarTy.Usize value1).val = value1.val := by
      rw [UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
    have hcap_step : (if UScalar.cast UScalarTy.Usize value1 > 1073741824#usize then ok 1073741824#usize
        else ok (UScalar.cast UScalarTy.Usize value1) : Result Usize)
        ⦃ c => c.val = min value1.val 1073741824 ⦄ := by
      split
      all_goals first
        | (step*; scalar_tac)
        | (simp only [WP.spec, min_def]; split_ifs <;> scalar_tac)
        | (rw [WP.spec_equiv_exists]; refine ⟨_, rfl, ?_⟩; simp only [min_def]; split_ifs <;> scalar_tac)
    step with hcap_step as ⟨cap, cap_post⟩
    step
    step with (hfrom i2) as ⟨out, out_post, out_post1⟩
    have hinv0 : Inv s { byte := value, bit := 0#u32 } := by
      unfold ReaderImpl.Inv
      simp only
      exact ⟨o_post.2, by decide, fun _ => rfl⟩
    have hblocks := decode_blocks_correct s { byte := value, bit := 0#u32 } out 0#usize cap.val hinv0
      (by simp) (by rw [out_post, List.length_replicate, i2_post]; omega)
    have hol : (((s.len.val - 4 : ℕ)) : ℤ) = (s.val.length : ℤ) - 4 := by scalar_tac
    rw [hol] at o1_post
    step with hblocks as ⟨o2, r, out1, o2_post⟩
    step*
    all_goals try simp only [ParsePost, show o2 = some value2 by assumption, List.take_zero] at o2_post
    all_goals try simp only [ParsePost, show o2 = none by assumption, List.take_zero] at o2_post
    all_goals try exact o2_post.1
    all_goals try (
      intro final hm hcap
      have hfl := member_length s.val final hm hcap value1.val o1_post
      obtain ⟨_, start, finish, trailer, hh, hb, ht, hlen, ⟨crc, hcrc, cval, hcval, hceq⟩, hsize⟩ := hm
      have heh := header_unique _ _ _ o_post.1 hh
      simp only [← heh] at hb)
    all_goals try (
      have heout := blocks_unique _ _ _ _ _ _ _ o2_post.2.2.2 hb
      have hfinal := heout.1
      have hfin := heout.2
      have hlt : (out1.val.take value2.val).length = value2.val := List.length_take_of_le o2_post.2.1
      subst hfinal
      simp only [← hfin] at ht hsize hcval hlen)
    · exact o2_post final finish hb (by omega)
    · scalar_tac
    · scalar_tac
    · scalar_tac
    · scalar_tac
    all_goals
      have hout2 : out2.val = out1.val.take value2.val := by
        rw [out2_post]
        exact resize_take _ _ o2_post.2.1
      have hl2 : out2.val.length = value2.val := by
        rw [hout2]
        exact List.length_take_of_le o2_post.2.1
      have hr1 : ((r1.byte.val : ℕ) : ℤ) = (pos r + 7) / 8 := r1_post2
    all_goals try simp only [NumPost, show o3 = some value3 by assumption] at o3_post
    all_goals try simp only [NumPost, show o3 = none by assumption] at o3_post
    all_goals try simp only [NumPost, show o4 = some value4 by assumption] at o4_post
    all_goals try simp only [NumPost, show o4 = none by assumption] at o4_post
    all_goals try simp only [Slice.from_val, hout2] at i7_post
    all_goals try (
      have hv3 := u32_unique _ _ _ _ o3_post (by rw [hr1, ← ht]; exact hcval))
    all_goals try (
      have hi8 : ((i8.val : ℕ) : ℤ) = trailer + 4 := by omega)
    all_goals try (
      have hv4 := u32_unique _ _ _ _ o4_post (by rw [hi8]; exact hsize))
    all_goals try (
      have hec := crc_unique _ _ _ i7_post hcrc)
    all_goals try (
      have hi10 : i10.val = value2.val := by
        rw [i10_post, UScalar.cast_val_eq]
        have hl := alloc.vec.Vec.len_val out2
        have hl' : out2.length = out2.val.length := rfl
        rw [hl, hl', hl2]
        apply Nat.mod_eq_of_lt
        scalar_tac)
    · exact o3_post cval (by rw [hr1, ← ht]; exact hcval)
    · scalar_tac
    · exact o4_post _ (by rw [hi8]; exact hsize)
    · have hmod : ((out1.val.take value2.val).length : ℤ) % 4294967296 = (out1.val.take value2.val).length := by
        apply Int.emod_eq_of_lt <;> omega
      rw [hmod] at hv4
      scalar_tac
    · have hv3 : value3 = i7 := by
        apply UScalar.eq_of_val_eq
        scalar_tac
      have hv4 : value4 = i10 := by
        apply UScalar.eq_of_val_eq
        scalar_tac
      refine ⟨⟨trivial, value.val, pos r, (pos r + 7) / 8, o_post.1, ?_, rfl, ?_, ?_, ?_⟩, ?_⟩
      · rw [hout2]
        exact o2_post.2.2.2
      · scalar_tac
      · refine ⟨i7, by rw [hout2]; exact i7_post, value3.val, by rw [← hr1]; exact o3_post, ?_⟩
        rw [hv3]
      · have hmod : (out2.val.length : ℤ) % 4294967296 = value4.val := by
          rw [hl2, hv4, hi10]
          apply Int.emod_eq_of_lt <;> scalar_tac
        rw [hmod]
        have hi8 : ((i8.val : ℕ) : ℤ) = (pos r + 7) / 8 + 4 := by omega
        rw [← hi8]
        exact o4_post
      · rw [hl2]
        scalar_tac

end Gzip.Proofs.Decode.DecompressImpl
