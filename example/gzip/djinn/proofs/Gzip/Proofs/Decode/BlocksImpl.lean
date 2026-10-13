import Gzip.Proofs.Decode.BlockImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.Encoding
open Gzip.Proofs.Decode.StoredImpl Gzip.Proofs.Decode.BlockFacts Gzip.Proofs.Decode.BlockImpl

namespace Gzip.Proofs.Decode.BlocksImpl

set_option maxHeartbeats 2000000 in
@[step]
theorem decode_blocks_correct (s : Aeneas.Std.Slice U8) (r : Reader) (out : alloc.vec.Vec U8)
    (n : Usize) (cap : Nat) (h : Inv s r) (hn : n.val ≤ out.val.length)
    (hcap : cap + 24 ≤ out.val.length) :
    decode_blocks s r out n ⦃ z => ParsePost s cap out.val.length (blocks_spec s.val (pos r) (out.val.take n.val)) z ⦄ := by
  generalize hm : (8 * (s.val.length : ℤ) - pos r).toNat = m
  induction m using Nat.strong_induction_on generalizing r out n with
  | h m ih =>
    have recur (r' : Reader) (out' : alloc.vec.Vec U8) (n' : Usize) (hr' : Inv s r')
        (hn' : n'.val ≤ out'.val.length) (hl' : out'.val.length = out.val.length)
        (hg : pos r < pos r') :
        decode_blocks s r' out' n' ⦃ z => ParsePost s cap out.val.length
          (blocks_spec s.val (pos r') (out'.val.take n'.val)) z ⦄ := by
      have hb := SymbolsImpl.inv_pos_bound _ _ hr'
      rw [← hl']
      exact ih _ (hm ▸ bit_measure_decreases s.val (pos r) (pos r') hg hb.2) r' out' n' hr' hn'
        (hl' ▸ hcap) rfl
    clear ih
    unfold decode_blocks
    step*
    all_goals simp_all only [BitPost, ParsePost, UScalar.ofNatCore_val_eq, Nat.cast_ofNat]
    all_goals try (have hb := block_bounds_length _ _ _ _ _ o1_post.2.2.2; omega)
    · intro final j hb hcap'
      obtain ⟨v, hv⟩ := blocks_has_bit _ _ _ _ _ (by unfold pos; omega) hb
      exact o_post.2 v hv
    · intro final j hb hcap'
      have hh := (blocks_at _ _ _ _ _ _ o_post.2.1).mp hb
      split_ifs at hh
      · obtain ⟨mid, k, hblock, hrec⟩ := hh
        have hl := blocks_length _ _ _ _ _ hrec
        exact o1_post mid k hblock (by omega)
      · exact o1_post final j hh hcap'
    · refine ⟨by first | trivial | exact o1_post.1,
        by first | trivial | exact o1_post.2.1 | (rw [← o1_post.2.2.1]; exact o1_post.2.1),
        by first | trivial | exact o1_post.2.2.1, (blocks_at _ _ _ _ _ _ o_post.2.1).mpr ?_⟩
      simpa using o1_post.2.2.2
    · have hv : value.val = 0 := by
        have hb := bit_range _ _ _ o_post.2.1
        scalar_tac
      have he (final : List U8) (j : ℤ) : blocks_spec s.val (pos r) (out.val.take n.val) final j ↔
          blocks_spec s.val (pos r2) (out1.val.take value1.val) final j := by
        rw [blocks_at _ _ _ _ _ _ o_post.2.1]
        simp only [hv, Nat.cast_zero, if_pos rfl]
        constructor
        · rintro ⟨mid, k, hblock, hrec⟩
          obtain ⟨hem, hek⟩ := block_unique _ _ _ _ _ _ _ o1_post.2.2.2 hblock
          simpa only [← hem, ← hek] using hrec
        · intro hr
          exact ⟨out1.val.take value1.val, pos r2, o1_post.2.2.2, hr⟩
      rcases z with ⟨res, r3, out2⟩
      cases res with
      | none =>
        intro final j hb hcap'
        exact z_post final j ((he final j).mp hb) hcap'
      | some u => exact ⟨z_post.1, z_post.2.1, z_post.2.2.1, (he _ _).mpr z_post.2.2.2⟩

end Gzip.Proofs.Decode.BlocksImpl
