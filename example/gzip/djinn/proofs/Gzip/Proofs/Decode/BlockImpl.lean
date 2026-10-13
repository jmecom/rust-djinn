import Gzip.Proofs.Decode.BlockFacts

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.RoundTrip Gzip.Proofs.Decode.SymbolsFacts
open Gzip.Proofs.Decode.DynamicFacts Gzip.Proofs.Decode.DynamicImpl Gzip.Proofs.Decode.StoredImpl Gzip.Proofs.Decode.BlockFacts
open Gzip.Proofs.Decode.TablesImpl Gzip.Proofs.Decode.CodewordImpl

namespace Gzip.Proofs.Decode.BlockImpl

theorem fixedlit_bound (lit : List U8) (h : fixedlit_spec lit) :
    ∀ k, k < lit.length → (lit[k]!).val ≤ 15 := by
  intro k hk
  obtain ⟨v, hv, he⟩ := h.2.2 k (by omega) (by have hh := h.2.1; omega)
  simp only [Int.toNat_natCast] at he
  unfold fixedlen_spec at hv
  split_ifs at hv <;> omega

theorem fixeddist_bound (dist : List U8) (h : fixeddist_spec dist) :
    ∀ k, k < dist.length → (dist[k]!).val ≤ 15 := by
  intro k hk
  have hv := h.2.2 (dist[k]!) (by rw [getElem!_pos dist k hk]; exact List.getElem_mem hk)
  omega

theorem valid_bound (lens : List U8) (h : valid_spec lens 15 true) :
    ∀ k, k < lens.length → (lens[k]!).val ≤ 15 := by
  intro k hk
  have hv := (h.2.mp rfl).1 (lens[k]!) (by rw [getElem!_pos lens k hk]; exact List.getElem_mem hk)
  omega

set_option maxHeartbeats 2000000 in
@[step]
theorem decode_block_correct (s : Aeneas.Std.Slice U8) (r : Reader) (out : alloc.vec.Vec U8)
    (n : Usize) (cap : Nat) (h : Inv s r) (hn : n.val ≤ out.val.length)
    (hcap : cap + 24 ≤ out.val.length) :
    decode_block s r out n ⦃ z => ParsePost s cap out.val.length (block_spec s.val (pos r) (out.val.take n.val)) z ⦄ := by
  unfold decode_block
  step*
  all_goals try (rcases value1 with ⟨lit, dist⟩; have htpost := o1_post; clear o1_post)
  all_goals try step*
  all_goals simp_all only [FieldPost, TablePost, alloc.vec.Vec.deref, Slice.from_val,
    UScalar.ofNatCore_val_eq, Nat.cast_ofNat]
  all_goals try (have hfixedlen := v_post.2.1)
  all_goals try (have hdistlen := v1_post.2.1)
  all_goals try (have htb := tables_bounds _ _ _ _ _ htpost.2.2)
  all_goals try scalar_tac
  all_goals try exact fixedlit_bound _ v_post
  all_goals try exact fixeddist_bound _ v1_post
  all_goals try (
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hvl, hvd⟩ := (tables_iff _ _ _ _ _).mp htpost.2.2
    first | exact valid_bound _ hvl | exact valid_bound _ hvd)
  · intro final j hb hcap'
    obtain ⟨v, hv⟩ := block_has_field _ _ _ _ _ hb
    exact o_post.2 v hv
  · apply parse_post_congr s cap _ _ _ z ?_ z_post
    intro v j
    rw [block_at _ _ _ _ _ _ o_post.2.1]
    simp
  · apply parse_post_congr s cap _ _ _ z ?_ z_post
    intro w j
    rw [block_at _ _ _ _ _ _ o_post.2.1]
    simp only [Nat.cast_one, if_neg (by decide : (1 : ℤ) ≠ 0), if_pos rfl]
    constructor
    · rintro ⟨lit, dist, hl, hd, hs⟩
      rw [← fixedlit_unique _ _ v_post hl, ← fixeddist_unique _ _ v1_post hd] at hs
      exact hs
    · intro hs
      exact ⟨v.val, v1.val, v_post, v1_post, hs⟩
  · intro final j hb hcap'
    have hh := (block_at _ _ _ _ _ _ o_post.2.1).mp hb
    simp only [if_neg (by decide : (2 : ℤ) ≠ 0), if_neg (by decide : (2 : ℤ) ≠ 1)] at hh
    obtain ⟨_, lit, dist, k, ht, _⟩ := hh
    exact o1_post lit dist k ht
  · apply parse_post_congr s cap _ _ _ z ?_ z_post
    intro v j
    rw [block_at _ _ _ _ _ _ o_post.2.1]
    simp only [if_neg (by decide : (2 : ℤ) ≠ 0), if_neg (by decide : (2 : ℤ) ≠ 1)]
    constructor
    · rintro ⟨_, lit0, dist0, k, ht, hs⟩
      obtain ⟨hel, hed, hek⟩ := tables_unique _ _ _ _ _ _ _ _ htpost.2.2 ht
      simp only [← hel, ← hed, ← hek] at hs
      exact hs
    · intro hs
      exact ⟨trivial, lit.val, dist.val, _, htpost.2.2, hs⟩
  · intro final j hb hcap'
    have hh := (block_at _ _ _ _ _ _ o_post.2.1).mp hb
    split_ifs at hh <;> scalar_tac

end Gzip.Proofs.Decode.BlockImpl
