import Gzip.Proofs.Decode.DynamicFacts
import Gzip.Proofs.Decode.LengthsWindow

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.RoundTrip Gzip.Proofs.Decode.ClImpl
open Gzip.Proofs.Decode.DynamicFacts Gzip.Proofs.Decode.LengthsImpl Gzip.Proofs.Decode.CodewordImpl
open Gzip.Proofs.Decode.RunImpl Gzip.Proofs.Decode.LengthsWindow

namespace Gzip.Proofs.Decode.DynamicImpl
set_option maxHeartbeats 2000000

def TablePost (s : Aeneas.Std.Slice U8) (r : Reader)
    (z : Option (alloc.vec.Vec U8 × alloc.vec.Vec U8) × Reader) : Prop := match z.1 with
  | none => ∀ lit dist j, ¬ tables_spec s.val (pos r) lit dist j
  | some (lit, dist) => Inv s z.2 ∧ pos r < pos z.2 ∧ tables_spec s.val (pos r) lit.val dist.val (pos z.2)

@[step]
theorem dynamic_tables_correct (s : Aeneas.Std.Slice U8) (r : Reader) (h : Inv s r) :
    dynamic_tables s r ⦃ z => TablePost s r z ⦄ := by
  unfold dynamic_tables
  step*
  case i => exact pos r + 14
  all_goals try step*
  all_goals simp_all only [FieldPost, ClPost, LengthPost, alloc.vec.Vec.deref, Slice.from_val, cast_usize, UScalar.ofNatCore_val_eq, Nat.cast_ofNat, Prod.fst, Prod.snd]
  all_goals try simp only [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append, List.length_nil, List.drop_zero] at *
  all_goals try (have hcllen := o3_post.2.2.1)
  all_goals try (have hcb := cl_bound _ _ _ _ o3_post.2.2)
  all_goals try (
    have hllen : lit.val.length = nl.val := by rw [lit_post]; simp only [List.length_take]; omega)
  all_goals try (
    have hdlen : dist.val.length = nd.val := by rw [dist_post]; simp only [List.length_take, List.length_drop]; omega)
  all_goals try scalar_tac
  all_goals try exact cl_zero _ _
  all_goals try (intro j hj; simp at hj)
  all_goals try (intro j hj; have hb := hcb j hj; omega)
  all_goals have hpos : 0 ≤ pos r := by unfold pos; omega
  all_goals try (
    intro lit0 dist0 j ht
    obtain ⟨n0, cs, whole, hl, hd, hc, hn0, hn1, hcs, hvalid, hwlen, hprefix, htail, hlens, hvl, hvd⟩ :=
      (tables_iff _ _ _ _ _).mp ht)
  all_goals try (
    have hll : lit0.length = nl.val := by
      have he := Decoding.field_unique _ _ _ _ _ o_post.2.1 hl; omega)
  all_goals try (
    have hdl : dist0.length = nd.val := by
      have he := Decoding.field_unique _ _ _ _ _ o1_post.2.1 hd; omega)
  all_goals try (
    have hnc : n0 = 4 + value2.val := by
      have he := Decoding.field_unique _ _ _ _ _ o2_post.2.1 hc; omega)
  all_goals try simp only [hnc] at hcs hlens
  all_goals try (have hecl : cl2.val = cs := cl_unique _ _ _ _ _ o3_post.2.2 hcs)
  all_goals try simp only [← hecl] at hlens hvalid
  · exact o_post.2 _ hl
  · exact o1_post.2 _ hd
  · exact o2_post.2 _ hc
  · exact o3_post cs hcs
  · exact o4_post whole j (by omega) (by simp) hlens
  · refine ⟨o4_post.1, ?_, (tables_iff _ _ _ _ _).mpr ?_⟩
    · change pos r < pos r5
      have hm := lengths_mono _ _ _ _ _ _ o4_post.2.2.2.2
      omega
    · refine ⟨4 + value2.val, cl2.val, all1.val, ?_, ?_, ?_, by omega, ?_, o3_post.2.2,
        b_post, ?_, ?_, ?_, o4_post.2.2.2.2, ?_, ?_⟩
      · convert o_post.2.1 using 1 <;> omega
      · convert o1_post.2.1 using 1 <;> omega
      · convert o2_post.2.1 using 1 <;> omega
      · have hb := o2_post.2.2.2; omega
      · omega
      · simpa only [hllen, nl_post] using lit_post.symm
      · have hdrop : (all1.val.drop (257 + value.val)).length = 1 + value1.val := by
          simp only [List.length_drop]; omega
        simpa only [hllen, nl_post, ← hdrop, List.take_length] using dist_post.symm
      · simpa only [lit_post] using b1_post
      · simpa only [dist_post] using b2_post
  all_goals try (
    have heall := lengths_unique s.val cl2.val all1.val whole _ 0 (pos r5) j
      (by omega) (by intro q hq hq0; omega) o4_post.2.2.2.2 hlens)
  all_goals try (
    have helit : lit.val = lit0 := by
      rw [lit_post, heall.1, ← nl_post, ← hll]; exact hprefix)
  all_goals try (
    have hedist : dist.val = dist0 := by
      have hdrop : (whole.drop lit0.length).length = dist0.length := by simp only [List.length_drop]; omega
      rw [dist_post, heall.1, ← nl_post, ← nd_post, ← hll, ← hdl, ← hdrop, List.take_length]
      exact htail)
  · have hbtrue := hvd.2.mp rfl
    have hbfalse := b2_post.2.mpr
    rw [← hedist, dist_post] at hbtrue
    have he := hbfalse hbtrue
    contradiction
  · have hbtrue := hvl.2.mp rfl
    have hbfalse := b1_post.2.mpr
    rw [← helit, lit_post] at hbtrue
    have he := hbfalse hbtrue
    contradiction
  · have he := b_post.2.mpr (hvalid.2.mp rfl)
    contradiction


end Gzip.Proofs.Decode.DynamicImpl
