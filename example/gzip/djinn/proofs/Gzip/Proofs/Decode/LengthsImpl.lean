import Gzip.Proofs.Decode.LengthsFacts
import Gzip.Proofs.Decode.RepeatImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.RunImpl Gzip.Proofs.Decode.RepeatImpl Gzip.Proofs.Decode.LengthsFacts
open Gzip.Proofs.Decode.CodewordTable Gzip.Proofs.Decode.DecodeTable

namespace Gzip.Proofs.Decode.LengthsImpl

def Bounds (all : List U8) : Prop := ∀ j, j < all.length → (all[j]!).val ≤ 15

def LengthPost (s : Aeneas.Std.Slice U8) (r : Reader) (cl : Aeneas.Std.Slice U8)
    (prev : List U8) (total : Nat) (z : Option Unit × Reader × alloc.vec.Vec U8) : Prop := match z.1 with
  | none => ∀ all j, all.length = total → all.take prev.length = prev →
      ¬ lengths_spec s.val (pos r) cl.val prev.length all j
  | some _ => Inv s z.2.1 ∧ z.2.2.val.length = total ∧ z.2.2.val.take prev.length = prev ∧
      Bounds z.2.2.val ∧ lengths_spec s.val (pos r) cl.val prev.length z.2.2.val (pos z.2.1)

theorem bounds_replicate (prev : List U8) (value : U8) (n : Nat)
    (hp : Bounds prev) (hv : value.val ≤ 15) : Bounds (prev ++ List.replicate n value) := by
  intro j hj
  by_cases hlt : j < prev.length
  · rw [List.getElem!_append_left prev _ j hlt]
    exact hp j hlt
  · simp only [List.length_append, List.length_replicate] at hj
    rw [List.getElem!_append_right prev _ j (by omega), List.getElem!_replicate value (by omega)]
    exact hv

theorem prefix_trans (all mid prev : List U8) (h1 : all.take mid.length = mid)
    (h2 : mid.take prev.length = prev) (hl : prev.length ≤ mid.length) : all.take prev.length = prev := by
  have he := congrArg (List.take prev.length) h1
  simp only [List.take_take, Nat.min_eq_left hl] at he
  exact he.trans h2

@[step]
theorem read_lengths_correct (s : Aeneas.Std.Slice U8) (r : Reader) (cl : Aeneas.Std.Slice U8)
    (codes : Aeneas.Std.Slice U32) (table : Array U32 2048#usize)
    (out : alloc.vec.Vec U8) (total : Usize) (h : Inv s r) (ho : out.val.length ≤ total.val)
    (hb : Bounds out.val) (ht : total.val ≤ 320) (hl : cl.val.length ≤ 320)
    (hcl : ∀ j, j < cl.val.length → (cl.val[j]!).val ≤ 15)
    (hcodes : codes.val.length = cl.val.length) (hentries : Entries cl.val codes.val)
    (hhints : Hints cl.val codes.val table.val false 7) :
    read_lengths s r cl codes table out total ⦃ z => LengthPost s r cl out.val total.val z ⦄ := by
  generalize hm : total.val - out.val.length = m
  induction m using Nat.strong_induction_on generalizing r out with
  | h m ih =>
    have recur (r' : Reader) (out' : alloc.vec.Vec U8) (hr' : Inv s r')
        (hg : out.val.length < out'.val.length) (ho' : out'.val.length ≤ total.val) (hb' : Bounds out'.val) :
        read_lengths s r' cl codes table out' total ⦃ z => LengthPost s r' cl out'.val total.val z ⦄ :=
      ih _ (by omega) r' out' hr' ho' hb' rfl
    clear ih
    unfold read_lengths
    step*
    all_goals try (rcases value with ⟨value1, count⟩)
    all_goals try step*
    all_goals try simp only [RunPost, show o = some (value1, count) by assumption,
      alloc.vec.Vec.deref, Slice.from_val] at o_post
    all_goals try simp only [RunPost, show o = none by assumption, alloc.vec.Vec.deref, Slice.from_val] at o_post
    all_goals try exact o_post.1
    all_goals try (
      have hc := o_post.2.1
      rw [all1_post, List.length_append, List.length_replicate]
      omega)
    all_goals try (rw [all1_post]; exact bounds_replicate _ _ _ hb o_post.2.2.2.1)
    · refine ⟨h, by scalar_tac, by simp, hb, ?_⟩
      change lengths_spec s.val (pos r) cl.val out.val.length out.val (pos r)
      rw [lengths_spec]
      refine ⟨⟨by omega, by omega⟩, fun _ => ⟨fun _ => rfl, fun he => (he rfl).elim⟩⟩
    · simpa only [alloc.vec.Vec.deref, Slice.from_val, Bounds] using hb
    · intro all j htotal hpre hs
      have hlt : out.val.length < all.length := by scalar_tac
      obtain ⟨v, n, a, hr, _⟩ := (lengths_unfold _ _ _ _ _ _ hlt hpre).mp hs
      exact o_post v n a hr
    · intro all j htotal hpre hs
      have hlt : out.val.length < all.length := by scalar_tac
      have hstep := (lengths_step_iff s.val cl.val out.val all (pos r) (pos r1) j value1 count.val
        hlt hpre (by have hcount := o_post.2.1; omega) o_post.2.2.2.2).mp hs
      scalar_tac
    · have hlen : all1.val.length = out.val.length + count.val := by
        rw [all1_post, List.length_append, List.length_replicate]
      have hprefix : all1.val.take out.val.length = out.val := by
        rw [all1_post]
        simp
      rcases z with ⟨res, r', final⟩
      cases res with
      | none =>
        intro all j htotal hpre hs
        have hlt : out.val.length < all.length := by scalar_tac
        obtain ⟨hbound, hpref, hrec⟩ := (lengths_step_iff s.val cl.val out.val all (pos r) (pos r1) j value1 count.val
          hlt hpre (by have hc := o_post.2.1; omega) o_post.2.2.2.2).mp hs
        apply z_post all j htotal
        · simpa only [hlen, all1_post, List.length_append, List.length_replicate] using hpref
        · simpa only [hlen] using hrec
      | some u =>
        obtain ⟨hr', htotal, hpref, hbounds, hrec⟩ := z_post
        have hpref' := prefix_trans final.val all1.val out.val hpref hprefix (by omega)
        refine ⟨hr', htotal, hpref', hbounds, ?_⟩
        apply (lengths_step_iff s.val cl.val out.val final.val (pos r) (pos r1) (pos r') value1 count.val
          (by scalar_tac) hpref' (by have hc := o_post.2.1; omega) o_post.2.2.2.2).mpr
        refine ⟨?_, ?_, ?_⟩
        · scalar_tac
        · simpa only [hlen, all1_post, List.length_append, List.length_replicate] using hpref
        · simpa only [hlen] using hrec

end Gzip.Proofs.Decode.LengthsImpl
