/- Specification obligations and refinement proofs for the optimal LZ77 encoder. -/
import Aeneas
import Lz77.Spec
import Lz77.Vocab
import Lz77.Code.Funs

open Aeneas Std Result
open Lz77.Spec
open Djinn.Vocab

namespace Lz77.Proofs

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

/-! ## copies -/

theorem copies.wf :
    ∀ (l : ℤ) (s : List U8) (j : ℤ) (d : ℤ) (b : Bool),
      copies_spec l s j d b →
      (¬(l = 0) → (0 ≤ j ∧ j < (s.length : ℤ)) ∧ (0 ≤ (j - d) ∧ (j - d) < (s.length : ℤ))) ∧
      (¬(l = 0) → s[j.toNat]! = s[(j - d).toNat]! → (copies_pre (l - 1) s (j + 1) d)) := by
  intro l s j d b h
  rw [copies_spec] at h
  have hp := h.1
  unfold copies_pre at *
  omega

/-! ## ismatch -/

theorem ismatch.wf :
    ∀ (s : List U8) (j : ℤ) (d : ℤ) (l : ℤ) (b : Bool),
      ismatch_spec s j d l b →
      (((((1 ≤ d ∧ d ≤ 32768) ∧ d ≤ j) ∧ 3 ≤ l) ∧ l ≤ 258) ∧ (j + l) ≤ (s.length : ℤ)) → (copies_pre l s j d) := by
  intro s j d l b h hp
  unfold copies_pre
  omega

/-! ## toklen -/

theorem toklen.unambiguous :
    ∀ (t : Lz77.spec.Token) (o₁ : U32) (o₂ : U32),
      toklen_spec t o₁ → toklen_spec t o₂ → o₁ = o₂ := by
  intro t a b ha hb
  cases t <;> simp only [toklen_spec, toklen_pre, true_and] at ha hb
  · apply UScalar.eq_of_val_eq
    omega
  · exact ha.trans hb.symm

/-! ## encoded -/

def tokenLength : Lz77.spec.Token → U32
  | .Lit _ => 1#u32
  | .Match _ l => l

theorem toklen_iff (t : Lz77.spec.Token) (n : U32) :
    toklen_spec t n ↔ n = tokenLength t := by
  cases t <;> simp only [toklen_spec, toklen_pre, true_and, tokenLength]
  constructor
  · intro h; apply UScalar.eq_of_val_eq; simpa using h
  · intro h; subst n; rfl


theorem encoded.wf :
    ∀ (ts : List Lz77.spec.Token) (m : ℤ),
      encoded_spec ts m →
      (¬((ts.length : ℤ) = 0) → (0 ≤ 0 ∧ 0 ≤ ((ts.length : ℤ) - 1) ∧ ((ts.length : ℤ) - 1) ≤ (ts.length : ℤ))) ∧
      (¬((ts.length : ℤ) = 0) → ∀ v_call0 : ℤ, encoded_spec ((ts.drop 0).take (((ts.length : ℤ) - 1)).toNat) v_call0 → (0 ≤ ((ts.length : ℤ) - 1) ∧ ((ts.length : ℤ) - 1) < (ts.length : ℤ))) := by
  intro ts m h
  constructor <;> intros <;> omega

/-! ## decode -/

theorem decode.wf :
    ∀ (ts : List Lz77.spec.Token) (s : List U8),
      decode_spec ts s →
      (¬((ts.length : ℤ) = 0) → ∀ p : List U8, (decode_spec ((ts.drop 0).take (((ts.length : ℤ) - 1)).toNat) p ∧ (match ts[((ts.length : ℤ) - 1).toNat]! with | .Lit ch_0 => ((s.length : ℤ) = ((p.length : ℤ) + 1) ∧ ((s.drop 0).take ((p.length : ℤ)).toNat) = p ∧ s[(p.length : ℤ).toNat]! = ch_0) | .Match dist_0 len_1 => ((1 ≤ (dist_0.val : ℤ) ∧ (dist_0.val : ℤ) ≤ (p.length : ℤ)) ∧ 1 ≤ (len_1.val : ℤ) ∧ (s.length : ℤ) = ((p.length : ℤ) + (len_1.val : ℤ)) ∧ ((s.drop 0).take ((p.length : ℤ)).toNat) = p ∧ (∀ k : ℤ, (p.length : ℤ) ≤ k → k < (s.length : ℤ) → s[k.toNat]! = s[(k - (dist_0.val : ℤ)).toNat]!)))) → (0 ≤ 0 ∧ 0 ≤ ((ts.length : ℤ) - 1) ∧ ((ts.length : ℤ) - 1) ≤ (ts.length : ℤ))) ∧
      (¬((ts.length : ℤ) = 0) → ∀ p : List U8, (decode_spec ((ts.drop 0).take (((ts.length : ℤ) - 1)).toNat) p ∧ (match ts[((ts.length : ℤ) - 1).toNat]! with | .Lit ch_0 => ((s.length : ℤ) = ((p.length : ℤ) + 1) ∧ ((s.drop 0).take ((p.length : ℤ)).toNat) = p ∧ s[(p.length : ℤ).toNat]! = ch_0) | .Match dist_0 len_1 => ((1 ≤ (dist_0.val : ℤ) ∧ (dist_0.val : ℤ) ≤ (p.length : ℤ)) ∧ 1 ≤ (len_1.val : ℤ) ∧ (s.length : ℤ) = ((p.length : ℤ) + (len_1.val : ℤ)) ∧ ((s.drop 0).take ((p.length : ℤ)).toNat) = p ∧ (∀ k : ℤ, (p.length : ℤ) ≤ k → k < (s.length : ℤ) → s[k.toNat]! = s[(k - (dist_0.val : ℤ)).toNat]!)))) → (0 ≤ ((ts.length : ℤ) - 1) ∧ ((ts.length : ℤ) - 1) < (ts.length : ℤ))) ∧
      (¬((ts.length : ℤ) = 0) → ∀ p : List U8, (decode_spec ((ts.drop 0).take (((ts.length : ℤ) - 1)).toNat) p ∧ (match ts[((ts.length : ℤ) - 1).toNat]! with | .Lit ch_0 => ((s.length : ℤ) = ((p.length : ℤ) + 1) ∧ ((s.drop 0).take ((p.length : ℤ)).toNat) = p ∧ s[(p.length : ℤ).toNat]! = ch_0) | .Match dist_0 len_1 => ((1 ≤ (dist_0.val : ℤ) ∧ (dist_0.val : ℤ) ≤ (p.length : ℤ)) ∧ 1 ≤ (len_1.val : ℤ) ∧ (s.length : ℤ) = ((p.length : ℤ) + (len_1.val : ℤ)) ∧ ((s.drop 0).take ((p.length : ℤ)).toNat) = p ∧ (∀ k : ℤ, (p.length : ℤ) ≤ k → k < (s.length : ℤ) → s[k.toNat]! = s[(k - (dist_0.val : ℤ)).toNat]!)))) → (match ts[((ts.length : ℤ) - 1).toNat]! with | .Lit ch_0 => (0 ≤ 0 ∧ 0 ≤ (p.length : ℤ) ∧ (p.length : ℤ) ≤ (s.length : ℤ)) | _ => True)) ∧
      (¬((ts.length : ℤ) = 0) → ∀ p : List U8, (decode_spec ((ts.drop 0).take (((ts.length : ℤ) - 1)).toNat) p ∧ (match ts[((ts.length : ℤ) - 1).toNat]! with | .Lit ch_0 => ((s.length : ℤ) = ((p.length : ℤ) + 1) ∧ ((s.drop 0).take ((p.length : ℤ)).toNat) = p ∧ s[(p.length : ℤ).toNat]! = ch_0) | .Match dist_0 len_1 => ((1 ≤ (dist_0.val : ℤ) ∧ (dist_0.val : ℤ) ≤ (p.length : ℤ)) ∧ 1 ≤ (len_1.val : ℤ) ∧ (s.length : ℤ) = ((p.length : ℤ) + (len_1.val : ℤ)) ∧ ((s.drop 0).take ((p.length : ℤ)).toNat) = p ∧ (∀ k : ℤ, (p.length : ℤ) ≤ k → k < (s.length : ℤ) → s[k.toNat]! = s[(k - (dist_0.val : ℤ)).toNat]!)))) → (match ts[((ts.length : ℤ) - 1).toNat]! with | .Lit ch_0 => (0 ≤ (p.length : ℤ) ∧ (p.length : ℤ) < (s.length : ℤ)) | _ => True)) ∧
      (¬((ts.length : ℤ) = 0) → ∀ p : List U8, (decode_spec ((ts.drop 0).take (((ts.length : ℤ) - 1)).toNat) p ∧ (match ts[((ts.length : ℤ) - 1).toNat]! with | .Lit ch_0 => ((s.length : ℤ) = ((p.length : ℤ) + 1) ∧ ((s.drop 0).take ((p.length : ℤ)).toNat) = p ∧ s[(p.length : ℤ).toNat]! = ch_0) | .Match dist_0 len_1 => ((1 ≤ (dist_0.val : ℤ) ∧ (dist_0.val : ℤ) ≤ (p.length : ℤ)) ∧ 1 ≤ (len_1.val : ℤ) ∧ (s.length : ℤ) = ((p.length : ℤ) + (len_1.val : ℤ)) ∧ ((s.drop 0).take ((p.length : ℤ)).toNat) = p ∧ (∀ k : ℤ, (p.length : ℤ) ≤ k → k < (s.length : ℤ) → s[k.toNat]! = s[(k - (dist_0.val : ℤ)).toNat]!)))) → (match ts[((ts.length : ℤ) - 1).toNat]! with | .Lit ch_0 => True | .Match dist_0 len_1 => (0 ≤ 0 ∧ 0 ≤ (p.length : ℤ) ∧ (p.length : ℤ) ≤ (s.length : ℤ)))) ∧
      (¬((ts.length : ℤ) = 0) → ∀ p : List U8, (decode_spec ((ts.drop 0).take (((ts.length : ℤ) - 1)).toNat) p ∧ (match ts[((ts.length : ℤ) - 1).toNat]! with | .Lit ch_0 => ((s.length : ℤ) = ((p.length : ℤ) + 1) ∧ ((s.drop 0).take ((p.length : ℤ)).toNat) = p ∧ s[(p.length : ℤ).toNat]! = ch_0) | .Match dist_0 len_1 => ((1 ≤ (dist_0.val : ℤ) ∧ (dist_0.val : ℤ) ≤ (p.length : ℤ)) ∧ 1 ≤ (len_1.val : ℤ) ∧ (s.length : ℤ) = ((p.length : ℤ) + (len_1.val : ℤ)) ∧ ((s.drop 0).take ((p.length : ℤ)).toNat) = p ∧ (∀ k : ℤ, (p.length : ℤ) ≤ k → k < (s.length : ℤ) → s[k.toNat]! = s[(k - (dist_0.val : ℤ)).toNat]!)))) → (match ts[((ts.length : ℤ) - 1).toNat]! with | .Lit ch_0 => True | .Match dist_0 len_1 => ∀ k : ℤ, (p.length : ℤ) ≤ k → k < (s.length : ℤ) → (0 ≤ k ∧ k < (s.length : ℤ)) ∧ (0 ≤ (k - (dist_0.val : ℤ)) ∧ (k - (dist_0.val : ℤ)) < (s.length : ℤ)))) := by
  intro ts s h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; omega
  · intros; omega
  all_goals
    intro hn p hp
    obtain ⟨_, hp⟩ := hp
    cases he : ts[((ts.length : ℤ) - 1).toNat]! <;> simp only [he] at hp ⊢
    all_goals first | trivial | omega | (intros; omega)

/-! ## mincost -/

theorem mincost.ens_0 :
    ∀ (n : ℤ) (s : List U8) (k : ℤ),
      mincost_spec n s k → (0 ≤ k ∧ k ≤ n) := by
  intro n
  induction n using (measure Int.toNat).wf.induction with
  | h n ih =>
    intro s k h
    rw [mincost_spec] at h
    obtain ⟨hp, hb⟩ := h
    have hpre := hp
    unfold mincost_pre at hp
    specialize hb hp
    by_cases hz : n = 0
    · have := hb.1 hz
      omega
    · obtain ⟨⟨a, ha, hka⟩, _, hc⟩ := hb.2 hz
      have hab := ih (n - 1) (by simp only [measure, InvImage, WellFoundedRelation.rel]; omega) s a ha
      have hk : k ≤ n := by omega
      refine ⟨?_, hk⟩
      rcases hc with ⟨b, hb, he⟩ | ⟨l, d, hm, hb⟩
      · have := ih (n - 1) (by simp only [measure, InvImage, WellFoundedRelation.rel]; omega) s b hb
        omega
      · obtain ⟨b, hb, he⟩ := hb hm
        have hl := (hm.2.mp rfl).1
        have := ih (n - l) (by simp only [measure, InvImage, WellFoundedRelation.rel]; omega) s b hb
        omega

theorem mincost.wf :
    ∀ (n : ℤ) (s : List U8) (k : ℤ),
      mincost_spec n s k →
      (¬(n = 0) → (mincost_pre (n - 1) s)) ∧
      (¬(n = 0) → ∀ l : ℤ, 3 ≤ l → l < (258 + 1) → ∀ d : ℤ, 1 ≤ d → d < (32768 + 1) → (ismatch_pre s ((s.length : ℤ) - n) d l)) ∧
      (¬(n = 0) → ∀ l : ℤ, 3 ≤ l → l < (258 + 1) → ∀ d : ℤ, 1 ≤ d → d < (32768 + 1) → ismatch_spec s ((s.length : ℤ) - n) d l true → (mincost_pre (n - l) s)) ∧
      (¬(n = 0) → (mincost_pre (n - 1) s)) ∧
      (¬(n = 0) → ∀ l : ℤ, ∀ d : ℤ, (ismatch_spec s ((s.length : ℤ) - n) d l true ∧ (ismatch_spec s ((s.length : ℤ) - n) d l true → (∃ v_call3 : ℤ, mincost_spec (n - l) s v_call3 ∧ k = (1 + v_call3)))) → (ismatch_pre s ((s.length : ℤ) - n) d l)) ∧
      (¬(n = 0) → ∀ l : ℤ, ∀ d : ℤ, (ismatch_spec s ((s.length : ℤ) - n) d l true ∧ (ismatch_spec s ((s.length : ℤ) - n) d l true → (∃ v_call3 : ℤ, mincost_spec (n - l) s v_call3 ∧ k = (1 + v_call3)))) → (mincost_pre (n - l) s)) := by
  intro n s k h
  rw [mincost_spec] at h
  have hp := h.1
  simp only [mincost_pre, ismatch_pre, ismatch_spec, eq_self_iff_true, true_iff] at *
  repeat' apply And.intro
  all_goals intros; omega

/-! ## besttoken -/

theorem besttoken.ens_0 :
    ∀ (n : ℤ) (s : List U8) (t : Lz77.spec.Token),
      besttoken_spec n s t → ((∃ v_call8 : U32, toklen_spec t v_call8 ∧ 1 ≤ (v_call8.val : ℤ)) ∧ (∃ v_call9 : U32, toklen_spec t v_call9 ∧ (v_call9.val : ℤ) ≤ n)) := by
  intro n s t h
  have hp := h.1
  cases t with
  | Lit ch =>
    refine ⟨⟨1#u32, (toklen_iff _ _).2 rfl, ?_⟩, ⟨1#u32, (toklen_iff _ _).2 rfl, ?_⟩⟩
    · simp
    · simpa using hp.1
  | Match d l =>
    have hm := (h.2.1.2.mp rfl).1
    refine ⟨⟨l, (toklen_iff _ _).2 rfl, ?_⟩, ⟨l, (toklen_iff _ _).2 rfl, ?_⟩⟩ <;> omega

theorem besttoken.ens_1 :
    ∀ (n : ℤ) (s : List U8) (t : Lz77.spec.Token),
      besttoken_spec n s t → (∃ v_call10 : U32, toklen_spec t v_call10 ∧ (∃ v_call11 : ℤ, mincost_spec (n - (v_call10.val : ℤ)) s v_call11 ∧ mincost_spec n s (1 + v_call11))) := by
  intro n s t h
  refine ⟨tokenLength t, (toklen_iff _ _).2 rfl, ?_⟩
  cases t with
  | Lit ch => simpa [tokenLength] using h.2.2.1
  | Match d l => exact h.2.2.1

theorem besttoken.wf :
    ∀ (n : ℤ) (s : List U8) (t : Lz77.spec.Token),
      besttoken_spec n s t →
      ((match t with | .Lit ch_0 => (0 ≤ ((s.length : ℤ) - n) ∧ ((s.length : ℤ) - n) < (s.length : ℤ)) | _ => True)) ∧
      ((match t with | .Lit ch_0 => (mincost_pre (n - 1) s) | _ => True)) ∧
      ((match t with | .Lit ch_0 => ∀ v_call0 : ℤ, mincost_spec (n - 1) s v_call0 → (mincost_pre n s) | _ => True)) ∧
      ((match t with | .Lit ch_0 => ∀ l : ℤ, 3 ≤ l → l < (258 + 1) → ∀ d : ℤ, 1 ≤ d → d < (32768 + 1) → (ismatch_pre s ((s.length : ℤ) - n) d l) | _ => True)) ∧
      ((match t with | .Lit ch_0 => ∀ l : ℤ, 3 ≤ l → l < (258 + 1) → ∀ d : ℤ, 1 ≤ d → d < (32768 + 1) → ismatch_spec s ((s.length : ℤ) - n) d l true → (mincost_pre (n - l) s) | _ => True)) ∧
      ((match t with | .Lit ch_0 => ∀ l : ℤ, 3 ≤ l → l < (258 + 1) → ∀ d : ℤ, 1 ≤ d → d < (32768 + 1) → ismatch_spec s ((s.length : ℤ) - n) d l true → ∀ v_call1 : ℤ, mincost_spec (n - l) s v_call1 → (mincost_pre n s) | _ => True)) ∧
      ((match t with | .Lit ch_0 => True | .Match dist_0 len_1 => (ismatch_pre s ((s.length : ℤ) - n) (dist_0.val : ℤ) (len_1.val : ℤ)))) ∧
      ((match t with | .Lit ch_0 => True | .Match dist_0 len_1 => (mincost_pre (n - (len_1.val : ℤ)) s))) ∧
      ((match t with | .Lit ch_0 => True | .Match dist_0 len_1 => ∀ v_call3 : ℤ, mincost_spec (n - (len_1.val : ℤ)) s v_call3 → (mincost_pre n s))) ∧
      ((match t with | .Lit ch_0 => True | .Match dist_0 len_1 => ∀ l : ℤ, ((len_1.val : ℤ) + 1) ≤ l → l < (258 + 1) → ∀ d : ℤ, 1 ≤ d → d < (32768 + 1) → (ismatch_pre s ((s.length : ℤ) - n) d l))) ∧
      ((match t with | .Lit ch_0 => True | .Match dist_0 len_1 => ∀ l : ℤ, ((len_1.val : ℤ) + 1) ≤ l → l < (258 + 1) → ∀ d : ℤ, 1 ≤ d → d < (32768 + 1) → ismatch_spec s ((s.length : ℤ) - n) d l true → (mincost_pre (n - l) s))) ∧
      ((match t with | .Lit ch_0 => True | .Match dist_0 len_1 => ∀ l : ℤ, ((len_1.val : ℤ) + 1) ≤ l → l < (258 + 1) → ∀ d : ℤ, 1 ≤ d → d < (32768 + 1) → ismatch_spec s ((s.length : ℤ) - n) d l true → ∀ v_call4 : ℤ, mincost_spec (n - l) s v_call4 → (mincost_pre n s))) ∧
      ((match t with | .Lit ch_0 => True | .Match dist_0 len_1 => ∀ d : ℤ, 1 ≤ d → d < (dist_0.val : ℤ) → (ismatch_pre s ((s.length : ℤ) - n) d (len_1.val : ℤ)))) ∧
      ((match t with | .Lit ch_0 => True | .Match dist_0 len_1 => ∀ d : ℤ, 1 ≤ d → d < (dist_0.val : ℤ) → ismatch_spec s ((s.length : ℤ) - n) d (len_1.val : ℤ) true → (mincost_pre (n - (len_1.val : ℤ)) s))) ∧
      ((match t with | .Lit ch_0 => True | .Match dist_0 len_1 => ∀ d : ℤ, 1 ≤ d → d < (dist_0.val : ℤ) → ismatch_spec s ((s.length : ℤ) - n) d (len_1.val : ℤ) true → ∀ v_call6 : ℤ, mincost_spec (n - (len_1.val : ℤ)) s v_call6 → (mincost_pre n s))) ∧
      (∀ v_call10 : U32, toklen_spec t v_call10 → (mincost_pre (n - (v_call10.val : ℤ)) s)) ∧
      (∀ v_call10 : U32, toklen_spec t v_call10 → ∀ v_call11 : ℤ, mincost_spec (n - (v_call10.val : ℤ)) s v_call11 → (mincost_pre n s)) := by
  intro n s t h
  have hp := h.1
  have hlen := besttoken.ens_0 n s t h
  simp only [toklen_iff] at hlen
  obtain ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩ := hlen
  cases t <;>
    simp only [besttoken_pre, mincost_pre, ismatch_pre, ismatch_spec,
      toklen_iff, tokenLength, eq_self_iff_true, true_iff, show (1#u32).val = 1 from rfl, Nat.cast_one] at *
  all_goals
    repeat' apply And.intro
    all_goals intros; first | trivial | (subst_vars; (try simp only [show (1#u32).val = 1 from rfl, Nat.cast_one] at *); omega)

/-! ## compress -/

def byteCount (ts : List Lz77.spec.Token) : ℤ :=
  (ts.map (fun t => (tokenLength t).val : Lz77.spec.Token → ℤ)).sum

@[simp] theorem byteCount_nil : byteCount [] = 0 := rfl

@[simp] theorem byteCount_append (a b : List Lz77.spec.Token) :
    byteCount (a ++ b) = byteCount a + byteCount b := by
  simp [byteCount]

@[simp] theorem byteCount_singleton (t : Lz77.spec.Token) :
    byteCount [t] = (tokenLength t).val := by simp [byteCount]

theorem encoded_iff (ts : List Lz77.spec.Token) (m : ℤ) :
    encoded_spec ts m ↔ m = byteCount ts := by
  induction ts using List.reverseRecOn generalizing m with
  | nil => rw [encoded_spec]; simp [encoded_pre]
  | append_singleton ts t ih =>
    rw [encoded_spec]
    simp only [encoded_pre, true_implies, true_and, List.length_append,
      List.length_singleton, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      Int.toNat_natCast, List.drop_zero]
    have hn : ¬ ((ts.length : ℤ) + 1 = 0) := by omega
    simp [hn, List.take_left, ih, toklen_iff, byteCount]

theorem mincost_le (n : ℤ) (s : List U8) (a b : ℤ)
    (ha : mincost_spec n s a) (hb : mincost_spec n s b) : a ≤ b := by
  induction n using (measure Int.toNat).wf.induction generalizing a b with
  | h n ih =>
    rw [mincost_spec] at ha hb
    have hp := ha.1
    unfold mincost_pre at hp
    have hba := ha.2 hp
    have hbb := hb.2 hp
    by_cases hz : n = 0
    · have := hba.1 hz; have := hbb.1 hz; omega
    · obtain ⟨⟨x, hx, hax⟩, hall, _⟩ := hba.2 hz
      rcases (hbb.2 hz).2.2 with ⟨y, hy, hby⟩ | ⟨l, d, hm, hh⟩
      · have hxy := ih (n - 1) (by change (n - 1).toNat < n.toNat; omega) x y hx hy
        omega
      · have hm' := (hm.2.mp rfl).1
        obtain ⟨x', hx', hax'⟩ := hall l (by omega) (by omega) d (by omega) (by omega) hm
        obtain ⟨y, hy, hby⟩ := hh hm
        have hxy := ih (n - l) (by change (n - l).toNat < n.toNat; omega) x' y hx' hy
        omega

theorem mincost_unique {n : ℤ} {s : List U8} {a b : ℤ}
    (ha : mincost_spec n s a) (hb : mincost_spec n s b) : a = b :=
  _root_.le_antisymm (mincost_le n s a b ha hb) (mincost_le n s b a hb ha)

theorem optimal_not_excluded {n r : ℤ} {s : List U8}
    (ho : ∃ x, mincost_spec r s x ∧ mincost_spec n s (1 + x))
    (he : ∃ y, mincost_spec r s y ∧ ∃ z, mincost_spec n s z ∧ 1 + y ≠ z) : False := by
  obtain ⟨x, hx, hnx⟩ := ho
  obtain ⟨y, hy, z, hz, hne⟩ := he
  have := mincost_unique hx hy
  have := mincost_unique hnx hz
  omega

theorem besttoken_unique {n : ℤ} {s : List U8} {a b : Lz77.spec.Token}
    (ha : besttoken_spec n s a) (hb : besttoken_spec n s b) : a = b := by
  cases a with
  | Lit ca =>
    cases b with
    | Lit cb => congr 1; exact ha.2.1.trans hb.2.1.symm
    | Match db lb =>
      have hm := (hb.2.1.2.mp rfl).1
      exact False.elim (optimal_not_excluded hb.2.2.1
        (ha.2.2.2 lb.val (by omega) (by omega) db.val (by omega) (by omega) hb.2.1))
  | Match da la =>
    cases b with
    | Lit cb =>
      have hm := (ha.2.1.2.mp rfl).1
      exact False.elim (optimal_not_excluded ha.2.2.1
        (hb.2.2.2 la.val (by omega) (by omega) da.val (by omega) (by omega) ha.2.1))
    | Match db lb =>
      have hma := (ha.2.1.2.mp rfl).1
      have hmb := (hb.2.1.2.mp rfl).1
      have hl : la = lb := by
        apply UScalar.eq_of_val_eq
        by_contra hn
        rcases lt_or_gt_of_ne hn with hlt | hgt
        · exact optimal_not_excluded hb.2.2.1
            (ha.2.2.2.1 lb.val (by omega) (by omega) db.val (by omega) (by omega) hb.2.1)
        · exact optimal_not_excluded ha.2.2.1
            (hb.2.2.2.1 la.val (by omega) (by omega) da.val (by omega) (by omega) ha.2.1)
      subst lb
      have hd : da = db := by
        apply UScalar.eq_of_val_eq
        by_contra hn
        rcases lt_or_gt_of_ne hn with hlt | hgt
        · exact optimal_not_excluded ha.2.2.1
            (hb.2.2.2.2 da.val (by omega) (by omega) ha.2.1)
        · exact optimal_not_excluded hb.2.2.1
            (ha.2.2.2.2 db.val (by omega) (by omega) hb.2.1)
      subst db
      rfl

@[simp] theorem byteCount_cons (t : Lz77.spec.Token) (ts : List Lz77.spec.Token) :
    byteCount (t :: ts) = (tokenLength t).val + byteCount ts := by simp [byteCount]

def Parses (s : List U8) (j : ℤ) : List Lz77.spec.Token → Prop
  | [] => j = s.length
  | t :: ts => besttoken_spec (s.length - j) s t ∧ Parses s (j + (tokenLength t).val) ts

theorem parses_of_tokens (s : List U8) (j : ℤ) (ts : List Lz77.spec.Token)
    (hend : j + byteCount ts = s.length)
    (hb : ∀ i : ℕ, i < ts.length →
      besttoken_spec (s.length - (j + byteCount (ts.take i))) s ts[i]!) :
    Parses s j ts := by
  induction ts generalizing j with
  | nil => simpa [Parses] using hend
  | cons t ts ih =>
    constructor
    · simpa using hb 0 (by simp)
    · apply ih
      · simp only [byteCount_cons] at hend
        omega
      · intro i hi
        have hh := hb (i + 1) (by simp; omega)
        simpa [List.take_succ_cons, byteCount_cons, add_assoc] using hh

theorem compress_parses {s : List U8} {ts : List Lz77.spec.Token}
    (h : compress_spec s ts) : Parses s 0 ts := by
  apply parses_of_tokens
  · have := (encoded_iff _ _).mp h.2.1
    omega
  · intro i hi
    obtain ⟨v, hv, hb⟩ := h.2.2 i (by omega) (by exact_mod_cast hi)
    have he := (encoded_iff _ _).mp hv
    simpa [he] using hb

theorem parses_unique {s : List U8} {j : ℤ} {a b : List Lz77.spec.Token}
    (ha : Parses s j a) (hb : Parses s j b) : a = b := by
  induction a generalizing j b with
  | nil =>
    cases b with
    | nil => rfl
    | cons t ts =>
      have hp := hb.1.1
      change j = s.length at ha
      unfold besttoken_pre at hp
      omega
  | cons t ts ih =>
    cases b with
    | nil =>
      have hp := ha.1.1
      change j = s.length at hb
      unfold besttoken_pre at hp
      omega
    | cons u us =>
      have ht := besttoken_unique ha.1 hb.1
      subst u
      exact congrArg (List.cons t) (ih ha.2 hb.2)

theorem parses_cost {s : List U8} {j : ℤ} {ts : List Lz77.spec.Token}
    (h : Parses s j ts) : mincost_spec (s.length - j) s ts.length := by
  induction ts generalizing j with
  | nil =>
    change j = s.length at h
    subst j
    rw [mincost_spec]
    simp [mincost_pre]
  | cons t ts ih =>
    obtain ⟨len, ht, cost, hc, hn⟩ := besttoken.ens_1 _ _ _ h.1
    have he := (toklen_iff _ _).mp ht
    subst len
    have hh := ih h.2
    have har : (s.length : ℤ) - (j + (tokenLength t).val) =
        s.length - j - (tokenLength t).val := by omega
    rw [har] at hh
    have he := mincost_unique hc hh
    subst cost
    simpa [add_comm] using hn

theorem compress.unambiguous :
    ∀ (s : List U8) (o₁ : List Lz77.spec.Token) (o₂ : List Lz77.spec.Token),
      compress_spec s o₁ → compress_spec s o₂ → o₁ = o₂ := by
  intro s a b ha hb
  exact parses_unique (compress_parses ha) (compress_parses hb)

theorem copies_pointwise {l : ℤ} {s : List U8} {j d : ℤ}
    (h : copies_spec l s j d true) (k : ℤ) (hj : j ≤ k) (hk : k < j + l) :
    s[k.toNat]! = s[(k - d).toNat]! := by
  induction l using (measure Int.toNat).wf.induction generalizing j with
  | h l ih =>
    rw [copies_spec] at h
    have hp := h.1
    have hb := (h.2 hp).mp rfl
    unfold copies_pre at hp
    have hn : l ≠ 0 := by omega
    have he := (hb.resolve_left hn) hn
    by_cases hjk : j = k
    · subst k; exact he.1
    · exact ih (l - 1) (by change (l - 1).toNat < l.toNat; omega)
        (he.2 he.1) (by omega) (by omega)

theorem get_take {α : Type} [Inhabited α] (xs : List α) (n k : ℕ) (h : k < n) :
    (xs.take n)[k]! = xs[k]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_take, h]

theorem decode_step {s : List U8} {j : ℕ} {ts : List Lz77.spec.Token}
    {t : Lz77.spec.Token} (hp : decode_spec ts (s.take j))
    (hb : besttoken_spec (s.length - j) s t) :
    decode_spec (ts ++ [t]) (s.take (j + (tokenLength t).val)) := by
  have hpre := hb.1
  unfold besttoken_pre at hpre
  have hj : j ≤ s.length := by omega
  obtain ⟨_, ⟨len, hl, hle⟩⟩ := besttoken.ens_0 _ _ _ hb
  have he := (toklen_iff _ _).mp hl
  subst len
  have hend : j + (tokenLength t).val ≤ s.length := by omega
  rw [decode_spec]
  have helem : (ts ++ [t])[ts.length]! = t := by simp
  have hn : ¬ ((ts.length : ℤ) + 1 = 0) := by omega
  simp only [decode_pre, true_and, true_implies, List.length_append,
    List.length_singleton, Nat.cast_add, Nat.cast_one, hn, false_implies,
    not_false_eq_true, add_sub_cancel_right, Int.toNat_natCast, List.drop_zero,
    List.take_left, helem]
  refine ⟨s.take j, hp, ?_⟩
  have hpl : (s.take j).length = j := List.length_take_of_le hj
  have hsl : (s.take (j + (tokenLength t).val)).length = j + (tokenLength t).val :=
    List.length_take_of_le hend
  cases t with
  | Lit ch =>
    have hc := hb.2.1
    have hend : j + 1 ≤ s.length := by simpa [tokenLength] using hend
    simp only [tokenLength, show (1#u32).val = 1 from rfl] at hsl ⊢
    simp only [hpl, hsl, Nat.cast_add, Int.toNat_natCast, List.drop_zero]
    refine ⟨by simp, ?_, ?_⟩
    · simp [List.take_take, Nat.min_eq_left (show j ≤ j + 1 by omega)]
    · have he : (s.length : ℤ) - (s.length - j) = j := by omega
      simpa [he, get_take, show j < j + 1 by omega] using hc.symm
  | Match d l =>
    have hm := hb.2.1
    have hbounds := (hm.2.mp rfl).1
    have hcopies := (hm.2.mp rfl).2
    have he : (s.length : ℤ) - (s.length - j) = j := by omega
    rw [he] at hbounds hcopies
    simp only [tokenLength, show (1#u32).val = 1 from rfl] at hsl ⊢
    simp only [hpl, hsl, Nat.cast_add, Int.toNat_natCast, List.drop_zero]
    refine ⟨⟨by omega, by omega⟩, by omega, trivial, ?_, ?_⟩
    · simp [List.take_take, Nat.min_eq_left (show j ≤ j + l.val by omega)]
    · intro k hk hke
      have hkd : 0 ≤ k - (d.val : ℤ) := by omega
      have hk0 : 0 ≤ k := by omega
      have hk1 : k.toNat < j + l.val := by omega
      have hk2 : (k - (d.val : ℤ)).toNat < j + l.val := by omega
      rw [get_take s _ _ hk1, get_take s _ _ hk2]
      exact copies_pointwise hcopies k hk (by omega)

theorem parses_decode {s : List U8} {j : ℕ} {ts : List Lz77.spec.Token}
    (h : Parses s j ts) (prets : List Lz77.spec.Token)
    (hp : decode_spec prets (s.take j)) : decode_spec (prets ++ ts) s := by
  induction ts generalizing j prets with
  | nil =>
    have he : j = s.length := by change (j : ℤ) = s.length at h; omega
    simpa [he] using hp
  | cons t ts ih =>
    have hn : Parses s (j + (tokenLength t).val : ℕ) ts := by
      simpa [Nat.cast_add] using h.2
    have hh := ih hn (prets ++ [t]) (decode_step hp h.1)
    simpa [List.append_assoc] using hh

theorem compress.ens_0 :
    ∀ (s : List U8) (ts : List Lz77.spec.Token),
      compress_spec s ts → (∃ v_out1 : List U8, decode_spec ts v_out1 ∧ v_out1 = s) := by
  intro s ts h
  refine ⟨s, ?_, rfl⟩
  have hp : decode_spec [] (s.take 0) := by rw [decode_spec]; simp [decode_pre]
  simpa using parses_decode (compress_parses h) [] hp

theorem compress.ens_1 :
    ∀ (s : List U8) (ts : List Lz77.spec.Token),
      compress_spec s ts → mincost_spec (s.length : ℤ) s (ts.length : ℤ) := by
  intro s ts h
  simpa using parses_cost (compress_parses h)

theorem compress.wf :
    ∀ (s : List U8) (ts : List Lz77.spec.Token),
      compress_spec s ts →
      (∀ i : ℤ, 0 ≤ i → i < (ts.length : ℤ) → (0 ≤ 0 ∧ 0 ≤ i ∧ i ≤ (ts.length : ℤ))) ∧
      (∀ i : ℤ, 0 ≤ i → i < (ts.length : ℤ) → ∀ v_call0 : ℤ, encoded_spec ((ts.drop 0).take (i).toNat) v_call0 → (0 ≤ i ∧ i < (ts.length : ℤ)) ∧ (besttoken_pre ((s.length : ℤ) - v_call0) s)) ∧
      ((mincost_pre (s.length : ℤ) s)) := by
  intro s ts h
  refine ⟨?_, ?_, ?_⟩
  · intros; omega
  · intro i hi ht v hv
    obtain ⟨w, hw, hb⟩ := h.2.2 i hi ht
    have he : v = w := (encoded_iff _ _).mp hv |>.trans ((encoded_iff _ _).mp hw).symm
    subst w
    exact ⟨⟨hi, ht⟩, hb.1⟩
  · unfold mincost_pre; omega

@[step] theorem toklen_model (t : Lz77.spec.Token) :
    Lz77.solution.toklen t ⦃ r => r = tokenLength t ⦄ := by
  cases t <;> unfold Lz77.solution.toklen <;> step* <;> rfl

theorem toklen.impl_correct (t : Lz77.spec.Token) (h : toklen_pre t) :
    Lz77.spec.toklen t ⦃ r => toklen_spec t r ⦄ := by
  unfold Lz77.spec.toklen
  step*
  exact (toklen_iff _ _).2 ‹_›

theorem copies_truth {l : ℤ} {s : List U8} {j d : ℤ} {b : Bool}
    (h : copies_spec l s j d b) : (b = true ↔ copies_spec l s j d true) := by
  constructor
  · intro hb; subst b; exact h
  · intro ht
    rw [copies_spec] at h ht
    exact (h.2 h.1).mpr ((ht.2 ht.1).mp rfl)

@[step] theorem match_bytes_model (s : Aeneas.Std.Slice U8) (pos dist len : Usize)
    (hp : copies_pre len.val s.val pos.val dist.val) :
    Lz77.solution.match_bytes s pos dist len
      ⦃ b => copies_spec len.val s.val pos.val dist.val b ⦄ := by
  induction len using (measure (fun x : Usize => x.val)).wf.induction generalizing pos with
  | h len ih =>
    have hpb := hp
    unfold copies_pre at hpb
    unfold Lz77.solution.match_bytes
    split
    · step*
      rw [copies_spec]
      refine ⟨hp, ?_⟩
      simp_all
    · have hl : 0 < len.val := by scalar_tac
      step*
      · have he1 : s.val[pos.val]! = i := by
          rw [getElem!_pos s.val pos.val (by omega)]; exact i_post.symm
        have he2 : s.val[(pos.val - (dist.val : ℤ)).toNat]! = i2 := by
          have he : (pos.val - (dist.val : ℤ)).toNat = i1.val := by omega
          rw [he, getElem!_pos s.val i1.val (by omega)]; exact i2_post.symm
        have hne : i ≠ i2 := by simpa using ‹(i != i2) = true›
        rw [copies_spec]
        refine ⟨hp, ?_⟩
        intro _
        rw [Int.toNat_natCast, he1, he2]
        simp [show len.val ≠ 0 by omega, hne]
      · change i4.val < len.val
        omega
      · unfold copies_pre; omega
      · have he1 : s.val[pos.val]! = i := by
          rw [getElem!_pos s.val pos.val (by omega)]; exact i_post.symm
        have he2 : s.val[(pos.val - (dist.val : ℤ)).toNat]! = i2 := by
          have he : (pos.val - (dist.val : ℤ)).toNat = i1.val := by omega
          rw [he, getElem!_pos s.val i1.val (by omega)]; exact i2_post.symm
        have heq : i = i2 := by apply UScalar.eq_of_val_eq; simpa using ‹¬(i != i2) = true›
        have he3 : (i3.val : ℤ) = pos.val + 1 := by omega
        have he4 : (i4.val : ℤ) = len.val - 1 := by omega
        have hr := copies_truth b_post
        rw [he3, he4] at hr
        rw [copies_spec]
        refine ⟨hp, ?_⟩
        intro _
        rw [Int.toNat_natCast, he1, he2]
        simpa [show len.val ≠ 0 by omega, heq] using hr

def CostTable (s : List U8) (costs : List Usize) : Prop :=
  ∀ i : ℕ, i < costs.length → mincost_spec (i + 1) s costs[i]!.val

@[step] theorem suffix_cost_model (s : List U8) (costs : Aeneas.Std.Slice Usize)
    (n : Usize) (ht : CostTable s costs.val) (hn : n.val ≤ costs.val.length) :
    Lz77.solution.suffix_cost costs n ⦃ c => mincost_spec n.val s c.val ∧ c.val ≤ n.val ⦄ := by
  unfold Lz77.solution.suffix_cost
  split
  · step*
    constructor
    · rw [mincost_spec]
      simp_all [mincost_pre]
    · simp_all
  · have hn0 : 0 < n.val := by scalar_tac
    step*
    have hh := ht i.val (by omega)
    have he : (i.val : ℤ) + 1 = n.val := by omega
    rw [he] at hh
    have hv : costs.val[i.val]! = c := by
      rw [getElem!_pos costs.val i.val (by omega)]
      exact c_post.symm
    rw [hv] at hh
    exact ⟨hh, by have := mincost.ens_0 _ _ _ hh; omega⟩

def tokenDist : Lz77.spec.Token → ℤ
  | .Lit _ => 0
  | .Match d _ => d.val

def Candidate (s : List U8) (n c : ℤ) (t : Lz77.spec.Token) : Prop :=
  (match t with
   | .Lit ch => ch = s[(s.length - n).toNat]!
   | .Match d l => ismatch_spec s (s.length - n) d.val l.val true) ∧
  ∃ k, mincost_spec (n - (tokenLength t).val) s k ∧ c = 1 + k

def rank (c : ℤ) (t : Lz77.spec.Token) : ℤ :=
  c * (258 * 32769) - (tokenLength t).val * 32769 + tokenDist t

def Visited (len dist : ℤ) (t : Lz77.spec.Token) : Prop :=
  match t with
  | .Lit _ => True
  | .Match d l => (l.val : ℤ) < len ∨ (l.val : ℤ) = len ∧ (d.val : ℤ) < dist

def SearchInv (s : List U8) (n len dist c : ℤ) (t : Lz77.spec.Token) : Prop :=
  Candidate s n c t ∧ Visited len dist t ∧
  ∀ c2 t2, Candidate s n c2 t2 → Visited len dist t2 → rank c t ≤ rank c2 t2

theorem candidate_bounds {s : List U8} {n c : ℤ} {t : Lz77.spec.Token}
    (hn : 1 ≤ n ∧ n ≤ s.length) (h : Candidate s n c t) :
    1 ≤ (tokenLength t).val ∧ (tokenLength t).val ≤ (258 : ℤ) ∧
    (tokenLength t).val ≤ n ∧ 0 ≤ tokenDist t ∧ tokenDist t ≤ 32768 ∧ 1 ≤ c ∧ c ≤ n := by
  obtain ⟨hv, k, hk, he⟩ := h
  have hkc := mincost.ens_0 _ _ _ hk
  cases t with
  | Lit ch => simp only [tokenLength, tokenDist, show (1#u32).val = 1 from rfl] at *; omega
  | Match d l =>
    have hm := (hv.2.mp rfl).1
    simp only [tokenLength, tokenDist] at *
    omega

theorem rank_cost_le {s : List U8} {n c c2 : ℤ} {t t2 : Lz77.spec.Token}
    (hn : 1 ≤ n ∧ n ≤ s.length) (h : Candidate s n c t) (h2 : Candidate s n c2 t2)
    (hr : rank c t ≤ rank c2 t2) : c ≤ c2 := by
  have hb := candidate_bounds hn h
  have hb2 := candidate_bounds hn h2
  unfold rank at hr
  omega

theorem rank_tie {s : List U8} {n c : ℤ} {t t2 : Lz77.spec.Token}
    (hn : 1 ≤ n ∧ n ≤ s.length) (h : Candidate s n c t) (h2 : Candidate s n c t2)
    (hr : rank c t ≤ rank c t2) :
    (tokenLength t2).val ≤ (tokenLength t).val ∧
    ((tokenLength t).val = (tokenLength t2).val → tokenDist t ≤ tokenDist t2) := by
  have hb := candidate_bounds hn h
  have hb2 := candidate_bounds hn h2
  unfold rank at hr
  omega


theorem candidate_cost_unique {s : List U8} {n c c2 : ℤ} {t : Lz77.spec.Token}
    (h : Candidate s n c t) (h2 : Candidate s n c2 t) : c = c2 := by
  obtain ⟨_, k, hk, he⟩ := h
  obtain ⟨_, k2, hk2, he2⟩ := h2
  have := mincost_unique hk hk2
  omega

theorem visited_mono {len dist : ℤ} {t : Lz77.spec.Token}
    (h : Visited len dist t) : Visited len (dist + 1) t := by
  cases t <;> simp only [Visited] at * <;> first | trivial | omega

theorem visited_next {len dist : ℤ} {d l : U32} {t : Lz77.spec.Token}
    (hd : (d.val : ℤ) = dist) (hl : (l.val : ℤ) = len)
    (h : Visited len (dist + 1) t) : Visited len dist t ∨ t = .Match d l := by
  by_cases ho : Visited len dist t
  · exact Or.inl ho
  · right
    cases t with
    | Lit ch => exact False.elim (ho trivial)
    | Match d2 l2 =>
      simp only [Visited] at h ho
      have he1 : d2 = d := by apply UScalar.eq_of_val_eq; omega
      have he2 : l2 = l := by apply UScalar.eq_of_val_eq; omega
      subst d2; subst l2; rfl

theorem search_keep {s : List U8} {n len dist c c2 : ℤ} {t : Lz77.spec.Token} {d l : U32}
    (hi : SearchInv s n len dist c t)
    (hd : (d.val : ℤ) = dist) (hl : (l.val : ℤ) = len)
    (hc : Candidate s n c2 (.Match d l)) (hr : rank c t ≤ rank c2 (.Match d l)) :
    SearchInv s n len (dist + 1) c t := by
  refine ⟨hi.1, visited_mono hi.2.1, ?_⟩
  intro cx tx hx hv
  rcases visited_next hd hl hv with ho | he
  · exact hi.2.2 cx tx hx ho
  · subst tx
    have he := candidate_cost_unique hc hx
    subst cx
    exact hr

theorem search_replace {s : List U8} {n len dist c c2 : ℤ} {t : Lz77.spec.Token} {d l : U32}
    (hi : SearchInv s n len dist c t)
    (hd : (d.val : ℤ) = dist) (hl : (l.val : ℤ) = len)
    (hc : Candidate s n c2 (.Match d l)) (hr : rank c2 (.Match d l) ≤ rank c t) :
    SearchInv s n len (dist + 1) c2 (.Match d l) := by
  refine ⟨hc, ?_, ?_⟩
  · simp only [Visited]; omega
  · intro cx tx hx hv
    rcases visited_next hd hl hv with ho | he
    · exact _root_.le_trans hr (hi.2.2 cx tx hx ho)
    · subst tx
      have he := candidate_cost_unique hc hx
      subst cx
      exact _root_.le_refl _

theorem search_skip {s : List U8} {n len dist c : ℤ} {t : Lz77.spec.Token} {d l : U32}
    (hi : SearchInv s n len dist c t)
    (hd : (d.val : ℤ) = dist) (hl : (l.val : ℤ) = len)
    (hc : ∀ cx, ¬Candidate s n cx (.Match d l)) :
    SearchInv s n len (dist + 1) c t := by
  refine ⟨hi.1, visited_mono hi.2.1, ?_⟩
  intro cx tx hx hv
  rcases visited_next hd hl hv with ho | he
  · exact hi.2.2 cx tx hx ho
  · subst tx; exact False.elim (hc cx hx)


theorem search_row {s : List U8} {n len dist c : ℤ} {t : Lz77.spec.Token}
    (hi : SearchInv s n len dist c t)
    (hd : 32768 < dist ∨ (s.length : ℤ) - n < dist) :
    SearchInv s n (len + 1) 1 c t := by
  refine ⟨hi.1, ?_, ?_⟩
  · have hv := hi.2.1
    cases t <;> simp only [Visited] at * <;> first | trivial | omega
  · intro cx tx hx hv
    apply hi.2.2 cx tx hx
    cases tx with
    | Lit ch => trivial
    | Match d l =>
      have hb := (hx.1.2.mp rfl).1
      simp only [Visited] at hv ⊢
      omega

def InnerInv (s : List U8) (n len : ℤ)
    (x : Usize × Lz77.spec.Token × Usize × Usize) : Prop :=
  1 ≤ x.2.2.2.val ∧ x.2.2.2.val ≤ 32769 ∧
  x.2.2.1.val = (tokenLength x.2.1).val ∧
  SearchInv s n len x.2.2.2.val x.1.val x.2.1

def InnerPost (s : List U8) (n len : ℤ)
    (x : Usize × Lz77.spec.Token × Usize) : Prop :=
  x.2.2.val = (tokenLength x.2.1).val ∧ SearchInv s n (len + 1) 1 x.1.val x.2.1

theorem rank_replace {s : List U8} {n c c2 : ℤ} {t : Lz77.spec.Token} {d l : U32}
    (hn : 1 ≤ n ∧ n ≤ s.length) (hc : Candidate s n c t)
    (hc2 : Candidate s n c2 (.Match d l))
    (h : c2 < c ∨ c2 = c ∧ (tokenLength t).val < l.val) :
    rank c2 (.Match d l) ≤ rank c t := by
  have hb := candidate_bounds hn hc
  have hb2 := candidate_bounds hn hc2
  simp only [rank, tokenLength, tokenDist] at *
  omega

theorem rank_keep {s : List U8} {n c c2 : ℤ} {t : Lz77.spec.Token} {d l : U32}
    (hn : 1 ≤ n ∧ n ≤ s.length) (hc : Candidate s n c t)
    (hc2 : Candidate s n c2 (.Match d l))
    (hv : Visited l.val d.val t)
    (h : c < c2 ∨ c = c2 ∧ l.val ≤ (tokenLength t).val) :
    rank c t ≤ rank c2 (.Match d l) := by
  have hb := candidate_bounds hn hc
  have hb2 := candidate_bounds hn hc2
  cases t <;> simp only [rank, tokenLength, tokenDist, Visited,
    show (1#u32).val = 1 from rfl] at * <;> omega

theorem inner_body_model (s : Aeneas.Std.Slice U8) (pos : Usize)
    (costs : Aeneas.Std.Slice Usize) (remaining len cost : Usize)
    (best : Lz77.spec.Token) (bestLen dist : Usize)
    (hp : pos.val < s.val.length) (hr : remaining.val = s.val.length - pos.val)
    (ht : CostTable s.val costs.val) (hcl : remaining.val - 1 ≤ costs.val.length)
    (hl : 3 ≤ len.val ∧ len.val ≤ 258 ∧ len.val ≤ remaining.val)
    (hi : InnerInv s.val remaining.val len.val (cost, best, bestLen, dist)) :
    Lz77.solution.best_at_loop0_loop0.body s pos costs remaining len cost best bestLen dist
      ⦃ r => match r with
        | .done x => InnerPost s.val remaining.val len.val x
        | .cont x => InnerInv s.val remaining.val len.val x ∧
            32769 - x.2.2.2.val < 32769 - dist.val ⦄ := by
  obtain ⟨hd0, hd1, hbl, hinv⟩ := hi
  have hn : 1 ≤ (remaining.val : ℤ) ∧ (remaining.val : ℤ) ≤ s.val.length := by omega
  have hb := candidate_bounds hn hinv.1
  simp only [Prod.fst, Prod.snd] at *
  let dd := UScalar.cast .U32 dist
  let ll := UScalar.cast .U32 len
  have hdv : dd.val = dist.val := by
    simp only [dd, UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  have hlv : ll.val = len.val := by
    simp only [ll, UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  have hpos : (s.val.length : ℤ) - remaining.val = pos.val := by omega
  unfold Lz77.solution.best_at_loop0_loop0.body
  step*
  · unfold copies_pre
    scalar_tac
  · have hdBound : dist.val ≤ 32768 := by scalar_tac
    split
    · rename_i hbtrue
      subst b
      step as ⟨rest, hrest, hrestBound⟩
      step as ⟨tailCost, htail, htailBound⟩
      step as ⟨newCost, hnew⟩
      have hc : Candidate s.val remaining.val newCost.val (.Match dd ll) := by
        refine ⟨?_, tailCost.val, ?_, by omega⟩
        · change ismatch_spec _ _ _ _ true
          unfold ismatch_spec ismatch_pre
          rw [hdv, hlv, hpos]
          simp only [eq_self_iff_true, true_iff]
          exact ⟨⟨by omega, by omega⟩, by scalar_tac, b_post⟩
        · have he : (remaining.val : ℤ) - ll.val = rest.val := by omega
          simpa only [tokenLength, he] using htail
      have hupdate : newCost < cost ∨ newCost = cost ∧ len > bestLen →
          SearchInv s.val remaining.val len.val (dist.val + 1) newCost.val (.Match dd ll) := by
        intro h
        apply search_replace hinv (by omega) (by omega) hc
        apply rank_replace hn hinv.1 hc
        scalar_tac
      have hkeep : ¬newCost < cost → (newCost ≠ cost ∨ ¬len > bestLen) →
          SearchInv s.val remaining.val len.val (dist.val + 1) cost.val best := by
        intro h1 h2
        apply search_keep hinv (by omega) (by omega) hc
        apply rank_keep hn hinv.1 hc
        · simpa only [hdv, hlv] using hinv.2.1
        · scalar_tac
      split
      · step as ⟨newDist, hnewDist⟩
        step as ⟨newLen, hnewLen⟩
        step as ⟨dist1, hdist1⟩
        step*
        have he : (dist1.val : ℤ) = dist.val + 1 := by omega
        have hd : newDist = dd := hnewDist
        have hll : newLen = ll := hnewLen
        subst newDist; subst newLen
        simp only [InnerInv, Prod.fst, Prod.snd]
        refine ⟨⟨by omega, by omega, hlv.symm, ?_⟩, by omega⟩
        rw [he]
        exact hupdate (Or.inl ‹newCost < cost›)
      · split
        · split
          · step as ⟨newDist, hnewDist⟩
            step as ⟨newLen, hnewLen⟩
            step as ⟨dist1, hdist1⟩
            step*
            have he : (dist1.val : ℤ) = dist.val + 1 := by omega
            have hd : newDist = dd := hnewDist
            have hll : newLen = ll := hnewLen
            subst newDist; subst newLen
            simp only [InnerInv, Prod.fst, Prod.snd]
            refine ⟨⟨by omega, by omega, hlv.symm, ?_⟩, by omega⟩
            rw [he]
            exact hupdate (Or.inr ⟨‹newCost = cost›, ‹len > bestLen›⟩)
          · step*
            have he : (dist1.val : ℤ) = dist.val + 1 := by omega
            simp only [InnerInv, Prod.fst, Prod.snd]
            refine ⟨⟨by omega, by omega, hbl, ?_⟩, by omega⟩
            rw [he]
            exact hkeep ‹¬newCost < cost› (Or.inr ‹¬len > bestLen›)
        · step*
          have he : (dist1.val : ℤ) = dist.val + 1 := by omega
          simp only [InnerInv, Prod.fst, Prod.snd]
          refine ⟨⟨by omega, by omega, hbl, ?_⟩, by omega⟩
          rw [he]
          exact hkeep ‹¬newCost < cost› (Or.inl ‹newCost ≠ cost›)
    · rename_i hbfalse
      step*
      have he : (dist1.val : ℤ) = dist.val + 1 := by omega
      simp only [InnerInv, Prod.fst, Prod.snd]
      refine ⟨⟨by omega, by omega, hbl, ?_⟩, by omega⟩
      rw [he]
      apply search_skip hinv (by omega : (dd.val : ℤ) = dist.val) (by omega : (ll.val : ℤ) = len.val)
      intro cx hc
      have hcopy := (hc.1.2.mp rfl).2
      simp only [hdv, hlv, hpos] at hcopy
      exact hbfalse ((copies_truth b_post).mpr hcopy)

  · refine ⟨hbl, search_row hinv (Or.inr ?_)⟩
    scalar_tac
  · refine ⟨hbl, search_row hinv (Or.inl ?_)⟩
    scalar_tac

@[step] theorem inner_model (s : Aeneas.Std.Slice U8) (pos : Usize)
    (costs : Aeneas.Std.Slice Usize) (remaining cost : Usize)
    (best : Lz77.spec.Token) (bestLen len dist : Usize)
    (hp : pos.val < s.val.length) (hr : remaining.val = s.val.length - pos.val)
    (ht : CostTable s.val costs.val) (hcl : remaining.val - 1 ≤ costs.val.length)
    (hl : 3 ≤ len.val ∧ len.val ≤ 258 ∧ len.val ≤ remaining.val)
    (hi : InnerInv s.val remaining.val len.val (cost, best, bestLen, dist)) :
    Lz77.solution.best_at_loop0_loop0 s pos costs remaining cost best bestLen len dist
      ⦃ x => InnerPost s.val remaining.val len.val x ⦄ := by
  unfold Lz77.solution.best_at_loop0_loop0
  apply loop.spec_decr_nat (fun x => 32769 - x.2.2.2.val)
    (InnerInv s.val remaining.val len.val)
  · rintro ⟨c, t, bl, d⟩ h
    exact Aeneas.Std.WP.spec_mono (inner_body_model s pos costs remaining len c t bl d hp hr ht hcl hl h)
      (by intro r h; cases r <;> exact h)
  · exact hi

def Optimal (s : List U8) (n c : ℤ) (t : Lz77.spec.Token) : Prop :=
  Candidate s n c t ∧ ∀ c2 t2, Candidate s n c2 t2 → rank c t ≤ rank c2 t2

theorem search_finish {s : List U8} {n len c : ℤ} {t : Lz77.spec.Token}
    (hi : SearchInv s n len 1 c t) (he : 258 < len ∨ n < len) : Optimal s n c t := by
  refine ⟨hi.1, ?_⟩
  intro cx tx hx
  apply hi.2.2 cx tx hx
  cases tx with
  | Lit ch => trivial
  | Match d l =>
    have hb := (hx.1.2.mp rfl).1
    simp only [Visited]
    omega

def OuterInv (s : List U8) (n : ℤ)
    (x : Usize × Lz77.spec.Token × Usize × Usize) : Prop :=
  3 ≤ x.2.2.2.val ∧ x.2.2.2.val ≤ 259 ∧
  x.2.2.1.val = (tokenLength x.2.1).val ∧
  SearchInv s n x.2.2.2.val 1 x.1.val x.2.1

theorem outer_body_model (s : Aeneas.Std.Slice U8) (pos : Usize)
    (costs : Aeneas.Std.Slice Usize) (remaining cost : Usize)
    (best : Lz77.spec.Token) (bestLen len : Usize)
    (hp : pos.val < s.val.length) (hr : remaining.val = s.val.length - pos.val)
    (ht : CostTable s.val costs.val) (hcl : remaining.val - 1 ≤ costs.val.length)
    (hi : OuterInv s.val remaining.val (cost, best, bestLen, len)) :
    Lz77.solution.best_at_loop0.body s pos costs remaining cost best bestLen len
      ⦃ r => match r with
        | .done x => Optimal s.val remaining.val x.1.val x.2
        | .cont x => OuterInv s.val remaining.val x ∧ 259 - x.2.2.2.val < 259 - len.val ⦄ := by
  obtain ⟨hl0, hl1, hbl, hinv⟩ := hi
  simp only [Prod.fst, Prod.snd] at *
  unfold Lz77.solution.best_at_loop0.body
  step*
  · exact ⟨by simp, by simp, hbl, by simpa using hinv⟩
  · simp only [OuterInv, Prod.fst, Prod.snd]
    refine ⟨⟨by omega, by scalar_tac, best_cost1_post.1, ?_⟩, by scalar_tac⟩
    have he : (len1.val : ℤ) = len.val + 1 := by omega
    rw [he]
    exact best_cost1_post.2
  · exact search_finish hinv (Or.inr (by scalar_tac))
  · exact search_finish hinv (Or.inl (by scalar_tac))

@[step] theorem outer_model (s : Aeneas.Std.Slice U8) (pos : Usize)
    (costs : Aeneas.Std.Slice Usize) (remaining cost : Usize)
    (best : Lz77.spec.Token) (bestLen len : Usize)
    (hp : pos.val < s.val.length) (hr : remaining.val = s.val.length - pos.val)
    (ht : CostTable s.val costs.val) (hcl : remaining.val - 1 ≤ costs.val.length)
    (hi : OuterInv s.val remaining.val (cost, best, bestLen, len)) :
    Lz77.solution.best_at_loop0 s pos costs remaining cost best bestLen len
      ⦃ x => Optimal s.val remaining.val x.1.val x.2 ⦄ := by
  unfold Lz77.solution.best_at_loop0
  apply loop.spec_decr_nat (fun x => 259 - x.2.2.2.val) (OuterInv s.val remaining.val)
  · rintro ⟨c, t, bl, l⟩ h
    exact Aeneas.Std.WP.spec_mono (outer_body_model s pos costs remaining c t bl l hp hr ht hcl h)
      (by intro r h; cases r <;> exact h)
  · exact hi

theorem search_initial {s : List U8} {n c : ℤ} {ch : U8}
    (hc : Candidate s n c (.Lit ch)) : SearchInv s n 3 1 c (.Lit ch) := by
  refine ⟨hc, trivial, ?_⟩
  intro cx tx hx hv
  cases tx with
  | Lit ch2 =>
    have he : ch2 = ch := hx.1.trans hc.1.symm
    subst ch2
    have he := candidate_cost_unique hc hx
    subst cx
    exact _root_.le_refl _
  | Match d l =>
    have hb := (hx.1.2.mp rfl).1
    simp only [Visited] at hv
    omega

theorem best_at_optimal (s : Aeneas.Std.Slice U8) (pos : Usize)
    (costs : Aeneas.Std.Slice Usize) (hp : pos.val < s.val.length)
    (ht : CostTable s.val costs.val) (hc : s.val.length - pos.val - 1 ≤ costs.val.length) :
    Lz77.solution.best_at s pos costs
      ⦃ x => Optimal s.val (s.val.length - pos.val) x.1.val x.2 ⦄ := by
  unfold Lz77.solution.best_at
  step*
  simp only [OuterInv, Prod.fst, Prod.snd]
  refine ⟨by simp, by simp, by simp [tokenLength], ?_⟩
  apply search_initial
  refine ⟨?_, i2.val, ?_, by omega⟩
  · have he : (s.val.length : ℤ) - remaining.val = pos.val := by
      simp only [Slice.len_val, Slice.length] at remaining_post
      omega
    rw [he, Int.toNat_natCast, getElem!_pos s.val pos.val hp]
    exact i3_post
  · have he : (remaining.val : ℤ) - 1 = i1.val := by omega
    simpa only [tokenLength, show (1#u32).val = 1 from rfl, Nat.cast_one, he] using i2_post

theorem table_exists {s : List U8} {costs : List Usize} (ht : CostTable s costs)
    (r : ℤ) (hr : 0 ≤ r) (hb : r ≤ costs.length) : ∃ k, mincost_spec r s k := by
  by_cases hz : r = 0
  · subst r
    refine ⟨0, ?_⟩
    rw [mincost_spec]
    simp [mincost_pre]
  · have hi : r.toNat - 1 < costs.length := by omega
    have he : ((r.toNat - 1 : ℕ) : ℤ) + 1 = r := by omega
    exact ⟨_, by simpa only [he] using ht (r.toNat - 1) hi⟩

theorem match_candidate {s : List U8} {n d l k : ℤ}
    (hm : ismatch_spec s (s.length - n) d l true)
    (hk : mincost_spec (n - l) s k) :
    ∃ t, Candidate s n (1 + k) t ∧ (tokenLength t).val = l ∧ tokenDist t = d := by
  have hb := (hm.2.mp rfl).1
  let dd := U32.ofNatCore d.toNat (by scalar_tac)
  let ll := U32.ofNatCore l.toNat (by scalar_tac)
  have hd : (dd.val : ℤ) = d := by simp only [dd, U32.ofNatCore_val_eq]; omega
  have hl : (ll.val : ℤ) = l := by simp only [ll, U32.ofNatCore_val_eq]; omega
  refine ⟨.Match dd ll, ⟨?_, k, ?_, rfl⟩, hl, hd⟩
  · simpa only [hd, hl] using hm
  · simpa only [tokenLength, hl] using hk

theorem optimal_spec {s : List U8} {n c : ℤ} {t : Lz77.spec.Token}
    (hn : 1 ≤ n ∧ n ≤ s.length) (ho : Optimal s n c t)
    (children : ∀ r : ℤ, 0 ≤ r → r < n → ∃ k, mincost_spec r s k) :
    mincost_spec n s c ∧ besttoken_spec n s t := by
  have hmin : mincost_spec n s c := by
    rw [mincost_spec]
    refine ⟨⟨by omega, hn.2⟩, ?_⟩
    intro _
    refine ⟨by intro; omega, ?_⟩
    intro _
    obtain ⟨k, hk⟩ := children (n - 1) (by omega) (by omega)
    have hcan : Candidate s n (1 + k) (.Lit s[(s.length - n).toNat]!) := by
      refine ⟨rfl, k, ?_, rfl⟩
      simpa [tokenLength] using hk
    refine ⟨⟨k, hk, rank_cost_le hn ho.1 hcan (ho.2 _ _ hcan)⟩, ?_, ?_⟩
    · intro l hl hlm d hd hdm hm
      have hb := (hm.2.mp rfl).1
      obtain ⟨k2, hk2⟩ := children (n - l) (by omega) (by omega)
      obtain ⟨t2, ht2, _, _⟩ := match_candidate hm hk2
      exact ⟨k2, hk2, rank_cost_le hn ho.1 ht2 (ho.2 _ _ ht2)⟩
    · have hh := ho.1.2
      cases t with
      | Lit ch => left; simpa [tokenLength] using hh
      | Match d l =>
        right
        exact ⟨l.val, d.val, ho.1.1, fun _ => hh⟩
  have reject : ∀ l d : ℤ, ismatch_spec s (s.length - n) d l true →
      ((tokenLength t).val < l ∨ (tokenLength t).val = l ∧ d < tokenDist t) →
      ∃ k, mincost_spec (n - l) s k ∧ ∃ cost, mincost_spec n s cost ∧ 1 + k ≠ cost := by
    intro l d hm better
    have hb := (hm.2.mp rfl).1
    obtain ⟨k, hk⟩ := children (n - l) (by omega) (by omega)
    obtain ⟨t2, ht2, hl, hd⟩ := match_candidate hm hk
    refine ⟨k, hk, c, hmin, ?_⟩
    intro he
    rw [he] at ht2
    have hr := rank_tie hn ho.1 ht2 (ho.2 _ _ ht2)
    omega
  refine ⟨hmin, hn, ?_⟩
  cases t with
  | Lit ch =>
    refine ⟨ho.1.1, ?_, ?_⟩
    · obtain ⟨k, hk, he⟩ := ho.1.2
      refine ⟨k, ?_, ?_⟩
      · simpa [tokenLength] using hk
      · simpa only [he] using hmin
    · intro l hl hlm d hd hdm hm
      apply reject l d hm
      left; simp [tokenLength]; omega
  | Match d l =>
    refine ⟨ho.1.1, ?_, ?_, ?_⟩
    · obtain ⟨k, hk, he⟩ := ho.1.2
      exact ⟨k, hk, by simpa only [he] using hmin⟩
    · intro l2 hl hlm d2 hd hdm hm
      apply reject l2 d2 hm
      left; simp only [tokenLength]; omega
    · intro d2 hd hdm hm
      apply reject l.val d2 hm
      right; exact ⟨rfl, hdm⟩


@[step] theorem best_at_model (s : Aeneas.Std.Slice U8) (pos : Usize)
    (costs : Aeneas.Std.Slice Usize) (hp : pos.val < s.val.length)
    (ht : CostTable s.val costs.val) (hc : s.val.length - pos.val - 1 ≤ costs.val.length) :
    Lz77.solution.best_at s pos costs
      ⦃ x => mincost_spec (s.val.length - pos.val) s.val x.1.val ∧
        besttoken_spec (s.val.length - pos.val) s.val x.2 ⦄ := by
  apply Aeneas.Std.WP.spec_mono (best_at_optimal s pos costs hp ht hc)
  intro x hx
  apply optimal_spec (by omega) hx
  intro r hr hrn
  exact table_exists ht r hr (by omega)

def ChoiceTable (s : List U8) (choices : List Lz77.spec.Token) : Prop :=
  ∀ i : ℕ, i < choices.length → besttoken_spec (i + 1) s choices[i]!

theorem cost_table_push {s : List U8} {costs : List Usize} {c : Usize}
    (h : CostTable s costs) (hc : mincost_spec (costs.length + 1) s c.val) :
    CostTable s (costs ++ [c]) := by
  intro i hi
  by_cases hl : i < costs.length
  · rw [List.getElem!_append_left costs [c] i hl]
    exact h i hl
  · have he : i = costs.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa using hc

theorem choice_table_push {s : List U8} {choices : List Lz77.spec.Token} {t : Lz77.spec.Token}
    (h : ChoiceTable s choices) (hc : besttoken_spec (choices.length + 1) s t) :
    ChoiceTable s (choices ++ [t]) := by
  intro i hi
  by_cases hl : i < choices.length
  · rw [List.getElem!_append_left choices [t] i hl]
    exact h i hl
  · have he : i = choices.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa using hc

def BuildInv (s : List U8)
    (x : alloc.vec.Vec Usize × alloc.vec.Vec Lz77.spec.Token × Usize) : Prop :=
  x.2.2.val ≤ s.length ∧ x.1.val.length = x.2.2.val ∧ x.2.1.val.length = x.2.2.val ∧
  CostTable s x.1.val ∧ ChoiceTable s x.2.1.val

def BuildPost (s : List U8) (choices : alloc.vec.Vec Lz77.spec.Token) : Prop :=
  choices.val.length = s.length ∧ ChoiceTable s choices.val

theorem build_body_model (s : Aeneas.Std.Slice U8) (costs : alloc.vec.Vec Usize)
    (choices : alloc.vec.Vec Lz77.spec.Token) (n : Usize)
    (hi : BuildInv s.val (costs, choices, n)) :
    Lz77.solution.compress_loop0.body s costs choices n
      ⦃ r => match r with
        | .done x => BuildPost s.val x
        | .cont x => BuildInv s.val x ∧ s.val.length - x.2.2.val < s.val.length - n.val ⦄ := by
  obtain ⟨hn, hcost, hchoices, hct, hbt⟩ := hi
  simp only [Prod.fst, Prod.snd] at *
  unfold Lz77.solution.compress_loop0.body
  step*
  · simpa [alloc.vec.Vec.deref] using hct
  · simp only [alloc.vec.Vec.deref, Slice.from_val]
    simp only [Slice.len_val, Slice.length] at i2_post i2_post1
    omega
  · simp only [BuildInv, Prod.fst, Prod.snd, costs1_post, choices1_post,
      List.length_append, List.length_singleton]
    simp only [Slice.len_val, Slice.length] at i2_post i2_post1
    refine ⟨⟨by omega, by omega, by omega, ?_, ?_⟩, by scalar_tac⟩
    · apply cost_table_push hct
      have he : (s.val.length : ℤ) - i2.val = costs.val.length + 1 := by omega
      simpa only [he] using cost_post
    · apply choice_table_push hbt
      have he : (s.val.length : ℤ) - i2.val = choices.val.length + 1 := by omega
      simpa only [he] using cost_post1
  · exact ⟨by scalar_tac, hbt⟩

@[step] theorem build_model (s : Aeneas.Std.Slice U8) (costs : alloc.vec.Vec Usize)
    (choices : alloc.vec.Vec Lz77.spec.Token) (n : Usize)
    (hi : BuildInv s.val (costs, choices, n)) :
    Lz77.solution.compress_loop0 s costs choices n ⦃ x => BuildPost s.val x ⦄ := by
  unfold Lz77.solution.compress_loop0
  apply loop.spec_decr_nat (fun x => s.val.length - x.2.2.val) (BuildInv s.val)
  · rintro ⟨c, t, n⟩ h
    exact Aeneas.Std.WP.spec_mono (build_body_model s c t n h)
      (by intro r h; cases r <;> exact h)
  · exact hi


def PrefixValid (s : List U8) (ts : List Lz77.spec.Token) : Prop :=
  ∀ i : ℕ, i < ts.length → besttoken_spec (s.length - byteCount (ts.take i)) s ts[i]!

theorem prefix_push {s : List U8} {ts : List Lz77.spec.Token} {t : Lz77.spec.Token}
    (h : PrefixValid s ts) (ht : besttoken_spec (s.length - byteCount ts) s t) :
    PrefixValid s (ts ++ [t]) := by
  intro i hi
  by_cases hl : i < ts.length
  · have htake : (ts ++ [t]).take i = ts.take i := by
      simp [List.take_append, Nat.sub_eq_zero_of_le (Nat.le_of_lt hl)]
    rw [htake, List.getElem!_append_left ts [t] i hl]
    exact h i hl
  · have he : i = ts.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa using ht

def EmitInv (s : List U8) (x : alloc.vec.Vec Lz77.spec.Token × Usize) : Prop :=
  x.2.val ≤ s.length ∧ x.1.val.length ≤ x.2.val ∧
  byteCount x.1.val = x.2.val ∧ PrefixValid s x.1.val

theorem emit_body_model (s : Aeneas.Std.Slice U8) (choices output : alloc.vec.Vec Lz77.spec.Token)
    (pos : Usize) (hc : BuildPost s.val choices) (hi : EmitInv s.val (output, pos)) :
    Lz77.solution.compress_loop1.body s choices output pos
      ⦃ r => match r with
        | .done x => compress_spec s.val x.val
        | .cont x => EmitInv s.val x ∧ s.val.length - x.2.val < s.val.length - pos.val ⦄ := by
  obtain ⟨hp, hol, hbytes, hvalid⟩ := hi
  obtain ⟨hcl, hchoices⟩ := hc
  simp only [Prod.fst, Prod.snd] at *
  unfold Lz77.solution.compress_loop1.body
  dsimp only
  split
  · step as ⟨remaining, hremaining, hremainingBound⟩
    step as ⟨idx, hidx, hidxBound⟩
    step as ⟨token, htoken⟩
    have hbt := hchoices idx.val (by scalar_tac)
    have he : (idx.val : ℤ) + 1 = s.val.length - pos.val := by
      simp only [Slice.len_val, Slice.length] at hremaining hremainingBound
      omega
    rw [he] at hbt
    have htok : choices.val[idx.val]! = token := by
      rw [getElem!_pos choices.val idx.val (by scalar_tac)]
      exact htoken.symm
    rw [htok] at hbt
    have hlen := besttoken.ens_0 _ _ _ hbt
    simp only [toklen_iff] at hlen
    obtain ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩ := hlen
    step*
    have hcast : i5.val = (tokenLength token).val := by scalar_tac
    simp only [EmitInv, Prod.fst, Prod.snd, output1_post, List.length_append,
      List.length_singleton, byteCount_append, byteCount_singleton]
    refine ⟨⟨by omega, by omega, by omega, ?_⟩, by scalar_tac⟩
    apply prefix_push hvalid
    simpa only [hbytes] using hbt
  · have he : pos.val = s.val.length := by scalar_tac
    refine ⟨trivial, (encoded_iff _ _).2 ?_, ?_⟩
    · omega
    · intro i hi hl
      refine ⟨byteCount (output.val.take i.toNat), ?_, ?_⟩
      · simp only [List.drop_zero]
        exact (encoded_iff _ _).2 rfl
      · exact hvalid i.toNat (by omega)


@[step] theorem emit_model (s : Aeneas.Std.Slice U8) (choices output : alloc.vec.Vec Lz77.spec.Token)
    (pos : Usize) (hc : BuildPost s.val choices) (hi : EmitInv s.val (output, pos)) :
    Lz77.solution.compress_loop1 s choices output pos ⦃ x => compress_spec s.val x.val ⦄ := by
  unfold Lz77.solution.compress_loop1
  apply loop.spec_decr_nat (fun x => s.val.length - x.2.val) (EmitInv s.val)
  · rintro ⟨o, p⟩ h
    exact Aeneas.Std.WP.spec_mono (emit_body_model s choices o p hc h)
      (by intro r h; cases r <;> exact h)
  · exact hi

theorem compress.impl_correct (s : Aeneas.Std.Slice U8) (h : compress_pre s.val) :
    Lz77.spec.compress s ⦃ ts => compress_spec s.val ts.val ⦄ := by
  unfold Lz77.spec.compress Lz77.solution.compress
  step*
  · simp [BuildInv, CostTable, ChoiceTable]
  · simp [EmitInv, PrefixValid]


end Lz77.Proofs
