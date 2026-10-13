/-  Proofs.lean — the implementer's file. Written once by `cargo djinn
    translate`, never overwritten. Replace every `sorry`; add any helper
    lemmas you need (loop invariants, bridging lemmas) in this file. -/
import Aeneas
import Sudoku.Spec
import Sudoku.Code.Funs
import Sudoku.Proofs.Solver

open Aeneas Std Result
open Sudoku.Spec

namespace Sudoku.Proofs

/-! ## sameunit -/

theorem sameunit.wf :
    ∀ (i : ℤ) (j : ℤ) (b : Bool),
      sameunit_spec i j b →
      ((9 ≠ 0) ∧ (9 ≠ 0)) ∧
      (¬((i / 9) = (j / 9)) → (9 ≠ 0) ∧ (9 ≠ 0)) ∧
      (¬(((i / 9) = (j / 9) ∨ (i % 9) = (j % 9))) → (27 ≠ 0) ∧ (27 ≠ 0)) ∧
      (¬(((i / 9) = (j / 9) ∨ (i % 9) = (j % 9))) → (i / 27) = (j / 27) → (9 ≠ 0) ∧ (3 ≠ 0) ∧ (9 ≠ 0) ∧ (3 ≠ 0)) := by
  intros; norm_num

/-! ## completion -/

theorem completion.wf :
    ∀ (g : List U8) (c : List U8),
      completion_spec g c →
      (∀ i : ℤ, 0 ≤ i → i < 81 → (0 ≤ i ∧ i < (c.length : ℤ))) ∧
      (∀ i : ℤ, 0 ≤ i → i < 81 → 1 ≤ ((c[i.toNat]!).val : ℤ) → (0 ≤ i ∧ i < (c.length : ℤ))) ∧
      (∀ i : ℤ, 0 ≤ i → i < 81 → (0 ≤ i ∧ i < (g.length : ℤ))) ∧
      (∀ i : ℤ, 0 ≤ i → i < 81 → ((g[i.toNat]!).val : ℤ) ≠ 0 → (0 ≤ i ∧ i < (c.length : ℤ)) ∧ (0 ≤ i ∧ i < (g.length : ℤ))) ∧
      (∀ i : ℤ, 0 ≤ i → i < 81 → ∀ j : ℤ, 0 ≤ j → j < 81 → i ≠ j → (sameunit_pre i j)) ∧
      (∀ i : ℤ, 0 ≤ i → i < 81 → ∀ j : ℤ, 0 ≤ j → j < 81 → (i ≠ j ∧ sameunit_spec i j true) → (0 ≤ i ∧ i < (c.length : ℤ)) ∧ (0 ≤ j ∧ j < (c.length : ℤ))) := by
  intro g c h
  rcases h with ⟨hg, hc, _⟩
  unfold completion_pre at hg
  unfold sameunit_pre
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> omega

/-! ## prefixthen -/

theorem prefixthen.wf :
    ∀ (g : List U8) (c : List U8) (i : ℤ) (d : ℤ) (h : List U8),
      prefixthen_spec g c i d h →
      (∀ j : ℤ, 0 ≤ j → j < i → (0 ≤ j ∧ j < (h.length : ℤ)) ∧ (0 ≤ j ∧ j < (c.length : ℤ))) ∧
      ((0 ≤ i ∧ i < (h.length : ℤ))) ∧
      (∀ j : ℤ, (i + 1) ≤ j → j < 81 → (0 ≤ j ∧ j < (h.length : ℤ)) ∧ (0 ≤ j ∧ j < (g.length : ℤ))) := by
  intro g c i d h hs
  rcases hs with ⟨⟨⟨⟨hg, hc⟩, hi⟩, hi81⟩, hh, _⟩
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> omega

/-! ## solve -/

-- A completion transfers to a prefix puzzle when it agrees with that prefix.
theorem complete_prefix (g c x h : List U8) (i : ℤ)
    (hx : completion_spec g x)
    (hp : prefixthen_spec g c i ((x[i.toNat]!).val : ℤ) h)
    (he : ∀ j : ℤ, 0 ≤ j → j < i → x[j.toNat]! = c[j.toNat]!) :
    completion_spec h x := by
  refine ⟨hp.2.1, hx.2.1, ?_, hx.2.2.2⟩
  intro j hj hj81
  refine ⟨(hx.2.2.1 j hj hj81).1, ?_⟩
  intro hn
  by_cases hji : j < i
  · exact (he j hj hji).trans (hp.2.2.1 j hj hji).symm
  · by_cases hji2 : j = i
    · subst j
      apply UScalar.eq_of_val_eq
      have hv := hp.2.2.2.1
      omega
    · have hh := hp.2.2.2.2 j (by omega) hj81
      rw [hh] at hn ⊢
      exact (hx.2.2.1 j hj hj81).2 hn

theorem least_unique (g x y : List U8)
    (hx : completion_spec g x) (hy : completion_spec g y)
    (mx : ∀ i : ℤ, 0 ≤ i → i < 81 → ((g[i.toNat]!).val : ℤ) = 0 →
      ∀ d : ℤ, 1 ≤ d → d < ((x[i.toNat]!).val : ℤ) →
      ¬ (∃ h, prefixthen_spec g x i d h ∧ completion_pre h ∧ ∃ c, completion_spec h c))
    (my : ∀ i : ℤ, 0 ≤ i → i < 81 → ((g[i.toNat]!).val : ℤ) = 0 →
      ∀ d : ℤ, 1 ≤ d → d < ((y[i.toNat]!).val : ℤ) →
      ¬ (∃ h, prefixthen_spec g y i d h ∧ completion_pre h ∧ ∃ c, completion_spec h c)) :
    x = y := by
  have point : ∀ n : Nat, n < 81 → x[n]! = y[n]! := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have hxn := hx.2.2.1 n (by omega) (by omega)
      have hyn := hy.2.2.1 n (by omega) (by omega)
      simp only [Int.toNat_natCast] at hxn hyn
      by_cases hg : ((g[n]!).val : ℤ) = 0
      · have hpref : ∀ j : ℤ, 0 ≤ j → j < (n : ℤ) → x[j.toNat]! = y[j.toNat]! := by
          intro j hj hjn
          exact ih j.toNat (by omega) (by omega)
        have notlt : ¬ ((x[n]!).val : ℤ) < ((y[n]!).val : ℤ) := by
          intro hlt
          have hno := my n (by omega) (by omega) (by simpa using hg) _ hxn.1.1 (by simpa using hlt)
          obtain ⟨h, hp⟩ := prefix_witness (g := g) (c := y) (i := n)
            (d := ((x[n]!).val : ℤ))
            (by have := hx.1; unfold completion_pre at this; omega)
            (by have := hy.2.1; omega) (by omega) (by omega) hxn.1.1 hxn.1.2
          have hc := complete_prefix g y x h n hx (by simpa using hp) hpref
          exact hno ⟨h, hp, hc.1, x, hc⟩
        have notgt : ¬ ((y[n]!).val : ℤ) < ((x[n]!).val : ℤ) := by
          intro hlt
          have hno := mx n (by omega) (by omega) (by simpa using hg) _ hyn.1.1 (by simpa using hlt)
          obtain ⟨h, hp⟩ := prefix_witness (g := g) (c := x) (i := n)
            (d := ((y[n]!).val : ℤ))
            (by have := hy.1; unfold completion_pre at this; omega)
            (by have := hx.2.1; omega) (by omega) (by omega) hyn.1.1 hyn.1.2
          have hc := complete_prefix g x y h n hy (by simpa using hp) (fun j hj hjn => (hpref j hj hjn).symm)
          exact hno ⟨h, hp, hc.1, y, hc⟩
        apply UScalar.eq_of_val_eq
        omega
      · exact (hxn.2 hg).trans (hyn.2 hg).symm
  apply List.ext_getElem
  · have := hx.2.1; have := hy.2.1; omega
  · intro i hi hj
    have hl := hx.2.1
    simpa [getElem!_pos, hi, hj] using point i (by omega)

theorem solve.unambiguous :
    ∀ (g : List U8) (o₁ : Option (List U8)) (o₂ : Option (List U8)),
      solve_spec g o₁ → solve_spec g o₂ → o₁ = o₂ := by
  intro g a b ha hb
  by_cases hd : completion_pre g ∧ ∃ c, completion_spec g c
  · obtain ⟨ha1, ha2, ha3⟩ := ha.2.1 hd
    obtain ⟨hb1, hb2, hb3⟩ := hb.2.1 hd
    have he := least_unique g a.get! b.get! ha2 hb2 ha3 hb3
    cases a <;> cases b <;> simp_all
  · exact (ha.2.2 hd).trans (hb.2.2 hd).symm

theorem solve.ens_0 :
    ∀ (g : List U8) (a : Option (List U8)),
      solve_spec g a → (a.isSome = true ↔ (completion_pre g ∧ ∃ (o0 : List U8), completion_spec g o0)) := by
  intro g a h
  by_cases hd : completion_pre g ∧ ∃ c, completion_spec g c
  · exact ⟨fun _ => hd, fun _ => (h.2.1 hd).1⟩
  · have ha := h.2.2 hd
    simp [ha, hd]

theorem solve.ens_1 :
    ∀ (g : List U8) (a : Option (List U8)),
      solve_spec g a → (a.isSome = true → completion_spec g a.get!) := by
  intro g a h ha
  by_cases hd : completion_pre g ∧ ∃ c, completion_spec g c
  · exact (h.2.1 hd).2.1
  · have := h.2.2 hd
    simp_all

theorem solve.wf :
    ∀ (g : List U8) (a : Option (List U8)),
      solve_spec g a →
      ((completion_pre g ∧ ∃ (o0 : List U8), completion_spec g o0) → (a.isSome = true) ∧ (completion_pre g)) ∧
      ((completion_pre g ∧ ∃ (o0 : List U8), completion_spec g o0) → ∀ i : ℤ, 0 ≤ i → i < 81 → (0 ≤ i ∧ i < (g.length : ℤ))) ∧
      ((completion_pre g ∧ ∃ (o0 : List U8), completion_spec g o0) → ∀ i : ℤ, 0 ≤ i → i < 81 → ((g[i.toNat]!).val : ℤ) = 0 → (a.isSome = true) ∧ (0 ≤ i ∧ i < (a.get!.length : ℤ))) ∧
      ((completion_pre g ∧ ∃ (o0 : List U8), completion_spec g o0) → ∀ i : ℤ, 0 ≤ i → i < 81 → ((g[i.toNat]!).val : ℤ) = 0 → ∀ d : ℤ, 1 ≤ d → d < ((a.get![i.toNat]!).val : ℤ) → (a.isSome = true) ∧ (prefixthen_pre g a.get! i d)) ∧
      (a.isSome = true → (a.isSome = true) ∧ (completion_pre g)) := by
  intro g a h
  have hg := h.1
  unfold solve_pre at hg
  have hs := solve.ens_0 g a h
  have hc := solve.ens_1 g a h
  unfold prefixthen_pre completion_pre
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hd; exact ⟨hs.mpr hd, hg⟩
  · intros; omega
  · intro hd i hi hi81 hz
    have ha := hs.mpr hd
    have hl := (hc ha).2.1
    exact ⟨ha, by omega⟩
  · intro hd i hi hi81 hz d hd1 hdlt
    have ha := hs.mpr hd
    exact ⟨ha, ⟨⟨⟨hg, (hc ha).2.1⟩, hi⟩, hi81⟩⟩
  · intro ha; exact ⟨ha, hg⟩

/-! ## digitof -/

theorem digitof.unambiguous :
    ∀ (ch : U8) (o₁ : U8) (o₂ : U8),
      digitof_spec ch o₁ → digitof_spec ch o₂ → o₁ = o₂ := by
  intro ch x y hx hy
  apply UScalar.eq_of_val_eq
  have := hx.2.trans hy.2.symm
  omega

theorem digitof.ens_0 :
    ∀ (ch : U8) (d : U8),
      digitof_spec ch d → (0 ≤ (d.val : ℤ) ∧ (d.val : ℤ) ≤ 9) := by
  intro ch d h
  have he := h.2
  split_ifs at he <;> omega

/-! ## parsepuzzle -/

theorem parsepuzzle.unambiguous :
    ∀ (s : List U8) (o₁ : List U8) (o₂ : List U8),
      parsepuzzle_spec s o₁ → parsepuzzle_spec s o₂ → o₁ = o₂ := by
  intro s x y hx hy
  apply List.ext_getElem
  · have := hx.2.1; have := hy.2.1; omega
  · intro i hi hj
    have hxlen := hx.2.1
    have hi81 : (i : ℤ) < 81 := by omega
    have he := digitof.unambiguous _ _ _ (hx.2.2 i (by omega) hi81) (hy.2.2 i (by omega) hi81)
    simpa [getElem!_pos, hi, hj] using he

theorem parsepuzzle.ens_0 :
    ∀ (s : List U8) (g : List U8),
      parsepuzzle_spec s g → (g.length : ℤ) = 81 := by
  intro s g h; exact h.2.1

theorem parsepuzzle.wf :
    ∀ (s : List U8) (g : List U8),
      parsepuzzle_spec s g →
      ∀ i : ℤ, 0 ≤ i → i < 81 → (0 ≤ i ∧ i < (g.length : ℤ)) ∧ (0 ≤ i ∧ i < (s.length : ℤ)) := by
  intro s g h i hi hi81
  have hs := h.1; have hg := h.2.1
  unfold parsepuzzle_pre at hs
  omega

/-! ## digitchar -/

theorem digitchar.unambiguous :
    ∀ (d : U8) (o₁ : U8) (o₂ : U8),
      digitchar_spec d o₁ → digitchar_spec d o₂ → o₁ = o₂ := by
  intro d x y hx hy
  apply UScalar.eq_of_val_eq
  have := hx.2.trans hy.2.symm
  omega

/-! ## showgrid -/

theorem showgrid.unambiguous :
    ∀ (c : List U8) (o₁ : List U8) (o₂ : List U8),
      showgrid_spec c o₁ → showgrid_spec c o₂ → o₁ = o₂ := by
  intro c x y hx hy
  apply List.ext_getElem
  · have := hx.2.1; have := hy.2.1; omega
  · intro i hi hj
    have hxlen := hx.2.1
    by_cases hic : i < c.length
    · have he := digitchar.unambiguous _ _ _ (hx.2.2.1 i (by omega) (by omega)) (hy.2.2.1 i (by omega) (by omega))
      simpa [getElem!_pos, hi, hj] using he
    · have hie : i = c.length := by omega
      subst i
      apply UScalar.eq_of_val_eq
      have h1 := hx.2.2.2; have h2 := hy.2.2.2
      simp only [Int.toNat_natCast, getElem!_pos, hi, hj] at h1 h2
      omega

theorem showgrid.ens_0 :
    ∀ (c : List U8) (s : List U8),
      showgrid_spec c s → (s.length : ℤ) = ((c.length : ℤ) + 1) := by
  intro c s h; exact h.2.1

theorem showgrid.wf :
    ∀ (c : List U8) (s : List U8),
      showgrid_spec c s →
      (∀ i : ℤ, 0 ≤ i → i < (c.length : ℤ) → (0 ≤ i ∧ i < (s.length : ℤ)) ∧ (0 ≤ i ∧ i < (c.length : ℤ))) ∧
      ((0 ≤ (c.length : ℤ) ∧ (c.length : ℤ) < (s.length : ℤ))) := by
  intro c s h
  have hl := h.2.1
  constructor
  · intros; omega
  · omega

/-! ## nosolutiontext -/

theorem nosolutiontext.wf :
    ∀  (s : List U8),
      nosolutiontext_spec  s →
      ((0 < (s.length : ℤ))) ∧
      ((1 < (s.length : ℤ))) ∧
      ((2 < (s.length : ℤ))) ∧
      ((3 < (s.length : ℤ))) ∧
      ((4 < (s.length : ℤ))) ∧
      ((5 < (s.length : ℤ))) ∧
      ((6 < (s.length : ℤ))) ∧
      ((7 < (s.length : ℤ))) ∧
      ((8 < (s.length : ℤ))) ∧
      ((9 < (s.length : ℤ))) ∧
      ((10 < (s.length : ℤ))) ∧
      ((11 < (s.length : ℤ))) := by
  intro s h
  have hl := h.2.1
  omega

theorem nosolutiontext.exists :
    nosolutiontext_pre  → ∃ s, nosolutiontext_spec  s := by
  intro _
  refine ⟨[110#u8, 111#u8, 32#u8, 115#u8, 111#u8, 108#u8, 117#u8, 116#u8, 105#u8, 111#u8, 110#u8, 10#u8], ?_⟩
  norm_num [nosolutiontext_spec, nosolutiontext_pre]

/-! ## showanswer -/

theorem nosolutiontext.unique (x y : List U8)
    (hx : nosolutiontext_spec x) (hy : nosolutiontext_spec y) : x = y := by
  apply List.ext_getElem
  · have := hx.2.1; have := hy.2.1; omega
  · intro i hi hj
    have hl := hx.2.1
    have hib : i < 12 := by omega
    apply UScalar.eq_of_val_eq
    unfold nosolutiontext_spec at hx hy
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by omega
    rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [getElem!_pos] <;> omega

theorem showanswer.unambiguous :
    ∀ (a : Option (List U8)) (o₁ : List U8) (o₂ : List U8),
      showanswer_spec a o₁ → showanswer_spec a o₂ → o₁ = o₂ := by
  intro a x y hx hy
  by_cases ha : a.isSome = true
  · exact showgrid.unambiguous _ _ _ (hx.2.1 ha) (hy.2.1 ha)
  · exact nosolutiontext.unique x y (hx.2.2 ha) (hy.2.2 ha)

theorem showanswer.wf :
    ∀ (a : Option (List U8)) (s : List U8),
      showanswer_spec a s →
      (a.isSome = true → (a.isSome = true)) ∧
      (a.isSome = true → (a.isSome = true) ∧ (showgrid_pre a.get!)) := by
  intro a s h
  exact ⟨fun ha => ha, fun ha => ⟨ha, h.1 ha⟩⟩


@[step] theorem digitof_code (ch : U8) :
    Sudoku.solution.digitof ch ⦃ d => digitof_spec ch d ⦄ := by
  unfold Sudoku.solution.digitof
  step* <;> simp_all [digitof_spec, digitof_pre] <;> omega

@[step] theorem digitchar_code (d : U8) :
    Sudoku.solution.digitchar d ⦃ ch => digitchar_spec d ch ⦄ := by
  unfold Sudoku.solution.digitchar
  step* <;> simp_all [digitchar_spec, digitchar_pre] <;> omega

theorem digitof.impl_correct :
    ∀ (ch : U8), digitof_pre ch →
      Sudoku.spec.digitof ch ⦃ d => digitof_spec ch d ⦄ := by
  intro ch _; exact digitof_code ch

theorem digitchar.impl_correct :
    ∀ (d : U8), digitchar_pre d →
      Sudoku.spec.digitchar d ⦃ ch => digitchar_spec d ch ⦄ := by
  intro d _; exact digitchar_code d


def MapInv (f : U8 → U8 → Prop) (s out : List U8) (i : Nat) : Prop :=
  out.length = i ∧ i ≤ s.length ∧ ∀ j : Nat, j < i → f s[j]! out[j]!

theorem map_push (f : U8 → U8 → Prop) (s out : List U8) (i : Nat) (x : U8)
    (h : MapInv f s out i) (hi : i < s.length) (hx : f s[i]! x) :
    MapInv f s (out ++ [x]) (i + 1) := by
  refine ⟨by simp [h.1], by omega, ?_⟩
  intro j hj
  by_cases he : j = i
  · subst j
    simpa [← h.1] using hx
  · have hji : j < i := by omega
    have hjout : j < out.length := by have := h.1; omega
    have hjnew : j < (out ++ [x]).length := by simp; omega
    simpa only [List.getElem!_append_left out [x] j hjout] using h.2.2 j hji


theorem parsepuzzle_body (s : Aeneas.Std.Slice U8) (out : alloc.vec.Vec U8) (i : Usize)
    (hs : s.val.length = 81) (h : MapInv digitof_spec s.val out.val i.val) :
    Sudoku.solution.parsepuzzle_loop.body s out i ⦃ r =>
      match r with
      | .done out1 => MapInv digitof_spec s.val out1.val 81
      | .cont st => MapInv digitof_spec s.val st.1.val st.2.val ∧ 81 - st.2.val < 81 - i.val ⦄ := by
  have hi : i.val ≤ 81 := by have := h.2.1; omega
  have hl : out.val.length = i.val := h.1
  unfold Sudoku.solution.parsepuzzle_loop.body
  dsimp only
  split
  · rename_i hlt
    step as ⟨x, hx⟩
    step as ⟨d, hd⟩
    step as ⟨out1, hout⟩
    step as ⟨i1, hi1⟩
    have hir : i.val < s.val.length := by scalar_tac
    have hx1 : digitof_spec s.val[i.val]! d := by simpa [hx, getElem!_pos, hir] using hd
    have hm := map_push digitof_spec s.val out.val i.val d h hir hx1
    constructor
    · simpa [hout, hi1] using hm
    · omega
  · rename_i hge
    have hie : i.val = 81 := by scalar_tac
    simpa [hie] using h

@[step] theorem parsepuzzle_loop_code (s : Aeneas.Std.Slice U8) (out : alloc.vec.Vec U8) (i : Usize)
    (hs : s.val.length = 81) (h : MapInv digitof_spec s.val out.val i.val) :
    Sudoku.solution.parsepuzzle_loop s out i ⦃ out1 => MapInv digitof_spec s.val out1.val 81 ⦄ := by
  unfold Sudoku.solution.parsepuzzle_loop
  apply loop.spec_decr_nat (fun st => 81 - st.2.val)
    (fun st => MapInv digitof_spec s.val st.1.val st.2.val)
  · rintro ⟨out1, i1⟩ hinv
    apply Aeneas.Std.WP.spec_mono (parsepuzzle_body s out1 i1 hs hinv)
    intro r hr; cases r <;> exact hr
  · exact h

theorem showgrid_body (s : Aeneas.Std.Slice U8) (out : alloc.vec.Vec U8) (i : Usize)
    (hs : s.val.length = 81) (h : MapInv digitchar_spec s.val out.val i.val) :
    Sudoku.solution.showgrid_loop.body s out i ⦃ r =>
      match r with
      | .done out1 => MapInv digitchar_spec s.val out1.val 81
      | .cont st => MapInv digitchar_spec s.val st.1.val st.2.val ∧ 81 - st.2.val < 81 - i.val ⦄ := by
  have hi : i.val ≤ 81 := by have := h.2.1; omega
  have hl : out.val.length = i.val := h.1
  unfold Sudoku.solution.showgrid_loop.body
  dsimp only
  split
  · rename_i hlt
    step as ⟨x, hx⟩
    step as ⟨d, hd⟩
    step as ⟨out1, hout⟩
    step as ⟨i1, hi1⟩
    have hir : i.val < s.val.length := by scalar_tac
    have hx1 : digitchar_spec s.val[i.val]! d := by simpa [hx, getElem!_pos, hir] using hd
    have hm := map_push digitchar_spec s.val out.val i.val d h hir hx1
    constructor
    · simpa [hout, hi1] using hm
    · omega
  · rename_i hge
    have hie : i.val = 81 := by scalar_tac
    simpa [hie] using h

@[step] theorem showgrid_loop_code (s : Aeneas.Std.Slice U8) (out : alloc.vec.Vec U8) (i : Usize)
    (hs : s.val.length = 81) (h : MapInv digitchar_spec s.val out.val i.val) :
    Sudoku.solution.showgrid_loop s out i ⦃ out1 => MapInv digitchar_spec s.val out1.val 81 ⦄ := by
  unfold Sudoku.solution.showgrid_loop
  apply loop.spec_decr_nat (fun st => 81 - st.2.val)
    (fun st => MapInv digitchar_spec s.val st.1.val st.2.val)
  · rintro ⟨out1, i1⟩ hinv
    apply Aeneas.Std.WP.spec_mono (showgrid_body s out1 i1 hs hinv)
    intro r hr; cases r <;> exact hr
  · exact h


theorem parsepuzzle.impl_correct :
    ∀ (s : Aeneas.Std.Slice U8), parsepuzzle_pre s.val →
      Sudoku.spec.parsepuzzle s ⦃ g => parsepuzzle_spec s.val g.val ⦄ := by
  intro s hs
  have hlen : s.val.length = 81 := by unfold parsepuzzle_pre at hs; omega
  unfold Sudoku.spec.parsepuzzle Sudoku.solution.parsepuzzle
  have hi : MapInv digitof_spec s.val (alloc.vec.Vec.new U8).val (0#usize).val := by
    simp [MapInv]
  step as ⟨out, hout⟩
  refine ⟨hs, by exact_mod_cast hout.1, ?_⟩
  intro i hi hi81
  exact hout.2.2 i.toNat (by omega)

@[step] theorem showgrid_code (c : Aeneas.Std.Slice U8) (hc : showgrid_pre c.val) :
    Sudoku.solution.showgrid c ⦃ s => showgrid_spec c.val s.val ⦄ := by
  have hlen : c.val.length = 81 := by unfold showgrid_pre at hc; omega
  have hi : MapInv digitchar_spec c.val (alloc.vec.Vec.new U8).val (0#usize).val := by
    simp [MapInv]
  unfold Sudoku.solution.showgrid
  step as ⟨out, hout⟩
  step as ⟨out1, hout1⟩
  have hl := hout.1
  refine ⟨hc, ?_, ?_, ?_⟩
  · simp [hout1, hl, hlen]
  · intro i hi hi81
    have hj : i.toNat < out.val.length := by omega
    rw [hout1, List.getElem!_append_left _ _ _ hj]
    exact hout.2.2 i.toNat (by omega)
  · simp [hout1, hlen, ← hl]

theorem showgrid.impl_correct :
    ∀ (c : Aeneas.Std.Slice U8), showgrid_pre c.val →
      Sudoku.spec.showgrid c ⦃ s => showgrid_spec c.val s.val ⦄ := by
  intro c hc; exact showgrid_code c hc

theorem showanswer.impl_correct :
    ∀ (a : Option (alloc.vec.Vec U8)), showanswer_pre a →
      Sudoku.spec.showanswer a ⦃ s => showanswer_spec a s.val ⦄ := by
  intro a ha
  unfold Sudoku.spec.showanswer Sudoku.solution.showanswer
  cases a with
  | none =>
    step* <;> simp_all [showanswer_spec, showanswer_pre, nosolutiontext_spec, nosolutiontext_pre] <;> scalar_tac
  | some c =>
    have hc : showgrid_pre (alloc.vec.Vec.deref c).val := by
      simpa [showanswer_pre, showgrid_pre, alloc.vec.Vec.deref] using ha
    step as ⟨out, hout⟩
    simpa [showanswer_spec, showanswer_pre, alloc.vec.Vec.deref] using And.intro ha hout


theorem solve.impl_correct :
    ∀ (g : Aeneas.Std.Slice U8), solve_pre g.val →
      Sudoku.spec.solve g ⦃ a => solve_spec g.val a ⦄ := by
  intro g hg
  have hgl : g.val.length = 81 := by unfold solve_pre at hg; omega
  have hinit : InitInv (alloc.vec.Vec.new U8) 0#i32 := by simp [InitInv]
  unfold Sudoku.spec.solve Sudoku.solution.solve
  step as ⟨c, hc⟩
  have hv : Valid g.val c.val (0#usize).val := by simp [Valid, hgl, hc]
  step as ⟨b, out, hout⟩
  have hcall : ∀ x, completion_spec g.val x → Candidate g.val c.val 0 1 x := by
    intro x hx
    exact ⟨hx, by simp [PrefixEq], fun _ => (completion_digit hx (by omega : 0 < 81)).1⟩
  split
  · rename_i hb
    have hr : SearchPost g.val c.val 0 1 true out.val := by simpa [hb] using hout
    exact (WP.spec_ok _).mpr (least_solve_spec hr.2.2.1.1 (fun x hx => hr.2.2.2 x (hcall x hx)))
  · rename_i hb
    have hr : SearchPost g.val c.val 0 1 false out.val := by simpa [show b = false by simp_all] using hout
    refine ⟨hg, ?_, fun _ => rfl⟩
    rintro ⟨_, x, hx⟩
    exact False.elim (hr.2.2 ⟨x, hcall x hx⟩)

end Sudoku.Proofs
