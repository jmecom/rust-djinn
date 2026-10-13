import Aeneas
import Sudoku.Spec
import Sudoku.Code.Funs
open Aeneas Std Result
open Sudoku.Spec
namespace Sudoku.Proofs

def Unit (i j : Nat) : Prop :=
  i / 9 = j / 9 ∨ i % 9 = j % 9 ∨ (i / 27 = j / 27 ∧ (i % 9) / 3 = (j % 9) / 3)

theorem unit_symm {i j : Nat} : Unit i j → Unit j i := by
  unfold Unit; aesop

theorem unit_spec (i j : Nat) (hi : i < 81) (hj : j < 81) :
    sameunit_spec i j true ↔ Unit i j := by
  simp [sameunit_spec, sameunit_pre, Unit, Int.natCast_ediv, Int.natCast_emod,
    hi, hj, or_assoc]
  norm_cast

@[step] theorem same_unit_code (i j : Usize) :
    Sudoku.solution.same_unit i j ⦃ b => b = true ↔ Unit i.val j.val ⦄ := by
  unfold Sudoku.solution.same_unit
  step*
  simp_all [Unit, UScalar.eq_equiv, or_assoc]

def NoConflict (c : List U8) (i : Nat) (d : U8) (j : Nat) : Prop :=
  ∀ k : Nat, k < j → Unit i k → c[k]! ≠ d

theorem noconflict_succ (c : List U8) (i j : Nat) (d : U8) :
    NoConflict c i d (j+1) ↔ NoConflict c i d j ∧ (Unit i j → c[j]! ≠ d) := by
  unfold NoConflict
  constructor
  · intro h; exact ⟨fun k hk => h k (by omega), h j (by omega)⟩
  · rintro ⟨h, hj⟩ k hk hu
    by_cases he : k = j
    · subst k; exact hj hu
    · exact h k (by omega) hu

theorem allowed_body (c : Aeneas.Std.Slice U8) (i j : Usize) (d : U8) (b : Bool)
    (hc : c.val.length = 81) (hi : i.val < 81) (hj : j.val ≤ i.val)
    (hb : b = true ↔ NoConflict c.val i.val d j.val) :
    Sudoku.solution.allowed_loop.body c i d j b ⦃ r =>
      match r with
      | .done b1 => b1 = true ↔ NoConflict c.val i.val d i.val
      | .cont st => (st.1.val ≤ i.val ∧
          (st.2 = true ↔ NoConflict c.val i.val d st.1.val)) ∧ i.val - st.1.val < i.val - j.val ⦄ := by
  have hjlen : j.val < c.val.length := by omega
  have hget := getElem!_pos c.val j.val hjlen
  unfold Sudoku.solution.allowed_loop.body
  step*
  split
  · step*
    split <;> step* <;> simp_all [noconflict_succ, UScalar.lt_equiv] <;> omega
  · step*
    simp_all [noconflict_succ, UScalar.lt_equiv] <;> omega

@[step] theorem allowed_code (c : Aeneas.Std.Slice U8) (i : Usize) (d : U8)
    (hc : c.val.length = 81) (hi : i.val < 81) :
    Sudoku.solution.allowed c i d ⦃ b => b = true ↔ NoConflict c.val i.val d i.val ⦄ := by
  unfold Sudoku.solution.allowed Sudoku.solution.allowed_loop
  apply loop.spec_decr_nat (fun st => i.val - st.1.val)
    (fun st => st.1.val ≤ i.val ∧ (st.2 = true ↔ NoConflict c.val i.val d st.1.val))
  · rintro ⟨j, b⟩ ⟨hj, hb⟩
    apply Aeneas.Std.WP.spec_mono (allowed_body c i j d b hc hi hj hb)
    intro r hr; cases r <;> exact hr
  · simp [NoConflict]


def PrefixEq (a b : List U8) (n : Nat) : Prop :=
  ∀ k : Nat, k < n → a[k]! = b[k]!

def Valid (g c : List U8) (n : Nat) : Prop :=
  g.length = 81 ∧ c.length = 81 ∧ n ≤ 81 ∧
  (∀ k : Nat, k < n → 1 ≤ c[k]!.val ∧ c[k]!.val ≤ 9 ∧
    (g[k]! ≠ 0#u8 → c[k]! = g[k]!)) ∧
  (∀ k : Nat, k < n → ∀ j : Nat, j < k → Unit k j → c[k]! ≠ c[j]!)

def Candidate (g c : List U8) (n d : Nat) (x : List U8) : Prop :=
  completion_spec g x ∧ PrefixEq c x n ∧ (n < 81 → d ≤ x[n]!.val)

def LexLE (a b : List U8) : Prop :=
  ∀ k : Nat, k < 81 → PrefixEq a b k → a[k]!.val ≤ b[k]!.val

def SearchPost (g c : List U8) (n d : Nat) (b : Bool) (out : List U8) : Prop :=
  out.length = 81 ∧ PrefixEq c out n ∧
  if b then Candidate g c n d out ∧ (∀ x, Candidate g c n d x → LexLE out x)
  else ¬ ∃ x, Candidate g c n d x

theorem prefix_refl (c : List U8) (n : Nat) : PrefixEq c c n := fun _ _ => rfl

theorem prefix_trans {a b c : List U8} {n : Nat} (hab : PrefixEq a b n)
    (hbc : PrefixEq b c n) : PrefixEq a c n := fun k hk => (hab k hk).trans (hbc k hk)

theorem prefix_symm {a b : List U8} {n : Nat} (hab : PrefixEq a b n) :
    PrefixEq b a n := fun k hk => (hab k hk).symm

theorem get_set (c : List U8) (i j : Nat) (d : U8) (hj : j < c.length) :
    (c.set i d)[j]! = if i = j then d else c[j]! := by
  have hj1 : j < (c.set i d).length := by simpa using hj
  rw [getElem!_pos (c.set i d) j hj1, List.getElem_set, getElem!_pos c j hj]

theorem prefix_set (c : List U8) (n : Nat) (d : U8) (hn : n < c.length) :
    PrefixEq c (c.set n d) n := by
  intro k hk
  rw [get_set c n k d (by omega), if_neg (by omega)]

theorem completion_digit {g x : List U8} (h : completion_spec g x)
    {n : Nat} (hn : n < 81) : 1 ≤ x[n]!.val ∧ x[n]!.val ≤ 9 := by
  have hh := (h.2.2.1 n (by omega) (by omega)).1
  simpa using hh

theorem completion_given {g x : List U8} (h : completion_spec g x)
    {n : Nat} (hn : n < 81) (hg : g[n]! ≠ 0#u8) : x[n]! = g[n]! := by
  apply h.2.2.1 n (by omega) (by omega) |>.2
  simp only [Int.toNat_natCast]
  intro hz
  apply hg
  apply UScalar.eq_of_val_eq
  simpa using hz

theorem completion_unit {g x : List U8} (h : completion_spec g x)
    {i j : Nat} (hi : i < 81) (hj : j < 81) (hne : i ≠ j) (hu : Unit i j) :
    x[i]! ≠ x[j]! := by
  exact h.2.2.2 i (by omega) (by omega) j (by omega) (by omega)
    ⟨by omega, (unit_spec i j hi hj).mpr hu⟩

theorem valid_complete {g c : List U8} (h : Valid g c 81) : completion_spec g c := by
  refine ⟨by unfold completion_pre; exact_mod_cast h.1, by exact_mod_cast h.2.1, ?_, ?_⟩
  · intro i hi hi81
    have hh := h.2.2.2.1 i.toNat (by omega)
    refine ⟨by exact_mod_cast And.intro hh.1 hh.2.1, ?_⟩
    intro hg
    apply hh.2.2
    intro hz
    simp [hz] at hg
  · intro i hi hi81 j hj hj81 hn
    have hu : Unit i.toNat j.toNat := by
      apply (unit_spec _ _ (by omega) (by omega)).mp
      simpa [Int.toNat_of_nonneg hi, Int.toNat_of_nonneg hj] using hn.2
    by_cases hij : j < i
    · exact h.2.2.2.2 i.toNat (by omega) j.toNat (by omega) hu
    · exact Ne.symm (h.2.2.2.2 j.toNat (by omega) i.toNat (by omega) (unit_symm hu))

theorem valid_prefix {g c out : List U8} {n : Nat} (h : Valid g c n)
    (hl : out.length = 81) (hp : PrefixEq c out n) : Valid g out n := by
  refine ⟨h.1, hl, h.2.2.1, ?_, ?_⟩
  · intro k hk
    rw [← hp k hk]
    exact h.2.2.2.1 k hk
  · intro k hk j hj hu
    rw [← hp k hk, ← hp j (by omega)]
    exact h.2.2.2.2 k hk j hj hu

theorem valid_extend {g c : List U8} {n : Nat} {d : U8} (h : Valid g c n)
    (hn : n < 81) (hd1 : 1 ≤ d.val) (hd9 : d.val ≤ 9)
    (hg : g[n]! = 0#u8 ∨ g[n]! = d) (hc : NoConflict c n d n) :
    Valid g (c.set n d) (n+1) := by
  have hlen := h.2.1
  refine ⟨h.1, by simpa using hlen, by omega, ?_, ?_⟩
  · intro k hk
    rw [get_set c n k d (by omega)]
    split_ifs with he
    · subst k
      refine ⟨hd1, hd9, ?_⟩
      intro hz
      rcases hg with hg | hg
      · exact False.elim (hz hg)
      · exact hg.symm
    · exact h.2.2.2.1 k (by omega)
  · intro k hk j hj hu
    have hnj : n ≠ j := by omega
    simp only [get_set c n k d (by omega), get_set c n j d (by omega), if_neg hnj]
    split_ifs with he
    · subst k; exact Ne.symm (hc j hj hu)
    · exact h.2.2.2.2 k (by omega) j hj hu

theorem candidate_rebase {g c out x : List U8} {n d : Nat} (hp : PrefixEq c out n) :
    Candidate g c n d x ↔ Candidate g out n d x := by
  constructor
  · rintro ⟨hc, hx, hd⟩; exact ⟨hc, prefix_trans (prefix_symm hp) hx, hd⟩
  · rintro ⟨hc, hx, hd⟩; exact ⟨hc, prefix_trans hp hx, hd⟩

theorem candidate_child {g c x : List U8} {n : Nat} {d : U8}
    (hlen : c.length = 81) (hn : n < 81) (hd : 1 ≤ d.val) :
    Candidate g (c.set n d) (n+1) 1 x ↔
      Candidate g c n d.val x ∧ x[n]! = d := by
  have hset : (c.set n d)[n]! = d := by simp [get_set, hlen, hn]
  constructor
  · rintro ⟨hc, hp, hmin⟩
    have he : x[n]! = d := (hp n (by omega)).symm.trans hset
    refine ⟨⟨hc, prefix_trans (prefix_set c n d (by omega)) (fun k hk => hp k (by omega)), ?_⟩, he⟩
    intro _; simp [he]
  · rintro ⟨⟨hc, hp, hmin⟩, he⟩
    refine ⟨hc, ?_, fun hn1 => (completion_digit hc hn1).1⟩
    intro k hk
    by_cases hkn : k = n
    · subst k; exact hset.trans he.symm
    · rw [get_set c n k d (by omega), if_neg (by omega)]
      exact hp k (by omega)

theorem candidate_can {g c x : List U8} {n : Nat} {d : U8}
    (hn : n < 81) (hx : Candidate g c n d.val x) (he : x[n]! = d) :
    (g[n]! = 0#u8 ∨ g[n]! = d) ∧ NoConflict c n d n := by
  constructor
  · by_cases hg : g[n]! = 0#u8
    · exact Or.inl hg
    · exact Or.inr ((completion_given hx.1 hn hg).symm.trans he)
  · intro j hj hu
    rw [hx.2.1 j hj, ← he]
    exact Ne.symm (completion_unit hx.1 hn (by omega) (by omega) hu)


theorem candidate_cases {g c x : List U8} {n : Nat} {d : U8}
    (hlen : c.length = 81) (hn : n < 81) (hd : 1 ≤ d.val)
    (hx : Candidate g c n d.val x) :
    Candidate g (c.set n d) (n+1) 1 x ∨ Candidate g c n (d.val+1) x := by
  by_cases he : x[n]! = d
  · exact Or.inl ((candidate_child hlen hn hd).mpr ⟨hx, he⟩)
  · apply Or.inr
    refine ⟨hx.1, hx.2.1, ?_⟩
    intro _
    have hmin := hx.2.2 hn
    have hne : x[n]!.val ≠ d.val := by
      intro hv; exact he (UScalar.eq_of_val_eq hv)
    omega

theorem candidate_weaken {g c x : List U8} {n d : Nat}
    (hx : Candidate g c n (d+1) x) : Candidate g c n d x := by
  refine ⟨hx.1, hx.2.1, ?_⟩
  intro hn; have := hx.2.2 hn; omega

theorem lex_first {a b : List U8} {n : Nat}
    (hp : PrefixEq a b n) (hd : a[n]!.val < b[n]!.val) : LexLE a b := by
  intro k hk hpk
  by_cases hkn : k < n
  · rw [hp k hkn]
  · by_cases he : k = n
    · subst k; omega
    · have := hpk n (by omega)
      rw [this] at hd
      omega

theorem found_post {g c out : List U8} {n : Nat} {d : U8}
    (hlen : c.length = 81) (hn : n < 81) (hd : 1 ≤ d.val)
    (h : SearchPost g (c.set n d) (n+1) 1 true out) :
    SearchPost g c n d.val true out := by
  have hc : Candidate g (c.set n d) (n+1) 1 out := h.2.2.1
  have hm : ∀ x, Candidate g (c.set n d) (n+1) 1 x → LexLE out x := h.2.2.2
  have hc0 := (candidate_child hlen hn hd).mp hc
  refine ⟨h.1, hc0.1.2.1, hc0.1, ?_⟩
  intro x hx
  rcases candidate_cases hlen hn hd hx with hx1 | hx1
  · exact hm x hx1
  · apply lex_first (prefix_trans (prefix_symm hc0.1.2.1) hx.2.1)
    have hh := hx1.2.2 hn
    rw [hc0.2]
    omega

theorem skip_post {g c mid out : List U8} {n : Nat} {d : U8} {b : Bool}
    (hlen : c.length = 81) (hn : n < 81) (hd : 1 ≤ d.val)
    (hp : PrefixEq c mid n)
    (hno : ¬ ∃ x, Candidate g (c.set n d) (n+1) 1 x)
    (h : SearchPost g mid n (d.val+1) b out) : SearchPost g c n d.val b out := by
  have allnext : ∀ x, Candidate g c n d.val x → Candidate g mid n (d.val+1) x := by
    intro x hx
    rcases candidate_cases hlen hn hd hx with hx1 | hx1
    · exact False.elim (hno ⟨x, hx1⟩)
    · exact (candidate_rebase hp).mp hx1
  refine ⟨h.1, prefix_trans hp h.2.1, ?_⟩
  cases b with
  | false =>
    intro he
    obtain ⟨x, hx⟩ := he
    exact h.2.2 ⟨x, allnext x hx⟩
  | true =>
    exact ⟨candidate_weaken ((candidate_rebase hp).mpr h.2.2.1),
      fun x hx => h.2.2.2 x (allnext x hx)⟩

theorem rejected_child {g c : List U8} {n : Nat} {d : U8}
    (hlen : c.length = 81) (hn : n < 81) (hd : 1 ≤ d.val)
    (hno : ¬ ((g[n]! = 0#u8 ∨ g[n]! = d) ∧ NoConflict c n d n)) :
    ¬ ∃ x, Candidate g (c.set n d) (n+1) 1 x := by
  rintro ⟨x, hx⟩
  have hh := (candidate_child hlen hn hd).mp hx
  exact hno (candidate_can hn hh.1 hh.2)


theorem leaf_post {g c : List U8} {d : Nat} (hv : Valid g c 81) :
    SearchPost g c 81 d true c := by
  refine ⟨hv.2.1, prefix_refl c 81, ⟨valid_complete hv, prefix_refl c 81, by omega⟩, ?_⟩
  intro x hx k hk _
  rw [hx.2.1 k hk]

theorem exhausted_post {g c : List U8} {n : Nat} (hv : Valid g c n) (hn : n < 81) :
    SearchPost g c n 10 false c := by
  refine ⟨hv.2.1, prefix_refl c n, ?_⟩
  rintro ⟨x, hx⟩
  have hh := hx.2.2 hn
  have hh2 := (completion_digit hx.1 hn).2
  omega

@[step] theorem search_code (g : Aeneas.Std.Slice U8) (c : alloc.vec.Vec U8)
    (i : Usize) (d : U8) (hv : Valid g.val c.val i.val)
    (hd1 : 1 ≤ d.val) (hd10 : d.val ≤ 10) :
    Sudoku.solution.search g c i d ⦃ r => SearchPost g.val c.val i.val d.val r.1 r.2.val ⦄ := by
  generalize hm : (81-i.val)*10 + (10-d.val) = m
  induction m using Nat.strong_induction_on generalizing c i d with
  | h m ih =>
    have hgl := hv.1
    have hcl := hv.2.1
    have hi81 := hv.2.2.1
    unfold Sudoku.solution.search
    split
    · rename_i he
      have hie : i.val = 81 := by scalar_tac
      simpa [hie] using leaf_post (d := d.val) (by simpa [hie] using hv)
    · rename_i hne
      have hi : i.val < 81 := by scalar_tac
      split
      · rename_i he
        have hde : d.val = 10 := by scalar_tac
        simpa [hde] using exhausted_post hv hi
      · rename_i hdne
        have hd9 : d.val ≤ 9 := by scalar_tac
        step as ⟨given, hgiven⟩
        have hcderef : (alloc.vec.Vec.deref c).val.length = 81 := by simpa [alloc.vec.Vec.deref] using hcl
        step as ⟨allowed, hallowed⟩
        have hgget : g.val[i.val]! = given := by
          rw [hgiven, getElem!_pos g.val i.val (by omega)]
        have hall : allowed = true ↔ NoConflict c.val i.val d i.val := by
          simpa [alloc.vec.Vec.deref] using hallowed
        split
        · rename_i hcan
          have hcan1 : (g.val[i.val]! = 0#u8 ∨ g.val[i.val]! = d) ∧ NoConflict c.val i.val d i.val := by
            simpa only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ← hgget, hall] using hcan
          step as ⟨old, back, hback⟩
          step as ⟨i1, hi1⟩
          have hset : (back d).val = c.val.set i.val d := by simp_all
          have hv1 : Valid g.val (back d).val i1.val := by
            rw [hset, hi1]
            exact valid_extend hv hi hd1 hd9 hcan1.1 hcan1.2
          have hm1 : (81-i1.val)*10 + (10-(1#u8).val) < m := by simp only [hi1] ; simp at hm ⊢; omega
          have hrec := ih _ hm1 (back d) i1 1#u8 hv1 (by simp) (by simp) rfl
          step as ⟨b1, c1, hr⟩
          split
          · rename_i hb1
            have hp : SearchPost g.val (c.val.set i.val d) (i.val+1) 1 true c1.val := by
              simpa [hset, hi1, hb1] using hr
            exact (WP.spec_ok _).mpr (found_post hcl hi hd1 hp)
          · rename_i hb1
            have hfalse : b1 = false := by simp_all
            have hr0 : SearchPost g.val (c.val.set i.val d) (i.val+1) 1 false c1.val := by
              simpa [hset, hi1, hfalse] using hr
            have hpref : PrefixEq c.val c1.val i.val :=
              prefix_trans (prefix_set c.val i.val d (by omega)) (fun k hk => hr0.2.1 k (by omega))
            have hv2 := valid_prefix hv hr0.1 hpref
            step as ⟨d1, hdnext⟩
            have hm2 : (81-i.val)*10 + (10-d1.val) < m := by omega
            have hrec2 := ih _ hm2 c1 i d1 hv2 (by omega) (by omega) rfl
            apply Aeneas.Std.WP.spec_mono hrec2
            intro r hr2
            apply skip_post hcl hi hd1 hpref hr0.2.2
            simpa [hdnext] using hr2
        · rename_i hcan
          have hno : ¬ ((g.val[i.val]! = 0#u8 ∨ g.val[i.val]! = d) ∧ NoConflict c.val i.val d i.val) := by
            simpa only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ← hgget, hall] using hcan
          step as ⟨d1, hdnext⟩
          have hm2 : (81-i.val)*10 + (10-d1.val) < m := by omega
          have hrec2 := ih _ hm2 c i d1 hv (by omega) (by omega) rfl
          apply Aeneas.Std.WP.spec_mono hrec2
          intro r hr2
          apply skip_post hcl hi hd1 (prefix_refl _ _) (rejected_child hcl hi hd1 hno)
          simpa [hdnext] using hr2


def InitInv (c : alloc.vec.Vec U8) (i : I32) : Prop :=
  0 ≤ i.val ∧ i.val ≤ 81 ∧ (c.val.length : ℤ) = i.val

theorem init_body (c : alloc.vec.Vec U8) (i : I32) (h : InitInv c i) :
    Sudoku.solution.solve_loop.body c i ⦃ r =>
      match r with
      | .done out => out.val.length = 81
      | .cont st => InitInv st.1 st.2 ∧ 81-st.1.val.length < 81-c.val.length ⦄ := by
  have hi0 := h.1
  have hi81 := h.2.1
  have hlen := h.2.2
  unfold Sudoku.solution.solve_loop.body
  step* <;> simp_all [InitInv, IScalar.lt_equiv] <;> omega

@[step] theorem init_code (c : alloc.vec.Vec U8) (i : I32) (h : InitInv c i) :
    Sudoku.solution.solve_loop c i ⦃ out => out.val.length = 81 ⦄ := by
  unfold Sudoku.solution.solve_loop
  apply loop.spec_decr_nat (fun st => 81-st.1.val.length) (fun st => InitInv st.1 st.2)
  · rintro ⟨c1, i1⟩ hi
    apply Aeneas.Std.WP.spec_mono (init_body c1 i1 hi)
    intro r hr; cases r <;> exact hr
  · exact h


theorem prefix_completion {g c h x : List U8} {i d : ℤ}
    (hc : completion_spec g c) (hi : 0 ≤ i) (hi81 : i < 81)
    (hd : 1 ≤ d) (hzero : ((g[i.toNat]!).val : ℤ) = 0)
    (hp : prefixthen_spec g c i d h) (hx : completion_spec h x) :
    completion_spec g x ∧ PrefixEq c x i.toNat ∧ ((x[i.toNat]!).val : ℤ) = d := by
  have hbefore : ∀ j : ℤ, 0 ≤ j → j < i → x[j.toNat]! = c[j.toNat]! := by
    intro j hj hji
    have hcj := (hc.2.2.1 j hj (by omega)).1.1
    have hh := hp.2.2.1 j hj hji
    have hne : ((h[j.toNat]!).val : ℤ) ≠ 0 := by rw [hh]; omega
    exact ((hx.2.2.1 j hj (by omega)).2 hne).trans hh
  have hat : x[i.toNat]! = h[i.toNat]! := by
    apply (hx.2.2.1 i hi hi81).2
    rw [hp.2.2.2.1]; omega
  refine ⟨?_, ?_, by rw [hat, hp.2.2.2.1]⟩
  · refine ⟨hc.1, hx.2.1, ?_, hx.2.2.2⟩
    intro j hj hj81
    refine ⟨(hx.2.2.1 j hj hj81).1, ?_⟩
    intro hgj
    by_cases hji : j < i
    · exact (hbefore j hj hji).trans ((hc.2.2.1 j hj hj81).2 hgj)
    · have hijn : j ≠ i := by intro he; subst j; exact hgj hzero
      have hh := hp.2.2.2.2 j (by omega) hj81
      have hne : ((h[j.toNat]!).val : ℤ) ≠ 0 := by simpa [hh] using hgj
      exact ((hx.2.2.1 j hj hj81).2 hne).trans hh
  · intro k hk
    have he := hbefore k (by omega) (by omega)
    simpa using he.symm

theorem prefix_witness {g c : List U8} {i d : ℤ}
    (hg : g.length = 81) (hc : c.length = 81)
    (hi : 0 ≤ i) (hi81 : i < 81) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    ∃ h, prefixthen_spec g c i d h := by
  let digit : U8 := UScalar.ofNatCore d.toNat (by norm_num; omega)
  have hdigit : (digit.val : ℤ) = d := by simp [digit]; omega
  let f : Fin 81 → U8 := fun k =>
    if (k.val : ℤ) < i then c[k.val]! else if (k.val : ℤ) = i then digit else g[k.val]!
  refine ⟨List.ofFn f, ?_⟩
  refine ⟨⟨⟨⟨by exact_mod_cast hg, by exact_mod_cast hc⟩, hi⟩, hi81⟩, by simp, ?_, ?_, ?_⟩
  · intro j hj hji
    rw [List.getElem!_ofFn f j.toNat (by omega)]
    simp [f, Int.toNat_of_nonneg hj, hji]
  · rw [List.getElem!_ofFn f i.toNat (by omega)]
    simpa [f, Int.toNat_of_nonneg hi] using hdigit
  · intro j hji hj81
    have hj : 0 ≤ j := by omega
    rw [List.getElem!_ofFn f j.toNat (by omega)]
    simp [f, Int.toNat_of_nonneg hj, show ¬ j < i by omega, show j ≠ i by omega]

theorem least_solve_spec {g c : List U8} (hc : completion_spec g c)
    (hm : ∀ x, completion_spec g x → LexLE c x) : solve_spec g (some c) := by
  refine ⟨hc.1, ?_, ?_⟩
  · intro _
    refine ⟨rfl, hc, ?_⟩
    intro i hi hi81 hzero d hd1 hdlt
    simp only [Option.get!_some] at hdlt
    rintro ⟨h, hp, _, x, hx⟩
    obtain ⟨hxg, hpx, hdx⟩ := prefix_completion hc hi hi81 hd1 hzero hp hx
    have hh := hm x hxg i.toNat (by omega) hpx
    omega
  · intro hno
    exact False.elim (hno ⟨hc.1, c, hc⟩)

end Sudoku.Proofs




