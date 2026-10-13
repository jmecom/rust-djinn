import Gzip.Proofs.Header
import Gzip.Proofs.Canon

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Header Gzip.Proofs.Codes

set_option maxHeartbeats 2000000

namespace Gzip.Proofs.Rle

/-- Items so far cover `all` from 0 to `p`: whatever covers the rest completes them. -/
def Prefix (all : List U8) (p : ℕ) (ss es : List Usize) : Prop :=
  ∀ ss' es', Covers all p ss' es' → Covers all 0 (ss ++ ss') (es ++ es')

theorem prefix_nil (all : List U8) : Prefix all 0 [] [] := by
  intro ss' es' h
  simpa using h

theorem prefix_cons {all : List U8} {p q : ℕ} {ss es : List Usize} (h : Prefix all p ss es)
    (sym e : Usize) (hstep : ∀ ss' es', Covers all q ss' es' → Covers all p (sym :: ss') (e :: es')) :
    Prefix all q (ss ++ [sym]) (es ++ [e]) := by
  intro ss' es' hc
  have := h (sym :: ss') (e :: es') (hstep ss' es' hc)
  simpa only [List.append_assoc, List.singleton_append] using this

theorem run_body (all : alloc.vec.Vec U8) (n p : Usize) (v : U8) (r : Usize)
    (hn : n.val = all.val.length) (hsmall : n.val ≤ 1024) (hp : p.val < n.val)
    (hr : 1 ≤ r.val ∧ r.val ≤ 138) (hpr : p.val + r.val ≤ n.val)
    (hrun : ∀ i < r.val, all.val[p.val + i]! = v) :
    rle_loop0_loop0.body all n p v r ⦃ res =>
      match res with
      | .done r' => 1 ≤ r'.val ∧ r'.val ≤ 138 ∧ p.val + r'.val ≤ n.val ∧ ∀ i < r'.val, all.val[p.val + i]! = v
      | .cont r' => r'.val = r.val + 1 ∧ 1 ≤ r'.val ∧ r'.val ≤ 138 ∧ p.val + r'.val ≤ n.val ∧
          ∀ i < r'.val, all.val[p.val + i]! = v ⦄ := by
  unfold rle_loop0_loop0.body
  split
  · rename_i h138
    have h138' : r.val < 138 := by scalar_tac
    step as ⟨i, hi⟩
    split
    · rename_i hin
      have hin' : i.val < all.val.length := by rw [← hn]; scalar_tac
      step as ⟨i1, hi1⟩
      split
      · rename_i heq
        step as ⟨r1, hr1⟩
        try simp only [WP.spec_ok]
        refine ⟨hr1, by omega, by omega, by scalar_tac, ?_⟩
        intro k hk
        by_cases hkr : k < r.val
        · exact hrun k hkr
        · have hkr' : k = r.val := by omega
          rw [hkr']
          have hidx : all.val[p.val + r.val]! = all.val[i.val]! := by rw [hi]
          rw [hidx, getElem!_pos all.val i.val hin', ← hi1]
          exact heq
      · try simp only [WP.spec_ok]
        exact ⟨hr.1, hr.2, hpr, hrun⟩
    · try simp only [WP.spec_ok]
      exact ⟨hr.1, hr.2, hpr, hrun⟩
  · try simp only [WP.spec_ok]
    exact ⟨hr.1, hr.2, hpr, hrun⟩

@[step]
theorem run_loop (all : alloc.vec.Vec U8) (n p : Usize) (v : U8) (r : Usize)
    (hn : n.val = all.val.length) (hsmall : n.val ≤ 1024) (hp : p.val < n.val)
    (hr : 1 ≤ r.val ∧ r.val ≤ 138) (hpr : p.val + r.val ≤ n.val)
    (hrun : ∀ i < r.val, all.val[p.val + i]! = v) :
    rle_loop0_loop0 all n p v r ⦃ r' =>
      1 ≤ r'.val ∧ r'.val ≤ 138 ∧ p.val + r'.val ≤ n.val ∧ ∀ i < r'.val, all.val[p.val + i]! = v ⦄ := by
  unfold rle_loop0_loop0
  apply loop.spec_decr_nat (fun r' => 138 - r'.val)
    (fun r' => (1 ≤ r'.val ∧ r'.val ≤ 138) ∧ p.val + r'.val ≤ n.val ∧ ∀ i < r'.val, all.val[p.val + i]! = v)
  · intro r' ⟨hr', hpr', hrun'⟩
    refine WP.spec_mono (run_body all n p v r' hn hsmall hp hr' hpr' hrun') ?_
    intro res hres
    cases res with
    | done k => exact ⟨hres.1, hres.2.1, hres.2.2.1, hres.2.2.2⟩
    | cont k => exact ⟨⟨⟨hres.2.1, hres.2.2.1⟩, hres.2.2.2.1, hres.2.2.2.2⟩, by omega⟩
  · exact ⟨hr, hpr, hrun⟩

/-- The repeat loop: `p - 1` and everything up to `p + rem` hold the value just emitted. -/
theorem repeat_body (all : List U8) (syms extras : alloc.vec.Vec Usize) (p rem : Usize) (v : U8)
    (hsmall : all.length ≤ 1024) (hp : 1 ≤ p.val) (hpr : p.val + rem.val ≤ all.length)
    (hrun : ∀ k, p.val - 1 ≤ k → k < p.val + rem.val → all[k]! = v)
    (hlen : syms.val.length = extras.val.length) (hcount : syms.val.length ≤ p.val)
    (hpre : Prefix all p.val syms.val extras.val) :
    rle_loop0_loop1.body syms extras p rem ⦃ res =>
      match res with
      | .done (syms', extras', p') => syms'.val.length = extras'.val.length ∧ syms'.val.length ≤ p'.val ∧
          p'.val ≤ all.length ∧ p.val ≤ p'.val ∧ Prefix all p'.val syms'.val extras'.val
      | .cont (syms', extras', p', rem') => rem'.val < rem.val ∧ 1 ≤ p'.val ∧ p.val ≤ p'.val ∧
          p'.val + rem'.val ≤ all.length ∧
          (∀ k, p'.val - 1 ≤ k → k < p'.val + rem'.val → all[k]! = v) ∧
          syms'.val.length = extras'.val.length ∧ syms'.val.length ≤ p'.val ∧
          Prefix all p'.val syms'.val extras'.val ⦄ := by
  unfold rle_loop0_loop1.body
  split
  · rename_i hge
    have hge' : 3 ≤ rem.val := by scalar_tac
    have hcSpec : (if rem > 6#usize then ok 6#usize else ok rem) ⦃ c => 3 ≤ c.val ∧ c.val ≤ 6 ∧ c.val ≤ rem.val ⦄ := by
      split <;> step* <;> scalar_tac
    step as ⟨c, hc3, hc6, hcr⟩
    have hspace : syms.val.length < Usize.max := by scalar_tac
    step as ⟨syms1, hsyms1⟩
    step as ⟨i, hi⟩
    have hspace2 : extras.val.length < Usize.max := by scalar_tac
    step as ⟨extras1, hextras1⟩
    step as ⟨p1, hp1⟩
    step as ⟨rem1, hrem1⟩
    try simp only [WP.spec_ok]
    refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · intro k hk1 hk2
      exact hrun k (by omega) (by omega)
    · simp only [hsyms1, hextras1, List.length_append, List.length_singleton, hlen]
    · rw [hsyms1, List.length_append, List.length_singleton]; omega
    · rw [hsyms1, hextras1, hp1]
      apply prefix_cons hpre 16#usize i
      intro ss' es' hcov
      apply Covers.rep p.val 16#usize i ss' es' (by simp) hp (by scalar_tac) (by scalar_tac)
      · intro k hk1 hk2
        rw [hrun k (by omega) (by scalar_tac), hrun (p.val - 1) (by omega) (by omega)]
      · have : p.val + 3 + i.val = p.val + c.val := by scalar_tac
        rw [this]
        exact hcov
  · try simp only [WP.spec_ok]
    exact ⟨hlen, hcount, by omega, Nat.le_refl _, hpre⟩

@[step]
theorem repeat_loop (all : List U8) (syms extras : alloc.vec.Vec Usize) (p rem : Usize) (v : U8)
    (hsmall : all.length ≤ 1024) (hp : 1 ≤ p.val) (hpr : p.val + rem.val ≤ all.length)
    (hrun : ∀ k, p.val - 1 ≤ k → k < p.val + rem.val → all[k]! = v)
    (hlen : syms.val.length = extras.val.length) (hcount : syms.val.length ≤ p.val)
    (hpre : Prefix all p.val syms.val extras.val) :
    rle_loop0_loop1 syms extras p rem ⦃ r =>
      r.1.val.length = r.2.1.val.length ∧ r.1.val.length ≤ r.2.2.val ∧ r.2.2.val ≤ all.length ∧
      p.val ≤ r.2.2.val ∧ Prefix all r.2.2.val r.1.val r.2.1.val ⦄ := by
  unfold rle_loop0_loop1
  apply loop.spec_decr_nat (fun (_, _, _, rem') => rem'.val)
    (fun (syms', extras', p', rem') => 1 ≤ p'.val ∧ p'.val + rem'.val ≤ all.length ∧
      (∀ k, p'.val - 1 ≤ k → k < p'.val + rem'.val → all[k]! = v) ∧
      syms'.val.length = extras'.val.length ∧ syms'.val.length ≤ p'.val ∧ p.val ≤ p'.val ∧
      Prefix all p'.val syms'.val extras'.val)
  · rintro ⟨syms', extras', p', rem'⟩ ⟨hp', hpr', hrun', hlen', hcount', hpp', hpre'⟩
    refine WP.spec_mono (repeat_body all syms' extras' p' rem' v hsmall hp' hpr' hrun' hlen' hcount' hpre') ?_
    intro res hres
    cases res with
    | done state =>
        obtain ⟨s, e, q⟩ := state
        exact ⟨hres.1, hres.2.1, hres.2.2.1, hpp'.trans hres.2.2.2.1, hres.2.2.2.2⟩
    | cont state =>
        obtain ⟨s, e, q, rm⟩ := state
        obtain ⟨hdec, h1, h1', h2, h3, h4, h5, h6⟩ := hres
        exact ⟨⟨h1, h2, h3, h4, h5, by omega, h6⟩, hdec⟩
  · exact ⟨hp, hpr, hrun, hlen, hcount, Nat.le_refl _, hpre⟩

theorem outer_body (all : alloc.vec.Vec U8) (n : Usize) (syms extras : alloc.vec.Vec Usize) (p : Usize)
    (hn : n.val = all.val.length) (hsmall : n.val ≤ 1024) (hsym : ∀ k < all.val.length, (all.val[k]!).val ≤ 15)
    (hp : p.val ≤ n.val) (hlen : syms.val.length = extras.val.length) (hcount : syms.val.length ≤ p.val)
    (hpre : Prefix all.val p.val syms.val extras.val) :
    rle_loop0.body all n syms extras p ⦃ res =>
      match res with
      | .done (syms', extras') => Covers all.val 0 syms'.val extras'.val ∧ syms'.val.length ≤ all.val.length
      | .cont (syms', extras', p') => p.val < p'.val ∧ p'.val ≤ n.val ∧
          syms'.val.length = extras'.val.length ∧ syms'.val.length ≤ p'.val ∧
          Prefix all.val p'.val syms'.val extras'.val ⦄ := by
  unfold rle_loop0.body
  split
  · rename_i hlt
    have hlt' : p.val < all.val.length := by rw [← hn]; scalar_tac
    step as ⟨v, hv⟩
    have hvget : all.val[p.val]! = v := by rw [hv, getElem!_pos all.val p.val hlt']
    have hrun := run_loop all n p v 1#usize hn hsmall (by scalar_tac) (by simp) (by scalar_tac)
      (by intro i hi; simp at hi; subst hi; simpa using hvget)
    step as ⟨r, hr1, hr138, hpr, hrunv⟩
    have hspace : syms.val.length < Usize.max := by scalar_tac
    have hspace2 : extras.val.length < Usize.max := by scalar_tac
    split
    · rename_i hz
      have hvz : v = 0#u8 := hz
      split
      · rename_i h11
        have h11' : 11 ≤ r.val := by scalar_tac
        step as ⟨syms1, hsyms1⟩
        step as ⟨i, hi⟩
        step as ⟨extras1, hextras1⟩
        step as ⟨p1, hp1⟩
        try simp only [WP.spec_ok]
        refine ⟨by omega, by omega, ?_, ?_, ?_⟩
        · simp only [hsyms1, hextras1, List.length_append, List.length_singleton, hlen]
        · rw [hsyms1, List.length_append, List.length_singleton]; omega
        · rw [hsyms1, hextras1, hp1]
          apply prefix_cons hpre 18#usize i
          intro ss' es' hcov
          apply Covers.zeros2 p.val 18#usize i ss' es' (by simp) (by scalar_tac) (by scalar_tac)
          · intro k hk1 hk2
            have := hrunv (k - p.val) (by scalar_tac)
            rw [show p.val + (k - p.val) = k by omega, hvz] at this
            rw [this]
            rfl
          · have : p.val + 11 + i.val = p.val + r.val := by scalar_tac
            rw [this]
            exact hcov
      · split
        · rename_i h3
          have h3' : 3 ≤ r.val := by scalar_tac
          have h10 : r.val < 11 := by scalar_tac
          step as ⟨syms1, hsyms1⟩
          step as ⟨i, hi⟩
          step as ⟨extras1, hextras1⟩
          step as ⟨p1, hp1⟩
          try simp only [WP.spec_ok]
          refine ⟨by omega, by omega, ?_, ?_, ?_⟩
          · simp only [hsyms1, hextras1, List.length_append, List.length_singleton, hlen]
          · rw [hsyms1, List.length_append, List.length_singleton]; omega
          · rw [hsyms1, hextras1, hp1]
            apply prefix_cons hpre 17#usize i
            intro ss' es' hcov
            apply Covers.zeros p.val 17#usize i ss' es' (by simp) (by scalar_tac) (by scalar_tac)
            · intro k hk1 hk2
              have := hrunv (k - p.val) (by scalar_tac)
              rw [show p.val + (k - p.val) = k by omega, hvz] at this
              rw [this]
              rfl
            · have : p.val + 3 + i.val = p.val + r.val := by scalar_tac
              rw [this]
              exact hcov
        · step as ⟨syms1, hsyms1⟩
          step as ⟨extras1, hextras1⟩
          step as ⟨p1, hp1⟩
          try simp only [WP.spec_ok]
          refine ⟨by omega, by omega, ?_, ?_, ?_⟩
          · simp only [hsyms1, hextras1, List.length_append, List.length_singleton, hlen]
          · rw [hsyms1, List.length_append, List.length_singleton]; omega
          · rw [hsyms1, hextras1, hp1]
            apply prefix_cons hpre 0#usize 0#usize
            intro ss' es' hcov
            apply Covers.lit p.val 0#usize 0#usize ss' es' hlt' (by simp) (by rw [hvget, hvz]; rfl) hcov
    · rename_i hnz
      step as ⟨i, hi⟩
      step as ⟨syms1, hsyms1⟩
      step as ⟨extras1, hextras1⟩
      step as ⟨p1, hp1⟩
      step as ⟨rem, hrem⟩
      have hiv : i.val = v.val := by
        rw [hi, UScalar.cast_val_eq]
        exact Nat.mod_eq_of_lt (by scalar_tac)
      have hpre1 : Prefix all.val p1.val (syms.val ++ [i]) (extras.val ++ [0#usize]) := by
        rw [hp1]
        apply prefix_cons hpre i 0#usize
        intro ss' es' hcov
        apply Covers.lit p.val i 0#usize ss' es' hlt' ?_ (by rw [hvget, hiv]) hcov
        rw [hiv]
        have := hsym p.val hlt'
        rw [hvget] at this
        omega
      have hrep := repeat_loop all.val syms1 extras1 p1 rem v (by omega) (by omega) (by omega)
        (by
          intro k hk1 hk2
          have := hrunv (k - p.val) (by omega)
          rw [show p.val + (k - p.val) = k by omega] at this
          exact this)
        (by simp only [hsyms1, hextras1, List.length_append, List.length_singleton, hlen])
        (by rw [hsyms1, List.length_append, List.length_singleton]; omega)
        (by rw [hsyms1, hextras1]; exact hpre1)
      step as ⟨syms2, extras2, p2, hlen2, hcount2, hp2n, hpp2, hpre2⟩
      try simp only [WP.spec_ok]
      exact ⟨by omega, by omega, hlen2, hcount2, hpre2⟩
  · rename_i hge
    have he : p.val = all.val.length := by rw [← hn]; scalar_tac
    try simp only [WP.spec_ok]
    have := hpre [] [] (by rw [he]; exact Covers.nil)
    exact ⟨by simpa using this, by omega⟩

@[step]
theorem outer_loop (all : alloc.vec.Vec U8) (n : Usize) (syms extras : alloc.vec.Vec Usize) (p : Usize)
    (hn : n.val = all.val.length) (hsmall : n.val ≤ 1024) (hsym : ∀ k < all.val.length, (all.val[k]!).val ≤ 15)
    (hp : p.val ≤ n.val) (hlen : syms.val.length = extras.val.length) (hcount : syms.val.length ≤ p.val)
    (hpre : Prefix all.val p.val syms.val extras.val) :
    rle_loop0 all n syms extras p ⦃ r => Covers all.val 0 r.1.val r.2.val ∧ r.1.val.length ≤ all.val.length ⦄ := by
  unfold rle_loop0
  apply loop.spec_decr_nat (fun (_, _, p') => n.val - p'.val)
    (fun (syms', extras', p') => p'.val ≤ n.val ∧ syms'.val.length = extras'.val.length ∧
      syms'.val.length ≤ p'.val ∧ Prefix all.val p'.val syms'.val extras'.val)
  · rintro ⟨syms', extras', p'⟩ ⟨hp', hlen', hcount', hpre'⟩
    refine WP.spec_mono (outer_body all n syms' extras' p' hn hsmall hsym hp' hlen' hcount' hpre') ?_
    intro res hres
    cases res with
    | done state => exact hres
    | cont state =>
        obtain ⟨s, e, q⟩ := state
        obtain ⟨h1, h2, h3, h4, h5⟩ := hres
        exact ⟨⟨h2, h3, h4, h5⟩, by change n.val - q.val < n.val - p'.val; omega⟩
  · exact ⟨hp, hlen, hcount, hpre⟩

theorem rle_spec (all : alloc.vec.Vec U8) (hsmall : all.val.length ≤ 1024)
    (hsym : ∀ k < all.val.length, (all.val[k]!).val ≤ 15) :
    rle all ⦃ r => Covers all.val 0 r.1.val r.2.val ∧ r.1.val.length ≤ all.val.length ⦄ := by
  unfold rle
  dsimp only
  have hlen : (alloc.vec.Vec.len all).val = all.val.length := by
    simp [alloc.vec.Vec.len_val, alloc.vec.Vec.length]
  exact outer_loop all (alloc.vec.Vec.len all) (alloc.vec.Vec.new Usize) (alloc.vec.Vec.new Usize) 0#usize
    hlen (by rw [hlen]; exact hsmall) hsym (by simp) (by simp [alloc.vec.Vec.new]) (by simp [alloc.vec.Vec.new])
    (by simp [alloc.vec.Vec.new]; exact prefix_nil all.val)

/-! ### The usage check of the code-length code -/

theorem header_body (syms : alloc.vec.Vec Usize) (cl : Code) (cost : Usize) (ok1 : Bool) (i : Usize)
    (hsmall : syms.val.length ≤ 1024) (hi : i.val ≤ syms.val.length) (hcost : cost.val ≤ 262 * i.val)
    (hok : ok1 = true → Usable cl.lens.val (syms.val.take i.val)) :
    header_cost_loop.body syms cl cost ok1 i ⦃ r =>
      match r with
      | .done (cost', ok') => cost'.val ≤ 262 * syms.val.length ∧ (ok' = true → Usable cl.lens.val syms.val)
      | .cont (cost', ok', i') => i'.val = i.val + 1 ∧ i'.val ≤ syms.val.length ∧ cost'.val ≤ 262 * i'.val ∧
          (ok' = true → Usable cl.lens.val (syms.val.take i'.val)) ⦄ := by
  unfold header_cost_loop.body
  dsimp only
  split
  · rename_i hlt
    have hlt' : i.val < syms.val.length := by scalar_tac
    step as ⟨s, hs⟩
    have hsget : s = syms.val[i.val]! := by rw [hs, getElem!_pos syms.val i.val hlt']
    have hpair : (if s < alloc.vec.Vec.len cl.lens then do
          let i3 ← alloc.vec.Vec.index_usize cl.lens s
          let x ← lift (UScalar.cast .Usize i3)
          let ok3 ← if x = 0#usize then ok false else ok ok1
          let extra ← if s = 16#usize then ok 2#usize else
            if s = 17#usize then ok 3#usize else if s = 18#usize then ok 7#usize else ok 0#usize
          let i4 ← x + extra
          let cost2 ← cost + i4
          ok (cost2, ok3)
        else ok (cost, false)) ⦃ r => r.1.val ≤ cost.val + 262 ∧
          (r.2 = true → ok1 = true ∧ s.val < cl.lens.val.length ∧ 1 ≤ (cl.lens.val[s.val]!).val) ⦄ := by
      split
      · rename_i hsl
        have hsl' : s.val < cl.lens.val.length := by
          have := (UScalar.lt_equiv _ _).mp hsl
          simpa [alloc.vec.Vec.len_val, alloc.vec.Vec.length] using this
        step as ⟨i3, hi3⟩
        step as ⟨x, hx⟩
        have hxv : x.val = (cl.lens.val[s.val]!).val := by
          rw [hx, UScalar.cast_val_eq, hi3, getElem!_pos cl.lens.val s.val hsl']
          exact Nat.mod_eq_of_lt (by scalar_tac)
        have hok3Spec : (if x = 0#usize then ok false else ok ok1) ⦃ ok3 =>
            ok3 = true → ok1 = true ∧ 1 ≤ x.val ⦄ := by
          split
          · simp
          · rename_i hx0
            have : 1 ≤ x.val := by scalar_tac
            simp only [WP.spec_ok]
            exact fun h => ⟨h, this⟩
        step as ⟨ok3, hok3⟩
        have hextraSpec : (if s = 16#usize then ok 2#usize else
            if s = 17#usize then ok 3#usize else if s = 18#usize then ok 7#usize else ok 0#usize) ⦃ e =>
            e.val ≤ 7 ⦄ := by
          split
          · simp
          · split
            · simp
            · split <;> simp
        step as ⟨extra, hextra⟩
        have hxb : x.val ≤ 255 := by rw [hxv]; scalar_tac
        step as ⟨i4, hi4⟩
        step as ⟨cost2, hcost2⟩
        try simp only [WP.spec_ok]
        refine ⟨by omega, ?_⟩
        intro h3
        obtain ⟨h1, h2⟩ := hok3 h3
        exact ⟨h1, hsl', by rw [← hxv]; exact h2⟩
      · try simp only [WP.spec_ok]
        exact ⟨by omega, fun h => by simp at h⟩
    step as ⟨cost1, ok2, hcost1, hok2⟩
    step as ⟨i1, hi1⟩
    try simp only [WP.spec_ok]
    refine ⟨hi1, by scalar_tac, by omega, ?_⟩
    intro h2
    obtain ⟨h1, hsl, hpos⟩ := hok2 h2
    have hprev := hok h1
    intro x hx
    rw [hi1, List.take_succ_eq_append_getElem hlt'] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hprev x hx
    · have hxe : x = syms.val[i.val] := List.mem_singleton.mp hx
      rw [hxe, ← getElem!_pos syms.val i.val hlt', ← hsget]
      exact ⟨hsl, hpos⟩
  · rename_i hge
    have he : i.val = syms.val.length := by scalar_tac
    try simp only [WP.spec_ok]
    refine ⟨by rw [← he]; exact hcost, ?_⟩
    intro h
    have := hok h
    rw [he, List.take_length] at this
    exact this

@[step]
theorem header_loop (syms : alloc.vec.Vec Usize) (cl : Code) (cost : Usize) (ok1 : Bool) (i : Usize)
    (hsmall : syms.val.length ≤ 1024) (hi : i.val ≤ syms.val.length) (hcost : cost.val ≤ 262 * i.val)
    (hok : ok1 = true → Usable cl.lens.val (syms.val.take i.val)) :
    header_cost_loop syms cl cost ok1 i ⦃ r => r.1.val ≤ 262 * syms.val.length ∧
      (r.2 = true → Usable cl.lens.val syms.val) ⦄ := by
  unfold header_cost_loop
  apply loop.spec_decr_nat (fun (_, _, i') => syms.val.length - i'.val)
    (fun (cost', ok', i') => i'.val ≤ syms.val.length ∧ cost'.val ≤ 262 * i'.val ∧
      (ok' = true → Usable cl.lens.val (syms.val.take i'.val)))
  · rintro ⟨cost', ok', i'⟩ ⟨hi', hcost', hok'⟩
    refine WP.spec_mono (header_body syms cl cost' ok' i' hsmall hi' hcost' hok') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨c, o, j⟩ := state
        obtain ⟨h1, h2, h3, h4⟩ := hr
        exact ⟨⟨h2, h3, h4⟩, by change syms.val.length - j.val < syms.val.length - i'.val; omega⟩
  · exact ⟨hi, hcost, hok⟩

theorem header_cost_spec (syms : alloc.vec.Vec Usize) (cl : Code) (hsmall : syms.val.length ≤ 1024) :
    header_cost syms cl ⦃ r => r.1.val ≤ 262 * syms.val.length ∧ (r.2 = true → Usable cl.lens.val syms.val) ⦄ := by
  unfold header_cost
  exact header_loop syms cl 0#usize true 0#usize hsmall (by simp) (by simp)
    (by intro _ x hx; simp at hx)

end Gzip.Proofs.Rle
