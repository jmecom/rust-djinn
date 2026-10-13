import Gzip.Proofs.Matches
import Gzip.Proofs.Cells

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Matches

namespace Gzip.Proofs.Plans

def widen (x : U16) : Usize := UScalar.cast .Usize x

@[simp] theorem widen_val (x : U16) : (widen x).val = x.val := by
  unfold widen
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]

theorem widen_cast (x : Usize) (hx : x.val < 65536) :
    widen (UScalar.cast .U16 x) = x := by
  apply (UScalar.eq_equiv _ _).mpr
  rw [widen_val, UScalar.cast_val_eq]
  simpa only [UScalarTy.numBits, Nat.reducePow] using Nat.mod_eq_of_lt hx

theorem narrow_val (x : Usize) (hx : x.val < 65536) :
    (UScalar.cast .U16 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  simpa only [UScalarTy.numBits, Nat.reducePow] using Nat.mod_eq_of_lt hx

def Step {ty : UScalarTy} (data : List U8) (p stop : ℕ) (length distance : UScalar ty) : Prop :=
  (length.val = 1 ∧ distance.val = 0) ∨
    (ValidMatch data p stop length.val distance.val ∧ 0 < distance.val)

/-- A token as numbers: a literal, or a verified copy. -/
def StepN (data : List U8) (p stop l d : ℕ) : Prop :=
  (l = 1 ∧ d = 0) ∨ (ValidMatch data p stop l d ∧ 0 < d)

theorem step_of_nat {ty : UScalarTy} {data : List U8} {p stop : ℕ} {length distance : UScalar ty}
    {l d : ℕ} (h : StepN data p stop l d) (hl : length.val = l) (hd : distance.val = d) :
    Step data p stop length distance := by
  unfold Step
  unfold StepN at h
  rw [hl, hd]
  exact h

theorem stepN_positive {data : List U8} {p stop l d : ℕ} (h : StepN data p stop l d) : 0 < l := by
  rcases h with h | ⟨h, hd⟩
  · omega
  · rcases h with h | h
    · omega
    · omega

theorem step_positive {ty : UScalarTy} {data : List U8} {p stop : ℕ} {length distance : UScalar ty}
    (h : Step data p stop length distance) : 0 < length.val := by
  rcases h with h | ⟨h, hd⟩
  · omega
  · rcases h with h | h
    · omega
    · omega

theorem step_of_vals {ty ty' : UScalarTy} {data : List U8} {p stop : ℕ}
    {length distance : UScalar ty} {length' distance' : UScalar ty'}
    (h : Step data p stop length distance)
    (hl : length'.val = length.val) (hd : distance'.val = distance.val) :
    Step data p stop length' distance' := by
  simpa only [Step, hl, hd] using h

theorem step_narrow {data : List U8} {p stop : ℕ} {length distance : Usize}
    (h : Step data p stop length distance) :
    Step data p stop (UScalar.cast .U16 length) (UScalar.cast .U16 distance) := by
  have hb : length.val < 65536 ∧ distance.val < 65536 := by
    rcases h with h | ⟨h, hd⟩
    · omega
    · rcases h with h | h
      · omega
      · omega
  apply step_of_vals h
  · rw [UScalar.cast_val_eq]
    simpa only [UScalarTy.numBits, Nat.reducePow] using Nat.mod_eq_of_lt hb.1
  · rw [UScalar.cast_val_eq]
    simpa only [UScalarTy.numBits, Nat.reducePow] using Nat.mod_eq_of_lt hb.2

theorem step_widen {data : List U8} {p stop : ℕ} {length distance : U16}
    (h : Step data p stop length distance) :
    Step data p stop (widen length) (widen distance) :=
  step_of_vals h (widen_val length) (widen_val distance)

inductive Runs (data : List U8) (stop : ℕ) : ℕ → ℕ → List U16 → List U16 → Prop
  | finish (p : ℕ) : Runs data stop p p [] []
  | next (p endpoint : ℕ) (length distance : U16) (ls ds : List U16)
      (valid : Step data p stop length distance)
      (tail : Runs data stop (p + length.val) endpoint ls ds) :
      Runs data stop p endpoint (length :: ls) (distance :: ds)

theorem runs_bound {data : List U8} {stop p q : ℕ} {ls ds : List U16}
    (h : Runs data stop p q ls ds) : p ≤ q := by
  induction h with
  | finish => exact Nat.le_refl _
  | next p q length distance ls ds hv ht ih => omega

theorem runs_lengths {data : List U8} {stop p q : ℕ} {ls ds : List U16}
    (h : Runs data stop p q ls ds) : ls.length = ds.length ∧ ls.length ≤ q - p := by
  induction h with
  | finish => simp
  | next p q length distance ls ds hv ht ih =>
      have hp := step_positive hv
      have hbound := runs_bound ht
      simp only [List.length_cons]
      exact ⟨by omega, by omega⟩

theorem runs_append {data : List U8} {stop p q : ℕ} {ls ds : List U16}
    (h : Runs data stop p q ls ds) (length distance : U16)
    (hs : Step data q stop length distance) :
    Runs data stop p (q + length.val) (ls ++ [length]) (ds ++ [distance]) := by
  induction h with
  | finish q => exact Runs.next q _ _ _ [] [] hs (Runs.finish _)
  | next p q l d ls ds hv ht ih =>
      exact Runs.next p _ l d _ _ hv (ih hs)

/-- A run of tokens stays valid under a later match bound. -/
theorem runs_mono {data : List U8} {stop stop' p q : ℕ} {ls ds : List U16}
    (h : Runs data stop p q ls ds) (hs : stop ≤ stop') : Runs data stop' p q ls ds := by
  induction h with
  | finish p => exact Runs.finish p
  | next p q l d ls ds hv ht ih =>
      refine Runs.next p q l d ls ds ?_ ih
      rcases hv with hl | ⟨hm, hd⟩
      · exact Or.inl hl
      · right
        refine ⟨?_, hd⟩
        rcases hm with hm | hm
        · exact Or.inl hm
        · exact Or.inr ⟨hm.1, hm.2.1, by omega, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1, hm.2.2.2.2.2.2⟩

/-- Two consecutive runs of tokens make one. -/
theorem runs_concat {data : List U8} {stop p q r : ℕ} {ls ds ls' ds' : List U16}
    (h : Runs data stop p q ls ds) (h' : Runs data stop q r ls' ds') :
    Runs data stop p r (ls ++ ls') (ds ++ ds') := by
  induction h with
  | finish p => simpa using h'
  | next p q l d ls ds hv ht ih =>
      simp only [List.cons_append]
      exact Runs.next p r l d _ _ hv (ih h')

/-- An empty run ends where it starts. -/
theorem runs_nil {data : List U8} {stop p q : ℕ} (h : Runs data stop p q [] []) : p = q := by
  cases h
  rfl

/-- Every cell of a finished row but the first records a valid last token ending at its
position. -/
def Predecessors (data : List U8) (start stop : ℕ) (dp : List U64) : Prop :=
  ∀ j, 0 < j → j < dp.length →
    Cells.len dp[j]! ≤ j ∧
    StepN data (start + (j - Cells.len dp[j]!)) stop (Cells.len dp[j]!) (Cells.dist dp[j]!)

theorem trace_body (data : List U8) (start stop size : ℕ)
    (dp : alloc.vec.Vec U64) (v d : alloc.vec.Vec U16) (i : Usize)
    (hsize : size ≤ 32768) (hlens : dp.val.length = size + 1)
    (hpred : Predecessors data start stop dp.val)
    (hi : i.val ≤ size) (hspace : v.val.length + i.val ≤ size)
    (hds : d.val.length = v.val.length)
    (hrun : Runs data stop (start + i.val) stop v.val.reverse d.val.reverse) :
    trace_loop0.body dp v d i ⦃ r =>
      match r with
      | .done (v', d') => Runs data stop start stop v'.val.reverse d'.val.reverse
      | .cont (v', d', j) => j.val < i.val ∧ j.val ≤ size ∧
          v'.val.length + j.val ≤ size ∧ d'.val.length = v'.val.length ∧
          Runs data stop (start + j.val) stop v'.val.reverse d'.val.reverse ⦄ := by
  unfold trace_loop0.body
  split
  · have hip : 0 < i.val := by scalar_tac
    have hil : i.val < dp.val.length := by omega
    obtain ⟨hlen, hstep⟩ := hpred i.val hip hil
    have hpos := stepN_positive hstep
    step as ⟨cell, hcell⟩
    have hcellE : cell = dp.val[i.val]! := by rw [hcell, getElem!_pos dp.val i.val hil]
    step as ⟨len, hlenv⟩
    have hlen' : len.val ≤ i.val := by rw [hlenv, hcellE]; exact hlen
    have hpos' : 0 < len.val := by rw [hlenv, hcellE]; exact hpos
    have hlen16 : len.val < 65536 := by omega
    step as ⟨i1, hi1⟩
    have hi1v : i1.val = len.val := by rw [hi1]; exact narrow_val len hlen16
    step as ⟨v2, hv2⟩
    step as ⟨i2, hi2⟩
    have hi2b : i2.val < 65536 := by rw [hi2]; exact Cells.dist_lt cell
    step as ⟨i3, hi3⟩
    have hi3v : i3.val = i2.val := by rw [hi3]; exact narrow_val i2 hi2b
    step as ⟨v3, hv3⟩
    step as ⟨i4, hi4⟩
    try simp only [WP.spec_ok]
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · rw [hv2, List.length_append, List.length_singleton]
      omega
    · simp only [hv3, hv2, List.length_append, List.length_singleton, hds]
    · rw [hv2, hv3, List.reverse_append, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append]
      have hstep' : Step data (start + i4.val) stop i1 i3 := by
        apply step_of_nat (l := Cells.len dp.val[i.val]!) (d := Cells.dist dp.val[i.val]!)
        · have he : start + i4.val = start + (i.val - Cells.len dp.val[i.val]!) := by
            rw [← hcellE, ← hlenv]
            omega
          rw [he]
          exact hstep
        · rw [hi1v, hlenv, hcellE]
        · rw [hi3v, hi2, hcellE]
      apply Runs.next _ _ _ _ _ _ hstep'
      convert hrun using 1
      rw [hi1v]
      omega
  · step*

@[step]
theorem trace_loop (data : List U8) (start stop size : ℕ)
    (dp : alloc.vec.Vec U64) (v d : alloc.vec.Vec U16) (i : Usize)
    (hsize : size ≤ 32768) (hlens : dp.val.length = size + 1)
    (hpred : Predecessors data start stop dp.val)
    (hi : i.val ≤ size) (hspace : v.val.length + i.val ≤ size)
    (hds : d.val.length = v.val.length)
    (hrun : Runs data stop (start + i.val) stop v.val.reverse d.val.reverse) :
    trace_loop0 dp v d i ⦃ r => Runs data stop start stop r.1.val.reverse r.2.val.reverse ⦄ := by
  unfold trace_loop0
  apply loop.spec_decr_nat (fun (_, _, j) => j.val)
    (fun (v', d', j) => j.val ≤ size ∧ v'.val.length + j.val ≤ size ∧
      d'.val.length = v'.val.length ∧ Runs data stop (start + j.val) stop v'.val.reverse d'.val.reverse)
  · rintro ⟨v', d', j⟩ ⟨hj, hspace', hds', hrun'⟩
    refine WP.spec_mono (trace_body data start stop size dp v' d' j
      hsize hlens hpred hj hspace' hds' hrun') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨v'', d'', j'⟩ := state
        obtain ⟨hdecr, hj', hspace'', hds'', hrun''⟩ := hr
        exact ⟨⟨hj', hspace'', hds'', hrun''⟩, hdecr⟩
  · exact ⟨hi, hspace, hds, hrun⟩

end Gzip.Proofs.Plans
