import Gzip.Spec

open Aeneas Std
open Gzip.Spec

namespace Gzip.SpecCounterexample

/-- The current specification excludes the old negative-index counterexample. -/
theorem flag_negative_index_rejected : ¬ flag_spec 0 (-1) false := by
  norm_num [flag_spec, flag_pre]

/-- The current pinned flag obligation follows from its explicit precondition. -/
theorem flag_wf_valid :
    ∀ (f : ℤ) (k : ℤ) (b : Bool),
      flag_spec f k b →
      (0 ≤ k) ∧ ((2 ^ k.toNat) ≠ 0) ∧ (2 ≠ 0) := by
  intro f k b h
  exact ⟨h.1, pow_ne_zero _ (by decide), by decide⟩

end Gzip.SpecCounterexample
