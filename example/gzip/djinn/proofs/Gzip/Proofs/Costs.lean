import Aeneas
import Gzip.Code.Funs
import Mathlib.Tactic.IntervalCases

open Aeneas Std Result
open Gzip.solution

namespace Gzip.Proofs.Costs

theorem length_extra_bound (i : ℕ) (hi : i < 29) : (LENGTH_EXTRA.val[i]!).val ≤ 5 := by
  interval_cases i <;> simp [LENGTH_EXTRA, Array.make]

theorem distance_extra_bound (i : ℕ) (hi : i < 30) : (DIST_EXTRA.val[i]!).val ≤ 13 := by
  interval_cases i <;> simp [DIST_EXTRA, Array.make]

end Gzip.Proofs.Costs
