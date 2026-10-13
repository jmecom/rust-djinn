import Gzip.Proofs.Tokens
import Gzip.Proofs.Chains

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Plans Gzip.Proofs.Matches

set_option maxHeartbeats 2000000

namespace Gzip.Proofs.Histogram

theorem bound_set {v : List Usize} {b : ℕ} (hv : ∀ i < v.length, (v[i]!).val ≤ b) (j : ℕ) (x : Usize)
    (hx : x.val ≤ b + 1) : ∀ i < (v.set j x).length, ((v.set j x)[i]!).val ≤ b + 1 := by
  intro i hi
  have hi' : i < v.length := by simpa using hi
  rw [Djinn.Vocab.getElem!_set v j i x hi']
  split
  · exact hx
  · exact Nat.le_succ_of_le (hv i hi')

end Gzip.Proofs.Histogram
