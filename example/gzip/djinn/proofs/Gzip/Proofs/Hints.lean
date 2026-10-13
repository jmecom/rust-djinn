import Gzip.Proofs.Matches

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Matches

/-! Casts between `usize` and `u64` used by the packed words of the optimal parser (its cells
and the edges a recording pass keeps for the later passes, `Edges`). -/

namespace Gzip.Proofs.Hints

/-- A `usize` fits in a `u64`. -/
theorem cast_u64 (x : Usize) : (UScalar.cast .U64 x).val = x.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]

/-- A small `u64` fits in a `usize`. -/
theorem cast_usize (x : U64) (hx : x.val < 4294967296) : (UScalar.cast .Usize x).val = x.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h] <;> omega

end Gzip.Proofs.Hints
