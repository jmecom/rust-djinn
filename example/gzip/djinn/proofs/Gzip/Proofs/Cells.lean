import Gzip.Proofs.Hints

open Aeneas Std Result
open Gzip.solution

/-! The optimal parser's row: one cell per position, holding the bits of the cheapest path to
it above bit 32, and the length (bits 16 to 31) and distance (the low 16 bits) of that path's
last token. -/

namespace Gzip.Proofs.Cells

/-- The bits of a cell's path. -/
def cost (c : U64) : ℕ := c.val / 4294967296

/-- The length of a cell's last token. -/
def len (c : U64) : ℕ := c.val % 4294967296 / 65536

/-- The distance of a cell's last token (0 for a literal). -/
def dist (c : U64) : ℕ := c.val % 65536

/-- The fields of a packed cell. -/
theorem fields (c l d : ℕ) (hc : c < 4294967296) (hl : l < 65536) (hd : d < 65536) :
    (c * 4294967296 + l * 65536 + d) / 4294967296 = c ∧
    (c * 4294967296 + l * 65536 + d) % 4294967296 / 65536 = l ∧
    (c * 4294967296 + l * 65536 + d) % 65536 = d := by
  omega

/-- A `u32` fits in a `u64`. -/
theorem cast_u32_u64 (x : U32) : (UScalar.cast .U64 x).val = x.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  simp [UScalarTy.numBits]

@[step]
theorem cell_cost_spec (c : U64) : cell_cost c ⦃ r => r.val = cost c ⦄ := by
  unfold cell_cost cost
  step*

@[step]
theorem cell_length_spec (c : U64) : cell_length c ⦃ r => r.val = len c ⦄ := by
  unfold cell_length len
  have hxb : c.val < 18446744073709551616 := by scalar_tac
  step*
  rw [Hints.cast_usize _ (by rw [i1_post, i_post]; omega), i1_post, i_post]

@[step]
theorem cell_distance_spec (c : U64) : cell_distance c ⦃ r => r.val = dist c ⦄ := by
  unfold cell_distance dist
  have hxb : c.val < 18446744073709551616 := by scalar_tac
  step*
  rw [Hints.cast_usize _ (by rw [i_post]; omega), i_post]

theorem probe_spec (c : U64) (hc : c.val < 4294967296) :
    probe c ⦃ r => r.val = c.val * 4294967296 + 4294967295 ⦄ := by
  unfold probe
  step*

/-- The length of a cell is below 2^16. -/
theorem len_lt (c : U64) : len c < 65536 := by
  unfold len
  omega

/-- The distance of a cell is below 2^16. -/
theorem dist_lt (c : U64) : dist c < 65536 := by
  unfold dist
  omega

end Gzip.Proofs.Cells
