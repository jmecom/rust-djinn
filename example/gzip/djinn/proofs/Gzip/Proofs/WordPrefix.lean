import Gzip.Proofs.CrcImpl

open Aeneas Std

namespace Gzip.Proofs.WordPrefix

def prefixValue (a b : ℕ) : ℕ :=
  (if a % 256 = b % 256 then 1 else 0) +
  (if a % 65536 = b % 65536 then 1 else 0) +
  (if a % 16777216 = b % 16777216 then 1 else 0)

theorem prefixValue_le (a b : ℕ) : prefixValue a b ≤ 3 := by
  unfold prefixValue
  split_ifs <;> omega

theorem prefix_bytes (a0 a1 a2 a3 b0 b1 b2 b3 : U8) :
    let a := a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
    let b := b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
    (0 < prefixValue a b → a0 = b0) ∧
    (1 < prefixValue a b → a1 = b1) ∧
    (2 < prefixValue a b → a2 = b2) := by
  have ha0 : a0.val < 256 := by scalar_tac
  have ha1 : a1.val < 256 := by scalar_tac
  have ha2 : a2.val < 256 := by scalar_tac
  have ha3 : a3.val < 256 := by scalar_tac
  have hb0 : b0.val < 256 := by scalar_tac
  have hb1 : b1.val < 256 := by scalar_tac
  have hb2 : b2.val < 256 := by scalar_tac
  have hb3 : b3.val < 256 := by scalar_tac
  dsimp only
  unfold prefixValue
  split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;>
    intro h <;> apply (UScalar.eq_equiv _ _).mpr <;> omega

end Gzip.Proofs.WordPrefix
