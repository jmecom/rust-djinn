import Gzip.Proofs.Plans

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Plans

/-! The edges the first optimal pass records for the later passes, each packed into one word:
the index of its position in the block (from bit 48), the index of its price (bits 32 to 47:
any value, the later pass checks it against its price table at run time) and the low half of
the cell it offers (the token's length from bit 16, its distance). The later passes read them
in order and price them without comparing again, so the invariant carries the verification:
the token of every edge is valid at its position. -/

namespace Gzip.Proofs.Edges

/-- The index in the block of an edge's position. -/
def index (x : U64) : ℕ := x.val / 281474976710656

/-- The low half of the cell an edge offers. -/
def low (x : U64) : ℕ := x.val % 4294967296

/-- A recorded edge: its token (length `low / 65536`, distance `low % 65536`) is valid at the
position `start + index x`. -/
def EdgeOk (data : List U8) (start stop : ℕ) (x : U64) : Prop :=
  StepN data (start + index x) stop (low x / 65536) (low x % 65536)

/-- Every recorded edge is valid. -/
def Edges (data : List U8) (start stop : ℕ) (edges : List U64) : Prop :=
  ∀ k < edges.length, EdgeOk data start stop edges[k]!

theorem empty (data : List U8) (start stop : ℕ) : Edges data start stop [] := by
  intro k hk
  simp at hk

/-- A valid edge joins the edges. -/
theorem push {data : List U8} {start stop : ℕ} {edges : List U64}
    (h : Edges data start stop edges) (x : U64) (hx : EdgeOk data start stop x) :
    Edges data start stop (edges ++ [x]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  by_cases hkl : k < edges.length
  · rw [List.getElem!_append_left edges [x] k hkl]
    exact h k hkl
  · have he : k = edges.length := by omega
    subst he
    rw [List.getElem!_append_right edges [x] edges.length (Nat.le_refl _)]
    simpa using hx

/-- What a later pass reads: a valid edge. -/
theorem lookup {data : List U8} {start stop : ℕ} {edges : List U64}
    (h : Edges data start stop edges) (k : ℕ) (hk : k < edges.length) :
    EdgeOk data start stop edges[k]! := h k hk

/-- The fields of a packed edge. -/
theorem fields (i c l d : ℕ) (hi : i < 65536) (hc : c < 65536) (hl : l < 65536) (hd : d < 65536) :
    (i * 281474976710656 + c * 4294967296 + l * 65536 + d) / 281474976710656 = i ∧
    (i * 281474976710656 + c * 4294967296 + l * 65536 + d) % 4294967296 / 65536 = l ∧
    (i * 281474976710656 + c * 4294967296 + l * 65536 + d) % 4294967296 % 65536 = d := by
  omega

/-- An edge whose token is valid at its position. -/
theorem edge_ok {data : List U8} {start stop : ℕ} (x : U64) (i c l d : ℕ)
    (hi : i < 65536) (hc : c < 65536) (hl : l < 65536) (hd : d < 65536)
    (hx : x.val = i * 281474976710656 + c * 4294967296 + l * 65536 + d)
    (hv : StepN data (start + i) stop l d) : EdgeOk data start stop x := by
  unfold EdgeOk index low
  rw [hx]
  have hf := fields i c l d hi hc hl hd
  rw [hf.1, hf.2.1, hf.2.2]
  exact hv

/-- The edge of a literal. -/
theorem literal_ok {data : List U8} {start stop : ℕ} (x : U64) (i b : ℕ)
    (hi : i < 65536) (hb : b < 65536)
    (hx : x.val = i * 281474976710656 + b * 4294967296 + 65536) : EdgeOk data start stop x :=
  edge_ok x i b 1 0 hi hb (by omega) (by omega) (by omega) (Or.inl ⟨rfl, rfl⟩)

/-- The index of any edge is below 2^16. -/
theorem index_lt (x : U64) : index x < 65536 := by
  unfold index
  have hxb : x.val < 18446744073709551616 := by scalar_tac
  omega

/-- The low half of any edge is below 2^32. -/
theorem low_lt (x : U64) : low x < 4294967296 := by
  unfold low
  omega

end Gzip.Proofs.Edges
