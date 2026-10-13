import Gzip.Proofs.Rle
import Gzip.Proofs.Symbolize
import Gzip.Proofs.Tokens

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Plans Gzip.Proofs.Matches

set_option maxHeartbeats 2000000

namespace Gzip.Proofs.Body

/-- The position of token `t`: the start plus the lengths of the tokens before it. -/
def pos (ls : List U16) (start t : ℕ) : ℕ := start + ((ls.take t).map (fun x => x.val)).sum

@[simp] theorem pos_zero (ls : List U16) (start : ℕ) : pos ls start 0 = start := by
  simp [pos]

theorem pos_succ (ls : List U16) (start t : ℕ) (ht : t < ls.length) :
    pos ls start (t + 1) = pos ls start t + (ls[t]!).val := by
  simp only [pos, List.take_succ_eq_append_getElem ht, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, getElem!_pos ls t ht]
  omega

/-- Token `t` only uses symbols the codes have codewords for. -/
def UsableAt (data : List U8) (start : ℕ) (ls ds : List U16) (lsym dsym : List U8) (lit dist : List U8) (t : ℕ) : Prop :=
  if (ds[t]!).val = 0 then
    (data[pos ls start t]!).val < lit.length ∧ 1 ≤ (lit[(data[pos ls start t]!).val]!).val
  else
    257 + (lsym[t]!).val < lit.length ∧ 1 ≤ (lit[257 + (lsym[t]!).val]!).val ∧
    (dsym[t]!).val < dist.length ∧ 1 ≤ (dist[(dsym[t]!).val]!).val

def Usable (data : List U8) (start : ℕ) (ls ds : List U16) (lsym dsym : List U8) (lit dist : List U8) : Prop :=
  (∀ t < ls.length, UsableAt data start ls ds lsym dsym lit dist t) ∧
  256 < lit.length ∧ 1 ≤ (lit[256]!).val

end Gzip.Proofs.Body
