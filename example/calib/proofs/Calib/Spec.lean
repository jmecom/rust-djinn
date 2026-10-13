/-  Spec.lean — what `cargo djinn translate` would emit for example/sort/src/spec.rs.
    TRUSTED. Hand-written here for the calibration experiment. -/
import Aeneas

open Aeneas Std

namespace Calib.Spec

/-! ## rel perm(list: &[i32]) -> t: Vec<i32>  [total]
      t.len() == list.len();
      for x in list { t.iter().filter(|y| y == x).count() == list.iter().filter(|y| y == x).count() }
      for x in t    { t.iter().filter(|y| y == x).count() == list.iter().filter(|y| y == x).count() } -/

def perm_pre (list : List I32) : Prop :=
  True

def perm_spec (list : List I32) (t : List I32) : Prop :=
  perm_pre list ∧
  ((t.length : ℤ) = (list.length : ℤ)) ∧
  (∀ x, x ∈ list → (List.count x t : ℤ) = (List.count x list : ℤ)) ∧
  (∀ x, x ∈ t → (List.count x t : ℤ) = (List.count x list : ℤ))

/-! ## func sort(v: &mut Vec<i32>)   outputs: v
      perm(old(v)) == v;
      for i in 0..v.len() - 1 { v[i] <= v[i + 1] } -/

def sort_pre (v_old : List I32) : Prop :=
  True

def sort_spec (v_old : List I32) (v : List I32) : Prop :=
  sort_pre v_old ∧
  perm_spec v_old v ∧
  (∀ i : ℤ, 0 ≤ i → i < (v.length : ℤ) - 1 →
     (v[i.toNat]!).val ≤ (v[(i + 1).toNat]!).val)

/-! ## func max(list: &[i32]) -> r: i32
      requires list.len() >= 1
      ensures r in list
      r in list;
      for x in list { x <= r } -/

def max_pre (list : List I32) : Prop :=
  (list.length : ℤ) ≥ 1

def max_spec (list : List I32) (r : I32) : Prop :=
  max_pre list ∧
  (r ∈ list) ∧
  (∀ x, x ∈ list → x.val ≤ r.val)

end Calib.Spec
