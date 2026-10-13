import Gzip.Spec
import Mathlib.Tactic.Linarith

open Aeneas Std
open Gzip.Spec

namespace Gzip.Proofs.Decode.Decoding

theorem int_step_decreases (n : ℤ) (hp : 0 ≤ n) (hn : n ≠ 0) :
    (n - 1).toNat < n.toNat := by omega

theorem bit_unique (s : List U8) (i x y : ℤ)
    (hx : bit_spec s i x) (hy : bit_spec s i y) : x = y :=
  hx.2.2.trans hy.2.2.symm

theorem field_unique (s : List U8) (i n x y : ℤ)
    (hx : field_spec s i n x) (hy : field_spec s i n y) : x = y := by
  generalize hm : n.toNat = m
  induction m using Nat.strong_induction_on generalizing i n x y with
  | h m ih =>
    rw [field_spec] at hx hy
    have hp := hx.1
    have hxb := hx.2 hp
    have hyb := hy.2 hp
    by_cases hn : n = 0
    · exact (hxb.1 hn).trans (hyb.1 hn).symm
    · obtain ⟨u, hu, hu'⟩ := hxb.2 hn
      obtain ⟨v, hv, hv'⟩ := hyb.2 hn
      obtain ⟨u', hu', he⟩ := hu' hu
      obtain ⟨v', hv', hf⟩ := hv' hv
      have huv := bit_unique _ _ _ _ hu hv
      have hlt : (n - 1).toNat < m := hm ▸ int_step_decreases n hp hn
      have huv' := ih _ hlt _ _ _ _ hu' hv' rfl
      omega

theorem code_unique (s : List U8) (i n x y : ℤ)
    (hx : code_spec s i n x) (hy : code_spec s i n y) : x = y := by
  generalize hm : n.toNat = m
  induction m using Nat.strong_induction_on generalizing n x y with
  | h m ih =>
    rw [code_spec] at hx hy
    have hp := hx.1
    have hxb := hx.2 hp
    have hyb := hy.2 hp
    by_cases hn : n = 0
    · exact (hxb.1 hn).trans (hyb.1 hn).symm
    · obtain ⟨u, hu, u', hu', he⟩ := hxb.2 hn
      obtain ⟨v, hv, v', hv', hf⟩ := hyb.2 hn
      have hlt : (n - 1).toNat < m := hm ▸ int_step_decreases n hp hn
      have huv := ih _ hlt _ _ _ hu hv rfl
      have huv' := bit_unique _ _ _ _ hu' hv'
      omega

theorem code_prefix_bound (s : List U8) (i m n x y : ℤ) (hmn : m ≤ n)
    (hx : code_spec s i m x) (hy : code_spec s i n y) :
    y < (x + 1) * 2 ^ (n - m).toNat := by
  generalize he : n.toNat = k
  induction k using Nat.strong_induction_on generalizing n y with
  | h k ih =>
    by_cases hmn' : m = n
    · subst n
      have hxy := code_unique _ _ _ _ _ hx hy
      simp only [sub_self, Int.toNat_zero, pow_zero, mul_one]
      omega
    · have hm0 : 0 ≤ m := by rw [code_spec] at hx; exact hx.1
      have hn0 : 0 ≤ n := by omega
      have hn : n ≠ 0 := by omega
      have hmn1 : m ≤ n - 1 := by omega
      rw [code_spec] at hy
      obtain ⟨v, hv, b, hb, hy⟩ := (hy.2 hn0).2 hn
      have hlt : (n - 1).toNat < k := he ▸ int_step_decreases n hn0 hn
      have hvb := ih _ hlt _ _ hmn1 hv rfl
      have hb1 : b ≤ 1 := by have hbe := hb.2.2; omega
      have hexp : (n - m).toNat = (n - 1 - m).toNat + 1 := by omega
      rw [hexp, pow_succ]
      nlinarith

theorem shorter_unique (lens : List U8) (k n x y : ℤ)
    (hx : shorter_spec lens k n x) (hy : shorter_spec lens k n y) : x = y := by
  generalize hm : k.toNat = m
  induction m using Nat.strong_induction_on generalizing k x y with
  | h m ih =>
    rw [shorter_spec] at hx hy
    have hp := hx.1
    have hxb := hx.2 hp
    have hyb := hy.2 hp
    by_cases hk : k = 0
    · exact (hxb.1 hk).trans (hyb.1 hk).symm
    · have hlt : (k - 1).toNat < m := hm ▸ int_step_decreases k hp.1 hk
      by_cases hl : (1 : ℤ) ≤ (lens[(k - 1).toNat]!).val ∧ (lens[(k - 1).toNat]!).val < n
      · obtain ⟨u, hu, he⟩ := (hxb.2 hk).1 hl
        obtain ⟨v, hv, hf⟩ := (hyb.2 hk).1 hl
        have huv := ih _ hlt _ _ _ hu hv rfl
        omega
      · exact ih _ hlt _ _ _ ((hxb.2 hk).2 hl) ((hyb.2 hk).2 hl) rfl

theorem earlier_unique (lens : List U8) (k n x y : ℤ)
    (hx : earlier_spec lens k n x) (hy : earlier_spec lens k n y) : x = y := by
  generalize hm : k.toNat = m
  induction m using Nat.strong_induction_on generalizing k x y with
  | h m ih =>
    rw [earlier_spec] at hx hy
    have hp := hx.1
    have hxb := hx.2 hp
    have hyb := hy.2 hp
    by_cases hk : k = 0
    · exact (hxb.1 hk).trans (hyb.1 hk).symm
    · have hlt : (k - 1).toNat < m := hm ▸ int_step_decreases k hp.1 hk
      by_cases hl : (lens[(k - 1).toNat]!).val = n
      · obtain ⟨u, hu, he⟩ := (hxb.2 hk).1 hl
        obtain ⟨v, hv, hf⟩ := (hyb.2 hk).1 hl
        have huv := ih _ hlt _ _ _ hu hv rfl
        omega
      · exact ih _ hlt _ _ _ ((hxb.2 hk).2 hl) ((hyb.2 hk).2 hl) rfl

theorem earlier_mono (lens : List U8) (k j n x y : ℤ) (hkj : k ≤ j)
    (hx : earlier_spec lens k n x) (hy : earlier_spec lens j n y) : x ≤ y := by
  generalize hm : j.toNat = m
  induction m using Nat.strong_induction_on generalizing j y with
  | h m ih =>
    by_cases he : k = j
    · subst j
      exact _root_.le_of_eq (earlier_unique _ _ _ _ _ hx hy)
    · have hk0 : 0 ≤ k := by rw [earlier_spec] at hx; exact hx.1.1
      rw [earlier_spec] at hy
      have hp := hy.1
      have hj : j ≠ 0 := by omega
      have hb := (hy.2 hp).2 hj
      have hlt : (j - 1).toNat < m := hm ▸ int_step_decreases j hp.1 hj
      have hk' : k ≤ j - 1 := by clear hx hy hb; omega
      by_cases hl : (lens[(j - 1).toNat]!).val = n
      · obtain ⟨v, hv, hv'⟩ := hb.1 hl
        have hvx := ih _ hlt _ _ hk' hv rfl
        omega
      · exact ih _ hlt _ _ hk' (hb.2 hl) rfl

theorem earlier_strict (lens : List U8) (k j n x y : ℤ) (hkj : k < j)
    (hl : (lens[k.toNat]!).val = n)
    (hx : earlier_spec lens k n x) (hy : earlier_spec lens j n y) : x < y := by
  have hk := hx
  rw [earlier_spec] at hk
  have hj := hy
  rw [earlier_spec] at hj
  have hs : earlier_spec lens (k + 1) n (x + 1) := by
    rw [earlier_spec]
    have hp : earlier_pre lens (k + 1) n := by unfold earlier_pre at *; omega
    refine ⟨hp, fun _ => ⟨?_, ?_⟩⟩
    · intro hz; have hk0 := hk.1.1; omega
    · intro _
      have hl' : (lens[(k + 1 - 1).toNat]!).val = n := by simpa using hl
      exact ⟨fun _ => ⟨x, by simpa using hx, rfl⟩, fun hn => (hn hl').elim⟩
  have hb := earlier_mono lens (k + 1) j n (x + 1) y (by omega) hs hy
  omega

theorem symbol_unique_equal_lengths (s lens : List U8) (i x y : ℤ)
    (hx : symbol_spec s i lens x) (hy : symbol_spec s i lens y)
    (hlen : (lens[x.toNat]!).val = (lens[y.toNat]!).val) : x = y := by
  obtain ⟨_, hxb, _, a, ha, hca⟩ := hx
  obtain ⟨_, hyb, _, b, hb, hcb⟩ := hy
  rw [← hlen] at hcb
  have hab := code_unique _ _ _ _ _ hca hcb
  obtain ⟨_, _, u, hu, v, hv, he⟩ := ha
  obtain ⟨_, _, u', hu', v', hv', hf⟩ := hb
  rw [← hlen] at hu' hv'
  have huu' := shorter_unique _ _ _ _ _ hu hu'
  have hvv' : v = v' := by omega
  rcases _root_.lt_trichotomy x y with hlt | heq | hgt
  · have hh := earlier_strict lens x y _ v v' hlt rfl hv hv'
    omega
  · exact heq
  · have hlen' : ((lens[y.toNat]!).val : ℤ) = (lens[x.toNat]!).val := by exact_mod_cast hlen.symm
    have hh := earlier_strict lens y x _ v' v hgt hlen' hv' hv
    omega

/- Remaining step for general symbol uniqueness:
   For codeword_spec lens x a and codeword_spec lens y b with lengths m < n,
   establish (a + 1) * 2 ^ (n - m).toNat ≤ b. The sum in shorter at length n
   includes every shorter code and every code of length m, including x.
   This contradicts code_prefix_bound when both symbols read the same bits.
   symbol_unique_equal_lengths already handles m = n; reverse x and y for n < m.
   General symbol uniqueness must then be lifted through lengths, tables,
   symbols, block, blocks, and member before discharging decompress.unambiguous.
-/

theorem decompress_unique_of_member_unique (s : List U8)
    (hm : ∀ x y, member_spec s x → member_spec s y → x = y)
    (x y : Option (List U8)) (hx : decompress_spec s x) (hy : decompress_spec s y) : x = y := by
  have hs : x.isSome = y.isSome := by
    have he : (x.isSome = true) ↔ (y.isSome = true) := hx.2.1.trans hy.2.1.symm
    cases x <;> cases y <;> simp_all
  cases x with
  | none => cases y <;> simp_all
  | some x =>
    cases y with
    | none => simp_all
    | some y =>
      have hmx := hx.2.2 rfl
      have hmy := hy.2.2 rfl
      exact congrArg some (hm x y hmx hmy)

theorem lextra_nonneg {k e : ℤ} (h : lextra_spec k e) : 0 ≤ e := by
  unfold lextra_spec at h
  by_cases hz : k < 8 ∨ k = 28
  · have := h.2.2.1 hz; omega
  · have := h.2.2.2 hz; omega

theorem dextra_nonneg {k e : ℤ} (h : dextra_spec k e) : 0 ≤ e := by
  unfold dextra_spec at h
  by_cases hz : k < 4
  · have := h.2.2.1 hz; omega
  · have := h.2.2.2 hz; omega

end Gzip.Proofs.Decode.Decoding
