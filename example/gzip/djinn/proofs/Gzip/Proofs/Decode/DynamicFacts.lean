import Gzip.Proofs.Decode.SliceImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.RoundTrip Gzip.Proofs.Decode.ClImpl

namespace Gzip.Proofs.Decode.DynamicFacts

theorem field_exists (s : List U8) (i : ℤ) (n : Nat) (hi : 0 ≤ i)
    (he : i + n ≤ 8 * s.length) : ∃ v, field_spec s i n v := by
  induction n generalizing i with
  | zero => exact ⟨0, by rw [field_spec]; simp [field_pre]⟩
  | succ n ih =>
    obtain ⟨v, hv⟩ := ih (i + 1) (by omega) (by omega)
    let b := ((s[(i / 8).toNat]!).val : ℤ) / 2 ^ (i % 8).toNat % 2
    have hb : bit_spec s i b := ⟨trivial, ⟨hi, by omega⟩, rfl⟩
    refine ⟨b + 2 * v, ?_⟩
    rw [field_spec]
    refine ⟨by unfold field_pre; omega, fun _ => ⟨by omega, fun _ => ⟨b, hb, fun _ => ⟨v, ?_, rfl⟩⟩⟩⟩
    convert hv using 1 <;> omega

theorem field_positive_end (s : List U8) (i n v : ℤ) (hn : 0 < n)
    (h : field_spec s i n v) : i + n ≤ 8 * s.length := by
  have h0 := h
  rw [field_spec] at h0
  obtain ⟨b, hb, _⟩ := (h0.2 h0.1).2 (by omega)
  exact field_end_bound s i n v (by have hi := hb.2.1.2; omega) h

theorem tables_iff (s lit dist : List U8) (i j : ℤ) :
    tables_spec s i lit dist j ↔ ∃ (nc : Nat) (cl all : List U8),
      field_spec s i 5 ((lit.length : ℤ) - 257) ∧
      field_spec s (i + 5) 5 ((dist.length : ℤ) - 1) ∧
      field_spec s (i + 10) 4 ((nc : ℤ) - 4) ∧ 4 ≤ nc ∧ nc ≤ 19 ∧
      ClSpec s (i + 14) nc cl ∧ valid_spec cl 7 true ∧
      all.length = lit.length + dist.length ∧ all.take lit.length = lit ∧ all.drop lit.length = dist ∧
      lengths_spec s (i + 14 + 3 * nc) cl 0 all j ∧ valid_spec lit 15 true ∧ valid_spec dist 15 true := by
  constructor
  · rintro ⟨_, nc, cl, all, ⟨lv, hlv, hll⟩, ⟨dv, hdv, hdl⟩, ⟨cv, hcv, hnc⟩,
      hcllen, hclvals, hvalid, halllen, hpre, htail, hlength, hlit, hdist⟩
    have hcvr := field_range _ _ _ _ hcv
    change 0 ≤ cv ∧ cv < 16 at hcvr
    have hcn : (nc.toNat : ℤ) = nc := by omega
    refine ⟨nc.toNat, cl, all, ?_, ?_, ?_, by omega, by omega, ?_, hvalid, by omega, ?_, ?_, ?_, hlit, hdist⟩
    · convert hlv using 1 <;> omega
    · convert hdv using 1 <;> omega
    · convert hcv using 1 <;> omega
    · refine ⟨by omega, ?_⟩
      intro k hk
      have hv := hclvals k (by omega) (by omega)
      change (↑k < nc → ∃ v, field_spec s (i + 14 + 3 * k) 3 v ∧ v = (cl[order k]!).val) ∧
        (¬ ↑k < nc → ((cl[order k]!).val : ℤ) = 0) at hv
      split_ifs with hlt
      · obtain ⟨v, hf, heq⟩ := hv.1 (by omega)
        rwa [heq] at hf
      · have hz := hv.2 (by omega)
        omega
    · simpa only [List.drop_zero, Int.toNat_natCast] using hpre
    · have he : ((all.length : ℤ) - lit.length).toNat = (all.drop lit.length).length := by
        simp only [List.length_drop]; omega
      simpa only [Int.toNat_natCast, he, List.take_length] using htail
    · simpa only [hcn] using hlength
  · rintro ⟨nc, cl, all, hl, hd, hc, hnc, hnc', hcl, hv, ha, hp, ht, hlength, hlit, hdist⟩
    refine ⟨trivial, nc, cl, all, ⟨_, hl, by omega⟩, ⟨_, hd, by omega⟩, ⟨_, hc, by omega⟩,
      by have he := hcl.1; omega, ?_, hv, by omega, ?_, ?_, hlength, hlit, hdist⟩
    · intro k hk hk'
      have hkn : (k.toNat : ℤ) = k := by omega
      have hh := hcl.2 k.toNat (by omega)
      change (k < ↑nc → ∃ v, field_spec s (i + 14 + 3 * k) 3 v ∧ v = (cl[order k.toNat]!).val) ∧
        (¬ k < ↑nc → ((cl[order k.toNat]!).val : ℤ) = 0)
      constructor
      · intro hlt
        rw [if_pos (by omega : k.toNat < nc), hkn] at hh
        exact ⟨_, hh, rfl⟩
      · intro hnlt
        rw [if_neg (by omega : ¬ k.toNat < nc)] at hh
        omega
    · simpa only [List.drop_zero, Int.toNat_natCast] using hp
    · have he : ((all.length : ℤ) - lit.length).toNat = (all.drop lit.length).length := by
        simp only [List.length_drop]; omega
      simpa only [Int.toNat_natCast, he, List.take_length] using ht

theorem tables_bounds (s lit dist : List U8) (i j : ℤ) (h : tables_spec s i lit dist j) :
    257 ≤ lit.length ∧ lit.length ≤ 288 ∧ 1 ≤ dist.length ∧ dist.length ≤ 32 := by
  obtain ⟨nc, cl, all, hl, hd, _⟩ := (tables_iff _ _ _ _ _).mp h
  have hlr := field_range _ _ _ _ hl
  have hdr := field_range _ _ _ _ hd
  change 0 ≤ (lit.length : ℤ) - 257 ∧ (lit.length : ℤ) - 257 < 32 at hlr
  change 0 ≤ (dist.length : ℤ) - 1 ∧ (dist.length : ℤ) - 1 < 32 at hdr
  omega

theorem lengths_mono (s cl all : List U8) (i p j : ℤ)
    (h : lengths_spec s i cl p all j) : i ≤ j := by
  generalize hm : ((all.length : ℤ) - p).toNat = m
  induction m using Nat.strong_induction_on generalizing i p j with
  | h m ih =>
    rw [lengths_spec] at h
    have hp := h.1
    have hx := h.2 hp
    by_cases hend : p = all.length
    · have he := hx.1 hend; omega
    have hx := hx.2 hend
    simp only [guard_and] at hx
    obtain ⟨sym, a, n, hs, ha, hb⟩ := hx
    have hsym := symbol_bounds _ _ _ _ hs
    have hia : i < a := by omega
    have recur (b v : ℤ) (hv : 0 < v) (hbound : p + v ≤ all.length)
        (hib : i ≤ b) (hr : lengths_spec s b cl (p + v) all j) : i ≤ j := by
      have hh := ih ((all.length : ℤ) - (p + v)).toNat
        (by clear h hb hs; unfold lengths_pre at hp; omega) b (p + v) j hr rfl
      omega
    by_cases hlit : sym < 16
    · obtain ⟨hn, _, hr⟩ := hb.1 hlit
      subst n
      exact recur a 1 (by omega) (by unfold lengths_pre at hp; omega) (by omega) hr
    have hb := hb.2 hlit
    by_cases h16 : sym = 16
    · obtain ⟨_, _, hn, _, hr⟩ := hb.1 h16
      exact recur (a + 2) n (by omega) hn.2 (by omega) hr
    have hb := hb.2 h16
    by_cases h17 : sym = 17
    · obtain ⟨_, hn, _, hr⟩ := hb.1 h17
      exact recur (a + 3) n (by omega) hn.2 (by omega) hr
    obtain ⟨_, _, hn, _, hr⟩ := hb.2 h17
    exact recur (a + 7) n (by omega) hn.2 (by omega) hr

end Gzip.Proofs.Decode.DynamicFacts
