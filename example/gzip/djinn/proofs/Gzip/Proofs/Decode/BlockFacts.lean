import Gzip.Proofs.Decode.DynamicImpl
import Gzip.Proofs.Decode.SymbolsImpl

open Aeneas Std Result Classical
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.RoundTrip Gzip.Proofs.Decode.SymbolsFacts
open Gzip.Proofs.Decode.DynamicFacts Gzip.Proofs.Decode.StoredImpl

namespace Gzip.Proofs.Decode.BlockFacts

theorem symbols_bounds (s lit dist prev out : List U8) (i j : ℤ)
    (h : symbols_spec s i lit dist prev out j) : i < j ∧ j ≤ 8 * s.length := by
  generalize hm : (8 * (s.length : ℤ) - i).toNat = m
  induction m using Nat.strong_induction_on generalizing i prev with
  | h m ih =>
    obtain ⟨sym, a, hs, ha, hab, hr⟩ := (symbols_unfold _ _ _ _ _ _ _).mp h
    by_cases he : sym = 256
    · simp only [if_pos he] at hr
      rw [hr.2]; exact hab
    by_cases hl : sym < 256
    · simp only [if_neg he, if_pos hl] at hr
      obtain ⟨p, hp, hrec⟩ := hr
      have hv := ih _ (hm ▸ bit_measure_decreases s i a hab.1 hab.2) p a hrec rfl
      omega
    · simp only [if_neg he, if_neg hl] at hr
      obtain ⟨len, d, c, _, hcb, p, hp, hrec⟩ := hr
      have hv := ih _ (hm ▸ bit_measure_decreases s i c (_root_.lt_trans hab.1 hcb.1) hcb.2) p c hrec rfl
      omega

theorem block_at (s prev out : List U8) (i j v : ℤ) (hv : field_spec s i 2 v) :
    block_spec s i prev out j ↔
      if v = 0 then stored_spec s (i + 2) prev out j
      else if v = 1 then ∃ lit dist, fixedlit_spec lit ∧ fixeddist_spec dist ∧ symbols_spec s (i + 2) lit dist prev out j
      else v = 2 ∧ ∃ lit dist k, tables_spec s (i + 2) lit dist k ∧ symbols_spec s k lit dist prev out j := by
  have he (w : ℤ) : field_spec s i 2 w ↔ v = w := by
    constructor
    · exact Decoding.field_unique _ _ _ _ _ hv
    · intro h; rwa [← h]
  rw [block_spec]
  simp only [block_pre, true_and, he]
  split_ifs <;> simp_all <;> aesop

theorem block_has_field (s prev out : List U8) (i j : ℤ) (h : block_spec s i prev out j) :
    ∃ v, field_spec s i 2 v := by
  by_cases h0 : field_spec s i 2 0
  · exact ⟨0, h0⟩
  by_cases h1 : field_spec s i 2 1
  · exact ⟨1, h1⟩
  exact ⟨2, ((h.2.2 h0).2 h1).1⟩

theorem tables_mono (s lit dist : List U8) (i j : ℤ) (h : tables_spec s i lit dist j) : i < j := by
  obtain ⟨nc, cl, all, _, _, _, hn, _, _, _, _, _, _, hl, _⟩ := (tables_iff _ _ _ _ _).mp h
  have hm := lengths_mono _ _ _ _ _ _ hl
  omega

theorem block_bounds_length (s prev out : List U8) (i j : ℤ) (h : block_spec s i prev out j) :
    i < j ∧ j ≤ 8 * s.length ∧ prev.length ≤ out.length := by
  obtain ⟨v, hv⟩ := block_has_field _ _ _ _ _ h
  have hh := (block_at _ _ _ _ _ _ hv).mp h
  split_ifs at hh with h0 h1
  · obtain ⟨len, hl, _, hb, hout, hj⟩ := (stored_iff _ _ _ _ _).mp hh
    have hlr := u16_range _ _ _ hl
    refine ⟨by omega, by omega, ?_⟩
    rw [hout, List.length_append]; omega
  · obtain ⟨lit, dist, _, _, hs⟩ := hh
    have hb := symbols_bounds _ _ _ _ _ _ _ hs
    exact ⟨by omega, hb.2, symbols_length _ _ _ _ _ _ _ hs⟩
  · obtain ⟨_, lit, dist, k, ht, hs⟩ := hh
    have htk := tables_mono _ _ _ _ _ ht
    have hb := symbols_bounds _ _ _ _ _ _ _ hs
    exact ⟨by omega, hb.2, symbols_length _ _ _ _ _ _ _ hs⟩

theorem blocks_unfold (s prev out : List U8) (i j : ℤ) :
    blocks_spec s i prev out j ↔
      if bit_spec s i 0 then ∃ mid k, block_spec s (i + 1) prev mid k ∧ blocks_spec s k mid out j
      else block_spec s (i + 1) prev out j := by
  rw [blocks_spec]
  simp only [blocks_pre, true_and, true_implies, guard_and]
  split_ifs with hbit
  · simp only [hbit, true_implies, not_true_eq_false, false_implies, and_true]
    constructor
    · rintro ⟨mid, k, hb, _, hr⟩; exact ⟨mid, k, hb, hr⟩
    · rintro ⟨mid, k, hb, hr⟩
      have hk := block_bounds_length _ _ _ _ _ hb
      exact ⟨mid, k, hb, ⟨by omega, hk.2.1⟩, hr⟩
  · simp only [hbit, false_implies, not_false_eq_true, true_implies, true_and]

theorem blocks_length (s prev out : List U8) (i j : ℤ) (h : blocks_spec s i prev out j) :
    prev.length ≤ out.length := by
  generalize hm : (8 * (s.length : ℤ) - i).toNat = m
  induction m using Nat.strong_induction_on generalizing i prev with
  | h m ih =>
    rw [blocks_unfold] at h
    split_ifs at h
    · obtain ⟨mid, k, hb, hr⟩ := h
      have hk := block_bounds_length _ _ _ _ _ hb
      have hrec := ih _ (hm ▸ bit_measure_decreases s i k (by omega) hk.2.1) mid k hr rfl
      omega
    · exact (block_bounds_length _ _ _ _ _ h).2.2

theorem blocks_has_bit (s prev out : List U8) (i j : ℤ) (hi : 0 ≤ i)
    (h : blocks_spec s i prev out j) : ∃ v, bit_spec s i v := by
  rw [blocks_unfold] at h
  split_ifs at h with hb
  · exact ⟨0, hb⟩
  · obtain ⟨v, hv⟩ := block_has_field _ _ _ _ _ h
    have he := field_positive_end _ _ _ _ (by omega) hv
    exact ⟨_, trivial, ⟨hi, by omega⟩, rfl⟩

theorem blocks_at (s prev out : List U8) (i j v : ℤ) (hv : bit_spec s i v) :
    blocks_spec s i prev out j ↔
      if v = 0 then ∃ mid k, block_spec s (i + 1) prev mid k ∧ blocks_spec s k mid out j
      else block_spec s (i + 1) prev out j := by
  have he : bit_spec s i 0 ↔ v = 0 := by
    constructor
    · exact Decoding.bit_unique _ _ _ _ hv
    · intro he; rwa [← he]
  rw [blocks_unfold, he]
  split_ifs <;> rfl

end Gzip.Proofs.Decode.BlockFacts
