import Gzip.Proofs.Decode.Decoding

open Aeneas Std
open Gzip.Spec Gzip.Proofs.Decode.Decoding

namespace Gzip.Proofs.Decode.Huffman

theorem earlier_exists (lens : List U8) (k n : ℤ)
    (hp : earlier_pre lens k n) : ∃ c, earlier_spec lens k n c := by
  generalize hm : k.toNat = m
  induction m using Nat.strong_induction_on generalizing k with
  | h m ih =>
    by_cases hk : k = 0
    · subst k
      exact ⟨0, by rw [earlier_spec]; simp [earlier_pre]⟩
    · have hlt : (k - 1).toNat < m := hm ▸ int_step_decreases k hp.1 hk
      obtain ⟨c, hc⟩ := ih _ hlt (k - 1) (by unfold earlier_pre at *; omega) rfl
      by_cases hl : ((lens[(k - 1).toNat]!).val : ℤ) = n
      · refine ⟨c + 1, ?_⟩
        rw [earlier_spec]
        exact ⟨hp, fun _ => ⟨fun h => (hk h).elim,
          fun _ => ⟨fun _ => ⟨c, hc, rfl⟩, fun h => (h hl).elim⟩⟩⟩
      · refine ⟨c, ?_⟩
        rw [earlier_spec]
        exact ⟨hp, fun _ => ⟨fun h => (hk h).elim,
          fun _ => ⟨fun h => (hl h).elim, fun _ => hc⟩⟩⟩

theorem earlier_nonneg (lens : List U8) (k n c : ℤ)
    (h : earlier_spec lens k n c) : 0 ≤ c := by
  have hz : earlier_spec lens 0 n 0 := by rw [earlier_spec]; simp [earlier_pre]
  have hk : 0 ≤ k := by rw [earlier_spec] at h; exact h.1.1
  exact earlier_mono lens 0 k n 0 c hk hz h

theorem shorter_scale (lens : List U8) (k m n a e b : ℤ)
    (hm : 1 ≤ m) (hmn : m < n)
    (ha : shorter_spec lens k m a) (he : earlier_spec lens k m e)
    (hb : shorter_spec lens k n b) :
    (a + e) * 2 ^ (n - m).toNat ≤ b := by
  generalize hq : k.toNat = q
  induction q using Nat.strong_induction_on generalizing k a e b with
  | h q ih =>
    rw [shorter_spec] at ha hb
    rw [earlier_spec] at he
    have hp := ha.1
    have hab := ha.2 hp
    have heb := he.2 hp
    have hbb := hb.2 hp
    by_cases hk : k = 0
    · rw [hab.1 hk, heb.1 hk, hbb.1 hk]; simp
    · have hlt : (k - 1).toNat < q := hq ▸ int_step_decreases k hp.1 hk
      have ih' := ih _ hlt
      have hab := hab.2 hk
      have heb := heb.2 hk
      have hbb := hbb.2 hk
      by_cases hlm : 1 ≤ ((lens[(k - 1).toNat]!).val : ℤ) ∧
          ((lens[(k - 1).toNat]!).val : ℤ) < m
      · have hln : 1 ≤ ((lens[(k - 1).toNat]!).val : ℤ) ∧
            ((lens[(k - 1).toNat]!).val : ℤ) < n := by omega
        obtain ⟨a', ha', rfl⟩ := hab.1 hlm
        obtain ⟨b', hb', rfl⟩ := hbb.1 hln
        have he' := heb.2 (by omega)
        have hrec := ih' _ _ _ _ ha' he' hb' rfl
        have hexp : (n - ((lens[(k - 1).toNat]!).val : ℤ)).toNat =
            (m - ((lens[(k - 1).toNat]!).val : ℤ)).toNat + (n - m).toNat := by omega
        rw [hexp, pow_add]
        nlinarith
      · have ha' := hab.2 hlm
        by_cases hle : ((lens[(k - 1).toNat]!).val : ℤ) = m
        · obtain ⟨e', he', rfl⟩ := heb.1 hle
          obtain ⟨b', hb', rfl⟩ := hbb.1 (by omega)
          have hrec := ih' _ _ _ _ ha' he' hb' rfl
          rw [hle]
          nlinarith
        · have he' := heb.2 hle
          by_cases hln : 1 ≤ ((lens[(k - 1).toNat]!).val : ℤ) ∧
              ((lens[(k - 1).toNat]!).val : ℤ) < n
          · obtain ⟨b', hb', rfl⟩ := hbb.1 hln
            have hrec := ih' _ _ _ _ ha' he' hb' rfl
            have hpos : (0 : ℤ) ≤ 2 ^ (n - ((lens[(k - 1).toNat]!).val : ℤ)).toNat := by positivity
            omega
          · exact ih' _ _ _ _ ha' he' (hbb.2 hln) rfl

theorem codeword_separated (lens : List U8) (x y a b : ℤ)
    (hx : codeword_spec lens x a) (hy : codeword_spec lens y b)
    (hm : 1 ≤ ((lens[x.toNat]!).val : ℤ))
    (hmn : (lens[x.toNat]!).val < (lens[y.toNat]!).val) :
    (a + 1) * 2 ^ (((lens[y.toNat]!).val : ℤ) - (lens[x.toNat]!).val).toNat ≤ b := by
  obtain ⟨_, hxb, u, hu, v, hv, rfl⟩ := hx
  obtain ⟨_, hyb, u', hu', v', hv', rfl⟩ := hy
  obtain ⟨e, he⟩ := earlier_exists lens lens.length (lens[x.toNat]!).val (by
    unfold earlier_pre; omega)
  have hcount := earlier_strict lens x lens.length (lens[x.toNat]!).val v e hxb.2 rfl hv he
  have hscale := shorter_scale lens lens.length _ _ u e u' hm (by omega) hu he hu'
  have hnonneg := earlier_nonneg lens y _ v' hv'
  have hpow : (0 : ℤ) < 2 ^ (((lens[y.toNat]!).val : ℤ) - (lens[x.toNat]!).val).toNat := by positivity
  nlinarith

theorem symbol_unique (s lens : List U8) (i x y : ℤ)
    (hx : symbol_spec s i lens x) (hy : symbol_spec s i lens y) : x = y := by
  rcases _root_.lt_trichotomy (lens[x.toNat]!).val (lens[y.toNat]!).val with hlt | heq | hgt
  · obtain ⟨_, _, hm, a, ha, hca⟩ := hx
    obtain ⟨_, _, _, b, hb, hcb⟩ := hy
    have hsep := codeword_separated lens x y a b ha hb hm hlt
    have hpre := code_prefix_bound s i _ _ a b (by omega) hca hcb
    omega
  · exact symbol_unique_equal_lengths s lens i x y hx hy heq
  · obtain ⟨_, _, _, a, ha, hca⟩ := hx
    obtain ⟨_, _, hm, b, hb, hcb⟩ := hy
    have hsep := codeword_separated lens y x b a hb ha hm hgt
    have hpre := code_prefix_bound s i _ _ b a (by omega) hcb hca
    omega

end Gzip.Proofs.Decode.Huffman
