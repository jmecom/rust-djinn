import Aeneas
import Gzip.Spec
import Mathlib.Tactic.IntervalCases

open Aeneas Std Result
open Gzip.Spec

set_option maxHeartbeats 2000000

namespace Gzip.Proofs.Huffman

def earlier (lens : List U8) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => earlier lens n k + if (lens[k]!).val = n then 1 else 0

theorem earlier_correct (lens : List U8) (n k : ℕ) (hk : k ≤ lens.length) :
    earlier_spec lens k n (earlier lens n k) := by
  induction k with
  | zero =>
      rw [earlier_spec]
      exact ⟨⟨by omega, by omega⟩, fun _ => ⟨fun _ => rfl, fun hn => False.elim (hn rfl)⟩⟩
  | succ k ih =>
      have hi := ih (by omega)
      have hindex : ((k + 1 : ℕ) - (1 : ℤ)).toNat = k := by omega
      rw [earlier_spec]
      refine ⟨⟨by omega, by omega⟩, fun _ => ⟨fun hz => by omega, fun _ => ?_⟩⟩
      constructor
      · intro he
        have he' : (lens[k]!).val = n := by rw [hindex] at he; omega
        refine ⟨(earlier lens n k : ℕ), ?_, ?_⟩
        · convert hi using 1 <;> omega
        · simp only [earlier, he', if_true, Nat.cast_add, Nat.cast_one]
      · intro he
        have he' : (lens[k]!).val ≠ n := by intro he'; apply he; rw [hindex, he']
        simp only [earlier, he', if_false, Nat.add_zero]
        convert hi using 1 <;> omega

def shorter (lens : List U8) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => shorter lens n k +
      if 1 ≤ (lens[k]!).val ∧ (lens[k]!).val < n then 2 ^ (n - (lens[k]!).val) else 0

theorem shorter_correct (lens : List U8) (n k : ℕ) (hk : k ≤ lens.length) :
    shorter_spec lens k n (shorter lens n k) := by
  induction k with
  | zero =>
      rw [shorter_spec]
      exact ⟨⟨by omega, by omega⟩, fun _ => ⟨fun _ => rfl, fun hn => False.elim (hn rfl)⟩⟩
  | succ k ih =>
      have hi := ih (by omega)
      have hindex : ((k + 1 : ℕ) - (1 : ℤ)).toNat = k := by omega
      rw [shorter_spec]
      refine ⟨⟨by omega, by omega⟩, fun _ => ⟨fun hz => by omega, fun _ => ?_⟩⟩
      constructor
      · intro he
        have he' : 1 ≤ (lens[k]!).val ∧ (lens[k]!).val < n := by rw [hindex] at he; omega
        refine ⟨(shorter lens n k : ℕ), ?_, ?_⟩
        · convert hi using 1 <;> omega
        · have hd : ((n : ℤ) - (lens[k]!).val).toNat = n - (lens[k]!).val := by omega
          rw [shorter, if_pos he', hindex, hd, Nat.cast_add, Nat.cast_pow]
          rfl
      · intro he
        have he' : ¬ (1 ≤ (lens[k]!).val ∧ (lens[k]!).val < n) := by
          intro he'
          apply he
          rw [hindex]
          constructor <;> omega
        simp only [shorter, he', if_false, Nat.add_zero]
        convert hi using 1 <;> omega

def canonical (lens : List U8) (symbol : ℕ) : ℕ :=
  shorter lens (lens[symbol]!).val lens.length + earlier lens (lens[symbol]!).val symbol

theorem canonical_correct (lens : List U8) (symbol : ℕ) (hs : symbol < lens.length) :
    codeword_spec lens symbol (canonical lens symbol) := by
  refine ⟨trivial, ⟨by omega, by omega⟩, (shorter lens (lens[symbol]!).val lens.length : ℕ),
    shorter_correct _ _ _ (by omega), (earlier lens (lens[symbol]!).val symbol : ℕ),
    earlier_correct _ _ _ (by omega), ?_⟩
  simp [canonical, Nat.cast_add]

def fixedLengths : List U8 := List.ofFn fun i : Fin 288 =>
  if i.val < 144 then 8#u8 else if i.val < 256 then 9#u8 else if i.val < 280 then 7#u8 else 8#u8

def fixedWord (symbol : ℕ) : ℕ :=
  if symbol < 144 then symbol + 48 else if symbol < 256 then symbol + 256
    else if symbol < 280 then symbol - 256 else symbol - 88

set_option maxRecDepth 10000 in
theorem fixed_codes : ∀ symbol : Fin 288,
    canonical fixedLengths symbol.val = fixedWord symbol.val := by
  decide

theorem fixed_lengths : fixedlit_spec fixedLengths := by
  refine ⟨trivial, by simp only [fixedLengths, List.length_ofFn, Nat.cast_ofNat], ?_⟩
  intro k hk0 hk1
  have hk : k.toNat < 288 := by omega
  have hkcast : (k.toNat : ℤ) = k := by omega
  refine ⟨(fixedLengths[k.toNat]!).val, ?_, rfl⟩
  rw [getElem!_pos fixedLengths k.toNat (by simpa only [fixedLengths, List.length_ofFn] using hk)]
  simp only [fixedLengths, List.getElem_ofFn, fixedlen_spec, fixedlen_pre]
  split_ifs <;> scalar_tac

theorem fixed_codeword (symbol : ℕ) (hs : symbol < 288) :
    codeword_spec fixedLengths symbol (fixedWord symbol) := by
  have h := canonical_correct fixedLengths symbol (by simpa only [fixedLengths, List.length_ofFn] using hs)
  rw [fixed_codes ⟨symbol, hs⟩] at h
  exact h

end Gzip.Proofs.Huffman
