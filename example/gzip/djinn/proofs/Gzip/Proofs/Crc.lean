import Aeneas
import Gzip.Spec
import Mathlib.Data.Nat.Bitwise

open Aeneas Std Result
open Gzip.Spec

namespace Gzip.Proofs.Crc

theorem xor_nat (a b : ℕ) : xor_spec a b (a ^^^ b : ℕ) := by
  rw [xor_spec]
  refine ⟨by simp [xor_pre], fun _ => ⟨?_, ?_⟩⟩
  · intro hz
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst a b
    simp
  · intro hz
    refine ⟨(a / 2 ^^^ b / 2 : ℕ), ?_, ?_⟩
    · simpa only [Int.natCast_ediv, Nat.cast_ofNat] using xor_nat (a / 2) (b / 2)
    · have hd := Nat.xor_div_two (a := a) (b := b)
      have hm := Nat.xor_mod_two_eq (m := a) (n := b)
      have he := Nat.mod_add_div (a ^^^ b) 2
      push_cast
      omega
termination_by a + b
decreasing_by omega

def one (c : ℕ) : ℕ := if c % 2 = 1 then c / 2 ^^^ 3988292384 else c / 2

def bits (c : ℕ) : ℕ → ℕ
  | 0 => c
  | n + 1 => one (bits c n)

theorem one_spec (c : ℕ) : crcbit_spec c (one c) := by
  refine ⟨by simp [crcbit_pre], ?_, ?_⟩
  · intro hc
    have hn : c % 2 = 1 := by omega
    simp only [one, hn, if_true]
    simpa only [Int.natCast_ediv, Nat.cast_ofNat] using xor_nat (c / 2) 3988292384
  · intro hc
    have hn : ¬ c % 2 = 1 := by omega
    simp only [one, hn, if_false, Int.natCast_ediv, Nat.cast_ofNat]

theorem bits_spec (c n : ℕ) : crcbits_spec c n (bits c n) := by
  induction n with
  | zero =>
      rw [crcbits_spec]
      simp [crcbits_pre, bits]
  | succ n ih =>
      rw [crcbits_spec]
      refine ⟨by simp only [crcbits_pre]; omega, fun _ => ⟨by omega, fun _ => ?_⟩⟩
      refine ⟨bits c n, ?_, one_spec (bits c n)⟩
      simpa using ih

theorem one_linear (a b : ℕ) : one (a ^^^ b) = one a ^^^ one b := by
  have hm := Nat.xor_mod_two_eq (m := a) (n := b)
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  all_goals have hs : (a + b) % 2 = (a % 2 + b % 2) % 2 := Nat.add_mod a b 2
  all_goals simp only [ha, hb] at hs
  all_goals simp only [one, hm, hs, ha, hb, Nat.xor_div_two]
  all_goals simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem bits_linear (a b n : ℕ) : bits (a ^^^ b) n = bits a n ^^^ bits b n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bits, ih, one_linear]

theorem bits_commute (c n : ℕ) : bits (one c) n = one (bits c n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bits, ih]

theorem bits_mul_pow (c n : ℕ) : bits (c * 2 ^ n) n = c := by
  induction n with
  | zero => simp [bits]
  | succ n ih =>
      rw [bits, ← bits_commute, Nat.pow_succ, ← Nat.mul_assoc]
      have ho (x : ℕ) : one (x * 2) = x := by simp [one]
      rw [ho]
      exact ih

theorem bits_table (c : ℕ) : bits c 8 = c / 256 ^^^ bits (c % 256) 8 := by
  have hl : c % 256 < 256 := Nat.mod_lt _ (by decide)
  have hd : (c / 256 * 256 ^^^ c % 256) / 256 = c / 256 := by
    change (c / 256 * 2 ^ 8 ^^^ c % 256) / 2 ^ 8 = c / 256
    rw [Nat.xor_div_two_pow]
    simp [Nat.div_eq_of_lt hl]
  have hm : (c / 256 * 256 ^^^ c % 256) % 256 = c % 256 := by
    change (c / 256 * 2 ^ 8 ^^^ c % 256) % 2 ^ 8 = c % 256
    rw [Nat.xor_mod_two_pow]
    simp
  have he : c = c / 256 * 256 ^^^ c % 256 := by omega
  conv_lhs => rw [he]
  rw [bits_linear]
  have hh : bits (c / 256 * 256) 8 = c / 256 := bits_mul_pow (c / 256) 8
  rw [hh]

def reg (data : List U8) : ℕ → ℕ
  | 0 => 4294967295
  | n + 1 => bits (reg data n ^^^ (data[n]!).val) 8

theorem reg_spec (data : List U8) (n : ℕ) (hn : n ≤ data.length) :
    crcreg_spec data n (reg data n) := by
  induction n with
  | zero =>
      rw [crcreg_spec]
      simp [crcreg_pre, reg]
  | succ n ih =>
      rw [crcreg_spec]
      refine ⟨by simp only [crcreg_pre]; omega, fun _ => ⟨by omega, fun _ => ?_⟩⟩
      have hprev := ih (by omega)
      have hxor := xor_nat (reg data n) (data[n]!).val
      refine ⟨reg data n, by simpa using hprev, reg data n ^^^ (data[n]!).val, ?_, ?_⟩
      · simpa using hxor
      · exact bits_spec _ 8

theorem table_byte (c : ℕ) (byte : U8) :
    bits (c ^^^ byte.val) 8 = c / 256 ^^^ bits ((c ^^^ byte.val) % 256) 8 := by
  rw [bits_table]
  have hb : byte.val < 256 := by scalar_tac
  have hd : (c ^^^ byte.val) / 256 = c / 256 := by
    change (c ^^^ byte.val) / 2 ^ 8 = c / 2 ^ 8
    rw [Nat.xor_div_two_pow]
    simp [Nat.div_eq_of_lt hb]
  rw [hd]

end Gzip.Proofs.Crc
