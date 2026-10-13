import Gzip.Spec
import Gzip.Code.Funs
import Gzip.Vocab
import Mathlib.Data.Nat.Bitwise

open Aeneas Std Result
open Gzip.Spec Gzip.solution

namespace Gzip.Proofs.Decode.CrcImpl

theorem nat_xor_spec (a b : Nat) : xor_spec a b (a ^^^ b : Nat) := by
  generalize hm : a + b = m
  induction m using Nat.strong_induction_on generalizing a b with
  | h m ih =>
    rw [xor_spec]
    refine ⟨⟨by omega, by omega⟩, fun _ => ⟨?_, ?_⟩⟩
    · intro hz
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a; subst b; rfl
    · intro hn
      have hlt : a / 2 + b / 2 < m := by omega
      have hrec := ih (a / 2 + b / 2) hlt (a / 2) (b / 2) rfl
      refine ⟨(a / 2 ^^^ b / 2 : Nat), ?_, ?_⟩
      · simpa only [Int.natCast_ediv, Nat.cast_ofNat] using hrec
      · have he := Nat.mod_add_div (a ^^^ b) 2
        rw [Nat.xor_mod_two_eq, Nat.xor_div_two] at he
        exact_mod_cast he.symm

theorem scalar_xor_spec (a b : U32) : xor_spec a.val b.val (a ^^^ b).val := by
  rw [UScalar.val_xor]
  exact nat_xor_spec a.val b.val

theorem crcbits_zero (c : ℤ) (hc : 0 ≤ c) : crcbits_spec c 0 c := by
  rw [crcbits_spec]
  simp [crcbits_pre, hc]

theorem crcbits_succ (c n v w : ℤ) (h : crcbits_spec c n v) (hw : crcbit_spec v w) :
    crcbits_spec c (n + 1) w := by
  have hn : 0 ≤ c ∧ 0 ≤ n := by rw [crcbits_spec] at h; exact h.1
  rw [crcbits_spec]
  refine ⟨⟨hn.1, by omega⟩, fun _ => ⟨?_, ?_⟩⟩
  · intro hz; omega
  · intro _; exact ⟨v, by simpa only [add_sub_cancel_right] using h, hw⟩

theorem crcreg_zero (data : List U8) : crcreg_spec data 0 4294967295 := by
  rw [crcreg_spec]
  simp [crcreg_pre]

theorem crcreg_succ (data : List U8) (n c v w : ℤ) (hn : n < data.length)
    (hc : crcreg_spec data n c) (hv : xor_spec c (data[n.toNat]!).val v)
    (hw : crcbits_spec v 8 w) : crcreg_spec data (n + 1) w := by
  have hn0 : 0 ≤ n := by rw [crcreg_spec] at hc; exact hc.1.1
  rw [crcreg_spec]
  refine ⟨⟨by omega, by omega⟩, fun _ => ⟨?_, ?_⟩⟩
  · intro hz; omega
  · intro _
    simp only [add_sub_cancel_right]
    exact ⟨c, hc, v, hv, hw⟩

/-! ## The register as a function: one step, and what the tables hold -/

/-- One shift-and-xor step of the register. -/
def stp (c : Nat) : Nat := if c % 2 = 1 then c / 2 ^^^ 3988292384 else c / 2

theorem crcbit_stp (c : Nat) : crcbit_spec c (stp c) := by
  unfold stp
  refine ⟨show (0 : ℤ) ≤ (c : ℤ) by omega, ?_, ?_⟩
  · intro h
    have h' : c % 2 = 1 := by omega
    rw [if_pos h']
    have hx := nat_xor_spec (c / 2) 3988292384
    simpa only [Int.natCast_ediv, Nat.cast_ofNat] using hx
  · intro h
    have h' : ¬ c % 2 = 1 := by omega
    rw [if_neg h']
    omega

theorem crcbits_iter (c n : Nat) : crcbits_spec c n (stp^[n] c) := by
  induction n with
  | zero => exact_mod_cast crcbits_zero (c : ℤ) (by omega)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := crcbits_succ c n _ _ ih (crcbit_stp _)
    exact_mod_cast h

theorem xor_cancel (x y p : Nat) : (x ^^^ p) ^^^ (y ^^^ p) = x ^^^ y := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit i <;> cases p.testBit i <;> rfl

/-- A step is linear over xor. -/
theorem stp_xor (a b : Nat) : stp (a ^^^ b) = stp a ^^^ stp b := by
  unfold stp
  rw [Nat.xor_mod_two_eq, Nat.xor_div_two]
  by_cases h1 : a % 2 = 1 <;> by_cases h2 : b % 2 = 1
  · have h3 : ¬ (a + b) % 2 = 1 := by omega
    rw [if_pos h1, if_pos h2, if_neg h3, xor_cancel]
  · have h3 : (a + b) % 2 = 1 := by omega
    rw [if_pos h1, if_neg h2, if_pos h3]
    ac_rfl
  · have h3 : (a + b) % 2 = 1 := by omega
    rw [if_neg h1, if_pos h2, if_pos h3]
    ac_rfl
  · have h3 : ¬ (a + b) % 2 = 1 := by omega
    rw [if_neg h1, if_neg h2, if_neg h3]

theorem stps_xor (n a b : Nat) : stp^[n] (a ^^^ b) = stp^[n] a ^^^ stp^[n] b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, stp_xor]

theorem stp_double (x : Nat) : stp (2 * x) = x := by
  unfold stp
  rw [if_neg (by omega)]
  omega

/-- Zero bits shift out without touching the rest. -/
theorem stps_shift (n x : Nat) : stp^[n] (2 ^ n * x) = x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', pow_succ, mul_assoc, ih, stp_double]

theorem mul_add_eq_xor (k a b : Nat) (hb : b < 2 ^ k) : 2 ^ k * a + b = (2 ^ k * a) ^^^ b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_two_pow_mul_add a hb, Nat.testBit_xor, Nat.testBit_two_pow_mul]
  by_cases h : j < k
  · have h' : ¬ k ≤ j := by omega
    simp [h, h']
  · have h' : k ≤ j := by omega
    have hb' : b.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) h'))
    simp [h, h', hb']

/-- A byte step after n steps is n + 8 steps with the byte xored in n bits up. -/
theorem step_byte (n m p u b : Nat) (hm : m = n + 8) (hp : p = 2 ^ n) :
    stp^[8] (stp^[n] u ^^^ b) = stp^[m] (u ^^^ p * b) := by
  subst hm hp
  rw [Nat.add_comm, Function.iterate_add_apply, stps_xor n, stps_shift]

/-- Four byte steps are 32 steps of the register xored with the little-endian word. -/
theorem word_step (c b0 b1 b2 b3 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) :
    stp^[8] (stp^[8] (stp^[8] (stp^[8] (c ^^^ b0) ^^^ b1) ^^^ b2) ^^^ b3)
      = stp^[32] (c ^^^ (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3)) := by
  have e1 : 256 * b1 + b0 = (256 * b1) ^^^ b0 := mul_add_eq_xor 8 b1 b0 (by omega)
  have e2 : 65536 * b2 + (256 * b1 + b0) = (65536 * b2) ^^^ (256 * b1 + b0) :=
    mul_add_eq_xor 16 b2 _ (by omega)
  have e3 : 16777216 * b3 + (65536 * b2 + (256 * b1 + b0))
      = (16777216 * b3) ^^^ (65536 * b2 + (256 * b1 + b0)) := mul_add_eq_xor 24 b3 _ (by omega)
  have ew : b0 + 256 * b1 + 65536 * b2 + 16777216 * b3
      = 16777216 * b3 ^^^ (65536 * b2 ^^^ (256 * b1 ^^^ b0)) := by
    rw [← e1, ← e2, ← e3]
    omega
  rw [step_byte 8 16 256 (c ^^^ b0) b1 rfl (by norm_num),
    step_byte 16 24 65536 _ b2 rfl (by norm_num),
    step_byte 24 32 16777216 _ b3 rfl (by norm_num), ew]
  congr 1
  ac_rfl

theorem stps_shift8 (n y : Nat) : stp^[n + 8] (256 * y) = stp^[n] y := by
  rw [Function.iterate_add_apply]
  congr 1
  exact stps_shift 8 y

theorem split_byte (n m x : Nat) (hm : m = n + 8) :
    stp^[m] x = stp^[m] (x % 256) ^^^ stp^[n] (x / 256) := by
  subst hm
  have e : 256 * (x / 256) + x % 256 = (256 * (x / 256)) ^^^ (x % 256) :=
    mul_add_eq_xor 8 (x / 256) (x % 256) (by omega)
  have key : stp^[n + 8] (256 * (x / 256) + x % 256)
      = stp^[n + 8] (x % 256) ^^^ stp^[n] (x / 256) := by
    rw [e, stps_xor, stps_shift8, Nat.xor_comm]
  rwa [Nat.div_add_mod] at key

/-- 32 steps of a word are the xor of the table entries of its four bytes. -/
theorem word_split (w : Nat) :
    stp^[32] w = stp^[32] (w % 256) ^^^ stp^[24] (w / 256 % 256) ^^^ stp^[16] (w / 65536 % 256)
      ^^^ stp^[8] (w / 16777216) := by
  have d2 : w / 256 / 256 = w / 65536 := by omega
  have d3 : w / 65536 / 256 = w / 16777216 := by omega
  rw [split_byte 24 32 w rfl, split_byte 16 24 (w / 256) rfl, d2,
    split_byte 8 16 (w / 65536) rfl, d3]
  simp only [Nat.xor_assoc]

/-- The register after n bytes. -/
def reg (data : List U8) : Nat → Nat
  | 0 => 4294967295
  | n + 1 => stp^[8] (reg data n ^^^ (data[n]!).val)

theorem reg_four (data : List U8) (n : Nat) :
    reg data (n + 4) = stp^[8] (stp^[8] (stp^[8] (stp^[8] (reg data n ^^^ (data[n]!).val)
      ^^^ (data[n + 1]!).val) ^^^ (data[n + 2]!).val) ^^^ (data[n + 3]!).val) := rfl

theorem crcreg_reg (data : List U8) (n : Nat) (hn : n ≤ data.length) :
    crcreg_spec data n (reg data n) := by
  induction n with
  | zero => exact_mod_cast crcreg_zero data
  | succ n ih =>
    have hv : xor_spec (reg data n : Nat) ((data[((n : ℕ) : ℤ).toNat]!).val : ℤ)
        ((reg data n ^^^ (data[n]!).val : Nat) : ℤ) := by
      simpa only [Int.toNat_natCast] using nat_xor_spec (reg data n) (data[n]!).val
    have hw : crcbits_spec ((reg data n ^^^ (data[n]!).val : Nat) : ℤ) 8
        ((stp^[8] (reg data n ^^^ (data[n]!).val) : Nat) : ℤ) := by
      exact_mod_cast crcbits_iter (reg data n ^^^ (data[n]!).val) 8
    have h := crcreg_succ data n _ _ _ (by omega) (ih (by omega)) hv hw
    exact_mod_cast h

/-! ## The implementation -/

theorem cast_usize_val (x : U32) : (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

theorem cast_u32_val (x : U8) : (UScalar.cast .U32 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

theorem cast_usize_u32 (k : Usize) (h : k.val < 256) : (UScalar.cast .U32 k).val = k.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

theorem u32_lt (x : U32) : x.val < 4294967296 := by scalar_tac

theorem u8_lt (x : U8) : x.val < 256 := by scalar_tac

theorem arr_len (t : Array U32 4096#usize) : t.val.length = 4096 := by scalar_tac

def BitInv (c0 : Nat) (c : U32) (n : I32) : Prop :=
  0 ≤ n.val ∧ n.val ≤ 8 ∧ c.val = stp^[n.val.toNat] c0

theorem bits_body (c0 : Nat) (c : U32) (n : I32) (h : BitInv c0 c n) :
    crc_byte_loop.body c n ⦃ r => match r with
      | .done v => v.val = stp^[8] c0
      | .cont (v, m) => BitInv c0 v m ∧ (8 - m.val).toNat < (8 - n.val).toNat ⦄ := by
  obtain ⟨hn0, hn8, hbits⟩ := h
  unfold crc_byte_loop.body
  step*
  split <;> step*
  · refine ⟨⟨by scalar_tac, by scalar_tac, ?_⟩, by scalar_tac⟩
    have hn : n1.val.toNat = n.val.toNat + 1 := by omega
    have hi : c.val % 2 = 1 := by scalar_tac
    have hs : stp c.val = c.val / 2 ^^^ 3988292384 := by unfold stp; rw [if_pos hi]
    rw [hn, Function.iterate_succ_apply', ← hbits, hs, UScalar.val_xor, x_post]
    rfl
  · refine ⟨⟨by scalar_tac, by scalar_tac, ?_⟩, by scalar_tac⟩
    have hn : n1.val.toNat = n.val.toNat + 1 := by omega
    have hi : ¬ c.val % 2 = 1 := by
      intro hc1
      have hie : i = 1#u32 := by apply UScalar.eq_of_val_eq; change i.val = 1; omega
      contradiction
    have hs : stp c.val = c.val / 2 := by unfold stp; rw [if_neg hi]
    rw [hn, Function.iterate_succ_apply', ← hbits, hs, c1_post]

@[step]
theorem bits_loop (c : U32) : crc_byte_loop c 0#i32 ⦃ d => d.val = stp^[8] c.val ⦄ := by
  unfold crc_byte_loop
  apply loop.spec_decr_nat (fun (_, n) => (8 - n.val).toNat)
    (fun (v, n) => BitInv c.val v n)
  · rintro ⟨v, n⟩ hinv
    simp only at hinv ⊢
    apply Aeneas.Std.WP.spec_mono (bits_body c.val v n hinv)
    intro r hr
    cases r <;> exact hr
  · exact ⟨by decide, by decide, rfl⟩

/-- 32 more steps of a word, from the steps of its four bytes. -/
theorem word_split_at (n w : Nat) :
    stp^[n + 32] w = stp^[n + 32] (w % 256) ^^^ stp^[n + 24] (w / 256 % 256)
      ^^^ stp^[n + 16] (w / 65536 % 256) ^^^ stp^[n + 8] (w / 16777216) := by
  have d2 : w / 256 / 256 = w / 65536 := by omega
  have d3 : w / 65536 / 256 = w / 16777216 := by omega
  rw [split_byte (n + 24) (n + 32) w (by omega),
    split_byte (n + 16) (n + 24) (w / 256) (by omega), d2,
    split_byte (n + 8) (n + 16) (w / 65536) (by omega), d3]
  simp only [Nat.xor_assoc]

/-- The four bytes from `n`, as a little-endian word. -/
def wd (data : List U8) (n : Nat) : Nat :=
  (data[n]!).val + 256 * (data[n + 1]!).val + 65536 * (data[n + 2]!).val
    + 16777216 * (data[n + 3]!).val

theorem reg_word (data : List U8) (n : Nat) :
    reg data (n + 4) = stp^[32] (reg data n ^^^ wd data n) := by
  rw [reg_four, word_step _ _ _ _ _ (u8_lt _) (u8_lt _) (u8_lt _)]
  rfl

/-- Sixteen byte steps: the four words of the chunk go through 128, 96, 64 and 32 steps. -/
theorem reg_sixteen (data : List U8) (n : Nat) :
    reg data (n + 16) = stp^[128] (reg data n ^^^ wd data n) ^^^ stp^[96] (wd data (n + 4))
      ^^^ stp^[64] (wd data (n + 8)) ^^^ stp^[32] (wd data (n + 12)) := by
  have h1 := reg_word data n
  have h2 : reg data (n + 8) = stp^[32] (reg data (n + 4) ^^^ wd data (n + 4)) :=
    reg_word data (n + 4)
  have h3 : reg data (n + 12) = stp^[32] (reg data (n + 8) ^^^ wd data (n + 8)) :=
    reg_word data (n + 8)
  have h4 : reg data (n + 16) = stp^[32] (reg data (n + 12) ^^^ wd data (n + 12)) :=
    reg_word data (n + 12)
  have a64 : ∀ x, stp^[32] (stp^[32] x) = stp^[64] x :=
    fun x => (Function.iterate_add_apply stp 32 32 x).symm
  have a96 : ∀ x, stp^[32] (stp^[64] x) = stp^[96] x :=
    fun x => (Function.iterate_add_apply stp 32 64 x).symm
  have a128 : ∀ x, stp^[32] (stp^[96] x) = stp^[128] x :=
    fun x => (Function.iterate_add_apply stp 32 96 x).symm
  rw [h4, h3, h2, h1]
  simp only [stps_xor, a64, a96, a128]

def TabInv (t : Array U32 4096#usize) (k : Nat) : Prop :=
  ∀ j < k, (t.val[j]!).val = stp^[8 * (j / 256 + 1)] (j % 256)

theorem table0_body (t : Array U32 4096#usize) (k : Usize) (hk : k.val ≤ 256)
    (h : TabInv t k.val) :
    crc_table_loop0.body t k ⦃ r => match r with
      | .done (a, m) => m.val = 256 ∧ TabInv a 256
      | .cont (a, m) => (m.val ≤ 256 ∧ TabInv a m.val) ∧ 256 - m.val < 256 - k.val ⦄ := by
  unfold crc_table_loop0.body
  step*
  · have hk' : k.val < 256 := by scalar_tac
    have hi : i.val = k.val := by rw [i_post]; exact cast_usize_u32 k hk'
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    intro j hj
    have hl : j < t.val.length := by rw [arr_len]; scalar_tac
    rw [a_post]
    simp only [Array.set_val_eq]
    rw [Djinn.Vocab.getElem!_set _ _ _ _ hl]
    by_cases hjk : j = k.val
    · have e1 : 8 * (k.val / 256 + 1) = 8 := by omega
      have e2 : k.val % 256 = k.val := by omega
      rw [if_pos hjk, hjk, i1_post, hi, e1, e2]
    · rw [if_neg hjk]
      exact h j (by scalar_tac)

theorem table0_loop (t : Array U32 4096#usize) :
    crc_table_loop0 t 0#usize ⦃ r => r.2.val = 256 ∧ TabInv r.1 256 ⦄ := by
  unfold crc_table_loop0
  apply loop.spec_decr_nat (fun (_, k) => 256 - k.val)
    (fun (a, k) => k.val ≤ 256 ∧ TabInv a k.val)
  · rintro ⟨a, k⟩ hinv
    simp only at hinv ⊢
    apply Aeneas.Std.WP.spec_mono (table0_body a k hinv.1 hinv.2)
    intro r hr
    cases r <;> exact hr
  · refine ⟨by simp, ?_⟩
    intro j hj
    simp at hj

theorem table1_body (t : Array U32 4096#usize) (k : Usize) (hk : 256 ≤ k.val)
    (h : TabInv t k.val) :
    crc_table_loop1.body t k ⦃ r => match r with
      | .done a => TabInv a 4096
      | .cont (a, m) => (256 ≤ m.val ∧ TabInv a m.val) ∧ 4096 - m.val < 4096 - k.val ⦄ := by
  unfold crc_table_loop1.body
  step*
  · have hk' : k.val < 4096 := by scalar_tac
    have hiv : i.val = k.val - 256 := by scalar_tac
    have hi1 : i1 = t.val[i.val]! := by
      rw [Djinn.Vocab.val_getElem! t.val i.val (by rw [arr_len]; omega)]; exact i1_post
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    intro j hj
    have hl : j < t.val.length := by rw [arr_len]; scalar_tac
    rw [a_post]
    simp only [Array.set_val_eq]
    rw [Djinn.Vocab.getElem!_set _ _ _ _ hl]
    by_cases hjk : j = k.val
    · have e1 : 8 + 8 * (i.val / 256 + 1) = 8 * (k.val / 256 + 1) := by omega
      have e2 : i.val % 256 = k.val % 256 := by omega
      rw [if_pos hjk, hjk, i2_post, hi1, h i.val (by omega), ← Function.iterate_add_apply,
        e1, e2]
    · rw [if_neg hjk]
      exact h j (by scalar_tac)
  · intro j hj
    exact h j (by scalar_tac)

theorem table1_loop (t : Array U32 4096#usize) (k : Usize) (hk : k.val = 256)
    (h : TabInv t 256) : crc_table_loop1 t k ⦃ a => TabInv a 4096 ⦄ := by
  unfold crc_table_loop1
  apply loop.spec_decr_nat (fun (_, k) => 4096 - k.val)
    (fun (a, k) => 256 ≤ k.val ∧ TabInv a k.val)
  · rintro ⟨a, k⟩ hinv
    simp only at hinv ⊢
    apply Aeneas.Std.WP.spec_mono (table1_body a k hinv.1 hinv.2)
    intro r hr
    cases r <;> exact hr
  · refine ⟨by omega, ?_⟩
    rw [hk]
    exact h

@[step]
theorem table_spec : crc_table ⦃ t => TabInv t 4096 ⦄ := by
  unfold crc_table
  step with table0_loop as ⟨t1, k, hk, ht⟩
  exact table1_loop t1 k hk ht

/-- Row `j` of the table: `8 * j + 8` steps of a byte. -/
theorem tab_get (t : Array U32 4096#usize) (ht : TabInv t 4096) (j b : Nat) (hj : j < 16)
    (hb : b < 256) : (t.val[256 * j + b]!).val = stp^[8 * j + 8] b := by
  have e1 : 8 * ((256 * j + b) / 256 + 1) = 8 * j + 8 := by omega
  have e2 : (256 * j + b) % 256 = b := by omega
  rw [ht (256 * j + b) (by omega), e1, e2]

@[step]
theorem word_at_spec (data : Aeneas.Std.Slice U8) (i : Usize)
    (h : i.val + 4 ≤ data.val.length) : word_at data i ⦃ w => w.val = wd data.val i.val ⦄ := by
  unfold word_at
  step*
  have d0 : i1 = data.val[i.val]! := by
    rw [Djinn.Vocab.val_getElem! data.val i.val (by omega)]; exact i1_post
  have d1 : i4 = data.val[i3.val]! := by
    rw [Djinn.Vocab.val_getElem! data.val i3.val (by omega)]; exact i4_post
  have d2 : i9 = data.val[i8.val]! := by
    rw [Djinn.Vocab.val_getElem! data.val i8.val (by omega)]; exact i9_post
  have d3 : i14 = data.val[i13.val]! := by
    rw [Djinn.Vocab.val_getElem! data.val i13.val (by omega)]; exact i14_post
  rw [i3_post] at d1
  rw [i8_post] at d2
  rw [i13_post] at d3
  unfold wd
  rw [← d0, ← d1, ← d2, ← d3, ← cast_u32_val i1, ← cast_u32_val i4, ← cast_u32_val i9,
    ← cast_u32_val i14, ← i2_post, ← i5_post, ← i10_post, ← i15_post]
  scalar_tac

@[step]
theorem crc_word_spec (t : Array U32 4096#usize) (w : U32) (m : Usize) (ht : TabInv t 4096)
    (hm : m.val ≤ 3) : crc_word t w m ⦃ r => r.val = stp^[32 * m.val + 32] w.val ⦄ := by
  unfold crc_word
  step*
  have hw := u32_lt w
  have v3 : i3.val = w.val % 256 := by rw [i3_post, cast_usize_val, i2_post]
  have v9 : i9.val = w.val / 256 % 256 := by rw [i9_post, cast_usize_val, i8_post, i7_post]
  have v16 : i16.val = w.val / 65536 % 256 := by
    rw [i16_post, cast_usize_val, i15_post, i14_post]
  have v21 : i21.val = w.val / 16777216 := by rw [i21_post, cast_usize_val, i20_post]
  have x3 : i4.val = 256 * (4 * m.val + 3) + w.val % 256 := by scalar_tac
  have x2 : i10.val = 256 * (4 * m.val + 2) + w.val / 256 % 256 := by scalar_tac
  have x1 : i17.val = 256 * (4 * m.val + 1) + w.val / 65536 % 256 := by scalar_tac
  have x0 : i22.val = 256 * (4 * m.val) + w.val / 16777216 := by scalar_tac
  have q3 : i5 = t.val[i4.val]! := by
    rw [Djinn.Vocab.val_getElem! t.val i4.val (by rw [arr_len]; omega)]; exact i5_post
  have q2 : i11 = t.val[i10.val]! := by
    rw [Djinn.Vocab.val_getElem! t.val i10.val (by rw [arr_len]; omega)]; exact i11_post
  have q1 : i18 = t.val[i17.val]! := by
    rw [Djinn.Vocab.val_getElem! t.val i17.val (by rw [arr_len]; omega)]; exact i18_post
  have q0 : i23 = t.val[i22.val]! := by
    rw [Djinn.Vocab.val_getElem! t.val i22.val (by rw [arr_len]; omega)]; exact i23_post
  have g3 : i5.val = stp^[32 * m.val + 32] (w.val % 256) := by
    have e : 8 * (4 * m.val + 3) + 8 = 32 * m.val + 32 := by omega
    rw [q3, x3, tab_get t ht (4 * m.val + 3) _ (by omega) (by omega), e]
  have g2 : i11.val = stp^[32 * m.val + 24] (w.val / 256 % 256) := by
    have e : 8 * (4 * m.val + 2) + 8 = 32 * m.val + 24 := by omega
    rw [q2, x2, tab_get t ht (4 * m.val + 2) _ (by omega) (by omega), e]
  have g1 : i18.val = stp^[32 * m.val + 16] (w.val / 65536 % 256) := by
    have e : 8 * (4 * m.val + 1) + 8 = 32 * m.val + 16 := by omega
    rw [q1, x1, tab_get t ht (4 * m.val + 1) _ (by omega) (by omega), e]
  have g0 : i23.val = stp^[32 * m.val + 8] (w.val / 16777216) := by
    have e : 8 * (4 * m.val) + 8 = 32 * m.val + 8 := by omega
    rw [q0, x0, tab_get t ht (4 * m.val) _ (by omega) (by omega), e]
  rw [word_split_at (32 * m.val) w.val, UScalar.val_xor, i19_post, UScalar.val_xor, i12_post,
    UScalar.val_xor, g3, g2, g1, g0]

def WordInv (data : Aeneas.Std.Slice U8) (c : U32) (i : Usize) : Prop :=
  i.val ≤ data.val.length ∧ c.val = reg data.val i.val

/-- The part of a chunk's sixteen steps that does not depend on the register: its three upper
words through 96, 64 and 32 steps. -/
def restOf (data : List U8) (i : Nat) : Nat :=
  stp^[96] (wd data (i + 4)) ^^^ stp^[64] (wd data (i + 8)) ^^^ stp^[32] (wd data (i + 12))

theorem reg_sixteen' (data : List U8) (n : Nat) :
    reg data (n + 16) = stp^[128] (reg data n ^^^ wd data n) ^^^ restOf data n := by
  rw [reg_sixteen]
  unfold restOf
  simp only [Nat.xor_assoc]

/-- The sixteen bytes of a chunk, read through a range index of the input. -/
theorem chunk_bytes (data : List U8) (i j : Nat) (b : List U8) (hj : j = i + 16)
    (hb : b = data.slice i j) (hlen : i + 16 ≤ data.length) :
    b.length = 16 ∧ ∀ k, k < 16 → b[k]! = data[i + k]! := by
  subst hj hb
  refine ⟨by rw [List.slice_length]; omega, ?_⟩
  intro k hk
  rw [List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩]

/-- A word of the chunk is the word of the input at the chunk's offset. -/
theorem wd_chunk (data b : List U8) (i k : Nat)
    (hb : ∀ k, k < 16 → b[k]! = data[i + k]!) (hk : k + 4 ≤ 16) :
    wd b k = wd data (i + k) := by
  unfold wd
  rw [hb k (by omega), hb (k + 1) (by omega), hb (k + 2) (by omega), hb (k + 3) (by omega)]
  simp only [Nat.add_assoc]

/-- The register-independent part of a chunk, from its sixteen bytes. -/
theorem rest_chunk (data b : List U8) (i : Nat) (hb : ∀ k, k < 16 → b[k]! = data[i + k]!) :
    stp^[96] (wd b 4) ^^^ stp^[64] (wd b 8) ^^^ stp^[32] (wd b 12) = restOf data i := by
  unfold restOf
  rw [wd_chunk data b i 4 hb (by omega), wd_chunk data b i 8 hb (by omega),
    wd_chunk data b i 12 hb (by omega)]

theorem crc_rest_spec (t : Array U32 4096#usize) (b : Aeneas.Std.Slice U8)
    (ht : TabInv t 4096) (hb : 16 ≤ b.val.length) :
    crc_rest_wide t b ⦃ r => r.val = stp^[96] (wd b.val 4) ^^^ stp^[64] (wd b.val 8)
      ^^^ stp^[32] (wd b.val 12) ⦄ := by
  unfold crc_rest_wide
  step*

/-- The pipelined loop's state: the register after `i` bytes, with the register-independent part
and the first word of the chunk at `i` already computed. -/
def PipeInv (data : Aeneas.Std.Slice U8) (c : U32) (i : Usize) (rest w0 : U32) : Prop :=
  i.val + 16 ≤ data.val.length ∧ c.val = reg data.val i.val ∧
    rest.val = restOf data.val i.val ∧ w0.val = wd data.val i.val

theorem pipe_body (data : Aeneas.Std.Slice U8) (t : Array U32 4096#usize)
    (ht : TabInv t 4096) (c : U32) (i : Usize) (rest w0 : U32) (h : PipeInv data c i rest w0) :
    crc32_wide_loop0.body data t c i rest w0 ⦃ r => match r with
      | .done (v, j, rs, w) => PipeInv data v j rs w
      | .cont (v, j, rs, w) => PipeInv data v j rs w ∧
          data.val.length - j.val < data.val.length - i.val ⦄ := by
  obtain ⟨hi, hc, hr, hw⟩ := h
  unfold crc32_wide_loop0.body
  step as ⟨i2, hi2⟩
  all_goals try scalar_tac
  split
  · have h32 : 32 ≤ i2.val := by scalar_tac
    have hlen : i.val + 32 ≤ data.val.length := by scalar_tac
    step as ⟨i3, hi3⟩
    all_goals try scalar_tac
    step as ⟨i4, hi4⟩
    all_goals try scalar_tac
    step as ⟨b, hb⟩
    all_goals try scalar_tac
    have hb16 := chunk_bytes data.val i3.val i4.val b.val (by omega) hb (by omega)
    have hbl : b.val.length = 16 := hb16.1
    have h0 : (0#usize).val = 0 := by scalar_tac
    have h3 : (3#usize).val ≤ 3 := by scalar_tac
    step with (crc_rest_spec t b ht (by omega)) as ⟨rest_next, hrn⟩
    step with (word_at_spec b 0#usize (by omega)) as ⟨w_next, hwn⟩
    step as ⟨i5, hi5⟩
    step with (crc_word_spec t i5 3#usize ht h3) as ⟨i6, hi6⟩
    step as ⟨c1, hc1⟩
    have h6 : i6.val = stp^[128] i5.val := by simpa using hi6
    refine ⟨⟨by scalar_tac, ?_, ?_, ?_⟩, by scalar_tac⟩
    · rw [hi3, reg_sixteen', ← hc, ← hw, ← hr, hc1, UScalar.val_xor, h6, hi5, UScalar.val_xor]
    · rw [hrn]
      exact rest_chunk data.val b.val i3.val hb16.2
    · rw [hwn]
      have hw0 := wd_chunk data.val b.val i3.val 0 hb16.2 (by omega)
      rw [Nat.add_zero] at hw0
      exact hw0
  · first
    | exact ⟨hi, hc, hr, hw⟩
    | (rw [WP.spec_ok]; exact ⟨hi, hc, hr, hw⟩)

theorem pipe_loop (data : Aeneas.Std.Slice U8) (t : Array U32 4096#usize)
    (ht : TabInv t 4096) (c : U32) (i : Usize) (rest w0 : U32) (h : PipeInv data c i rest w0) :
    crc32_wide_loop0 data t c i rest w0 ⦃ r => PipeInv data r.1 r.2.1 r.2.2.1 r.2.2.2 ⦄ := by
  unfold crc32_wide_loop0
  apply loop.spec_decr_nat (fun (_, i, _, _) => data.val.length - i.val)
    (fun (c, i, rest, w0) => PipeInv data c i rest w0)
  · rintro ⟨c, i, rest, w0⟩ hinv
    simp only at hinv ⊢
    apply Aeneas.Std.WP.spec_mono (pipe_body data t ht c i rest w0 hinv)
    intro r hr
    cases r <;> exact hr
  · exact h

theorem tail_body (data : Aeneas.Std.Slice U8) (c : U32) (i : Usize) (h : WordInv data c i) :
    crc32_wide_loop1.body data c i ⦃ r => match r with
      | .done v => v.val = reg data.val data.val.length
      | .cont (v, j) => WordInv data v j ∧ data.val.length - j.val < data.val.length - i.val ⦄ := by
  obtain ⟨hi, hc⟩ := h
  unfold crc32_wide_loop1.body
  step*
  · have hlt : i.val < data.val.length := by scalar_tac
    have d0 : i2 = data.val[i.val]! := by
      rw [Djinn.Vocab.val_getElem! data.val i.val hlt]; exact i2_post
    refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
    rw [i5_post]
    show c1.val = stp^[8] (reg data.val i.val ^^^ (data.val[i.val]!).val)
    rw [c1_post, i4_post, UScalar.val_xor, i3_post, cast_u32_val, hc, d0]

theorem tail_loop (data : Aeneas.Std.Slice U8) (c : U32) (i : Usize) (h : WordInv data c i) :
    crc32_wide_loop1 data c i ⦃ v => v.val = reg data.val data.val.length ⦄ := by
  unfold crc32_wide_loop1
  apply loop.spec_decr_nat (fun (_, i) => data.val.length - i.val)
    (fun (c, i) => WordInv data c i)
  · rintro ⟨c, i⟩ hinv
    simp only at hinv ⊢
    apply Aeneas.Std.WP.spec_mono (tail_body data c i hinv)
    intro r hr
    cases r <;> exact hr
  · exact h

/-- The byte loop of the short-input branch is the same loop as `crc32_wide_loop1`. -/
theorem tail_body2 (data : Aeneas.Std.Slice U8) (c : U32) (i : Usize) (h : WordInv data c i) :
    crc32_wide_loop2.body data c i ⦃ r => match r with
      | .done v => v.val = reg data.val data.val.length
      | .cont (v, j) => WordInv data v j ∧ data.val.length - j.val < data.val.length - i.val ⦄ := by
  obtain ⟨hi, hc⟩ := h
  unfold crc32_wide_loop2.body
  step*
  · have hlt : i.val < data.val.length := by scalar_tac
    have d0 : i2 = data.val[i.val]! := by
      rw [Djinn.Vocab.val_getElem! data.val i.val hlt]; exact i2_post
    refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
    rw [i5_post]
    show c1.val = stp^[8] (reg data.val i.val ^^^ (data.val[i.val]!).val)
    rw [c1_post, i4_post, UScalar.val_xor, i3_post, cast_u32_val, hc, d0]

theorem tail_loop2 (data : Aeneas.Std.Slice U8) (c : U32) (i : Usize) (h : WordInv data c i) :
    crc32_wide_loop2 data c i ⦃ v => v.val = reg data.val data.val.length ⦄ := by
  unfold crc32_wide_loop2
  apply loop.spec_decr_nat (fun (_, i) => data.val.length - i.val)
    (fun (c, i) => WordInv data c i)
  · rintro ⟨c, i⟩ hinv
    simp only at hinv ⊢
    apply Aeneas.Std.WP.spec_mono (tail_body2 data c i hinv)
    intro r hr
    cases r <;> exact hr
  · exact h

/-- The register of the whole input, xored out, is the specification's CRC. -/
theorem crc_final (data : Aeneas.Std.Slice U8) (c : U32) (hc : c.val = reg data.val data.val.length) :
    crc32_spec data.val (c ^^^ 4294967295#u32) := by
  refine ⟨trivial, (reg data.val data.val.length : Nat), crcreg_reg _ _ le_rfl,
    (c ^^^ 4294967295#u32).val, ?_, rfl⟩
  have hx := scalar_xor_spec c 4294967295#u32
  rw [hc] at hx
  simpa only [UScalar.ofNatCore_val_eq, Nat.cast_ofNat] using hx

/-- The constant table is the table the builder computes. -/
@[step]
theorem crc_table_const_spec : CRC_TABLE ⦃ t => TabInv t 4096 ⦄ := by
  unfold CRC_TABLE
  exact table_spec

theorem crc32_correct (data : Aeneas.Std.Slice U8) :
    crc32_wide data ⦃ c => crc32_spec data.val c ⦄ := by
  unfold crc32_wide
  step as ⟨t, ht⟩
  split
  · -- at least sixteen bytes: the pipelined loop, the last chunk, then the byte tail
    step as ⟨b0, hb0⟩
    all_goals try scalar_tac
    have hb16 := chunk_bytes data.val 0 16 b0.val (by scalar_tac) (by simpa using hb0) (by scalar_tac)
    have hbl : b0.val.length = 16 := hb16.1
    have h0 : (0#usize).val = 0 := by scalar_tac
    step with (crc_rest_spec t b0 ht (by omega)) as ⟨rest, hrest⟩
    step with (word_at_spec b0 0#usize (by omega)) as ⟨w0, hw0⟩
    have h0 : PipeInv data 4294967295#u32 0#usize rest w0 := by
      refine ⟨by scalar_tac, by simp [reg], ?_, ?_⟩
      · rw [hrest]
        simpa using rest_chunk data.val b0.val 0 hb16.2
      · rw [hw0]
        simpa using wd_chunk data.val b0.val 0 0 hb16.2 (by omega)
    step with pipe_loop data t ht 4294967295#u32 0#usize rest w0 h0 as ⟨c, i1, rest1, w01, hinv⟩
    obtain ⟨hi, hc, hr, hw⟩ := hinv
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3⟩
    step as ⟨c1, hc1⟩
    step as ⟨i4, hi4⟩
    have h3 : i3.val = stp^[128] i2.val := by simpa using hi3
    have hreg : WordInv data c1 i4 := by
      refine ⟨by scalar_tac, ?_⟩
      rw [hi4, reg_sixteen', ← hc, ← hw, ← hr, hc1, UScalar.val_xor, h3, hi2, UScalar.val_xor]
    step with tail_loop data c1 i4 hreg as ⟨c2, hc2⟩
    exact crc_final data c2 hc2
  · step with tail_loop2 data 4294967295#u32 0#usize ⟨by scalar_tac, by simp [reg]⟩ as ⟨c, hc⟩
    exact crc_final data c hc

end Gzip.Proofs.Decode.CrcImpl
