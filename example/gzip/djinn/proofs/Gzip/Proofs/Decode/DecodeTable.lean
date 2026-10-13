import Gzip.Proofs.Decode.CodewordTable
import Gzip.Proofs.Decode.PeekFacts
import Gzip.Proofs.Decode.RevFacts
import Gzip.Proofs.Decode.BaseImpl
import Gzip.Vocab

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.BaseImpl Gzip.Proofs.Decode.PeekFacts Gzip.Proofs.Decode.TablesImpl Gzip.Proofs.Decode.RevFacts
open Djinn.Vocab

namespace Gzip.Proofs.Decode.DecodeTable

/-! ## the byte-reversal table and the fast reversal -/

/-- The first `k` entries of the byte table hold the reversed bytes. -/
def RevTab (r : List U8) (k : Nat) : Prop := ∀ j, j < k → (r[j]!).val = rev j 8

theorem rev_zero (n : Nat) : rev 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rev, ih]

/-- Two entries per step: entries `2 * j` and `2 * j + 1` come from entry `j`, which is below
`2 * j` once `j` is positive; entry 0 is zero from the start, so step 0 reads a right entry. -/
theorem rev_table_body (r : Array U8 256#usize) (j : Usize) (hj : j.val ≤ 128)
    (hrt : RevTab r.val (2 * j.val)) (hz : (r.val[0]!).val = 0) :
    rev_table_loop.body r j ⦃ z => match z with
      | .done v => RevTab v.val 256
      | .cont (v, j1) => (j1.val ≤ 128 ∧ RevTab v.val (2 * j1.val) ∧ (v.val[0]!).val = 0) ∧
          128 - j1.val < 128 - j.val ⦄ := by
  unfold rev_table_loop.body
  step*
  all_goals try scalar_tac
  · have hlt : j.val < 128 := by scalar_tac
    have hi : i = r.val[j.val]! := by
      rw [Djinn.Vocab.val_getElem! r.val j.val (by scalar_tac)]; exact i_post
    have hrj : (r.val[j.val]!).val = rev j.val 8 := by
      by_cases hj0 : j.val = 0
      · rw [hj0, hz, rev_zero]
      · exact hrt j.val (by omega)
    have hh : h.val = rev j.val 8 / 2 := by rw [h_post, hi, hrj]
    have hi1 : i1.val = 2 * j.val := by scalar_tac
    have hi3 : i3.val = 2 * j.val + 1 := by scalar_tac
    have hi2 : i2.val = rev j.val 8 / 2 + 128 := by rw [i2_post, hh]
    have hlen1 : (r.val.set i1.val h).length = 256 := by simp
    have hget : ∀ q, q < 256 → (a.val[q]!).val =
        if q = 2 * j.val + 1 then rev j.val 8 / 2 + 128
        else if q = 2 * j.val then rev j.val 8 / 2 else (r.val[q]!).val := by
      intro q hq
      rw [a_post, Array.set_val_eq, r1_post, Array.set_val_eq,
        Djinn.Vocab.getElem!_set _ _ _ _ (by rw [hlen1]; exact hq),
        Djinn.Vocab.getElem!_set _ _ _ _ (by scalar_tac)]
      rw [hi3, hi1]
      split_ifs with h1 h2 h3 h4 h5 h6 <;> first | rfl | omega | (rw [hi2]) | (rw [hh])
    refine ⟨?_, ?_, ?_, ?_⟩
    · show j1.val ≤ 128
      scalar_tac
    rotate_right
    · show 128 - j1.val < 128 - j.val
      scalar_tac
    · intro q hq
      rw [hget q (by scalar_tac)]
      split_ifs with h1 h2
      · rw [h1, rev_byte_step (2 * j.val + 1) (by omega)]
        have e1 : (2 * j.val + 1) / 2 = j.val := by omega
        have e2 : (2 * j.val + 1) % 2 = 1 := by omega
        simp only [e1, e2, Nat.mul_one]
      · rw [h2, rev_byte_step (2 * j.val) (by omega)]
        have e1 : (2 * j.val) / 2 = j.val := by omega
        have e2 : (2 * j.val) % 2 = 0 := by omega
        simp only [e1, e2, Nat.mul_zero, Nat.add_zero]
      · exact hrt q (by scalar_tac)
    · rw [hget 0 (by omega)]
      have hne : (0 : Nat) ≠ 2 * j.val + 1 := by omega
      rw [if_neg hne]
      by_cases hj0 : j.val = 0
      · rw [if_pos (by omega), hj0, rev_zero]
      · rw [if_neg (by omega)]
        exact hz
  all_goals try (intro q hq; exact hrt q (by scalar_tac))

@[step]
theorem rev_table_correct : rev_table ⦃ r => RevTab r.val 256 ⦄ := by
  unfold rev_table rev_table_loop
  apply loop.spec_decr_nat (fun (_, j) => 128 - j.val)
    (fun (v, j) => j.val ≤ 128 ∧ RevTab v.val (2 * j.val) ∧ (v.val[0]!).val = 0)
  · rintro ⟨v, j⟩ ⟨hj, hv, h0⟩
    apply WP.spec_mono (rev_table_body v j hj hv h0)
    intro z hz
    cases z <;> exact hz
  · have h256 : (256#usize).val = 256 := by scalar_tac
    have hm := getElem!_mem (List.replicate 256 0#u8) 0 (by rw [List.length_replicate]; omega)
    rw [List.mem_replicate] at hm
    refine ⟨by scalar_tac, ?_, ?_⟩
    · intro j hj
      have : j < 2 * (0#usize).val := hj
      scalar_tac
    · rw [Array.repeat_val, h256, hm.2]
      rfl

@[step]
theorem reverse_fast_correct (r : Array U8 256#usize) (code n : U32) (hr : RevTab r.val 256)
    (hn1 : 1 ≤ n.val) (hn : n.val ≤ 16) :
    reverse_fast r code n ⦃ v => v.val = rev code.val n.val ⦄ := by
  unfold reverse_fast
  step*
  all_goals try scalar_tac
  have hi1 : i1.val = code.val % 256 := by
    rw [i1_post, UScalar.cast_val_eq, i_post]
    apply Nat.mod_eq_of_lt
    scalar_tac
  have h2 : i2 = r.val[i1.val]! := by
    rw [Djinn.Vocab.val_getElem! r.val i1.val (by scalar_tac)]; exact i2_post
  have hi7 : i7.val = code.val / 256 % 256 := by
    rw [i7_post, UScalar.cast_val_eq, i6_post, i5_post]
    apply Nat.mod_eq_of_lt
    scalar_tac
  have h8 : i8 = r.val[i7.val]! := by
    rw [Djinn.Vocab.val_getElem! r.val i7.val (by scalar_tac)]; exact i8_post
  have h3 : i3.val = i2.val := by
    rw [i3_post, UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  have h9 : i9.val = i8.val := by
    rw [i9_post, UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  have hv : i10.val = 256 * rev (code.val % 256) 8 + rev (code.val / 256 % 256) 8 := by
    rw [i10_post, i4_post, h3, h9, h2, h8, hr _ (by omega), hr _ (by omega), hi1, hi7]
  have h11 : i11.val = 16 - n.val := by scalar_tac
  rw [v_post, Nat.shiftRight_eq_div_pow, hv, h11]
  exact (rev_of_bytes code.val n.val hn).symm

/-- The extra-bit count and base value a table entry carries for its symbol: those of distance
code `sym` in a distance table, those of length code `sym - 257` in a literal/length table. -/
def ExtraBase (isd : Bool) (sym extra base : Nat) : Prop :=
  if isd then
    (sym ≤ 29 → dextra_spec sym extra ∧ extra ≤ 13 ∧ dbase_spec sym base ∧ 1 ≤ base ∧ base ≤ 24577) ∧
      (29 < sym → base = 0)
  else
    (257 ≤ sym → sym ≤ 285 → lextra_spec ((sym : ℤ) - 257) extra ∧ extra ≤ 5 ∧
      lbase_spec ((sym : ℤ) - 257) base ∧ 3 ≤ base ∧ base ≤ 258) ∧
      (sym ≤ 256 ∨ 285 < sym → base = 0)

/-- The base value of an entry: bits 15..30 of a distance entry, bits 15..24 of a
literal/length entry (whose bits 24..28 hold a length code's codeword length). -/
def EntryBase (isd : Bool) (e : Nat) : Nat := if isd then e / 32768 else e / 32768 % 512

/-- The fields of a packed entry `e` of symbol `sym` whose codeword has `n` bits: the symbol in
bits 6..15, the bits the symbol takes (`n` plus its extra-bit count, which is zero for a
literal) in bits 0..6 (so bit 5 is clear: the count is below 32), and the base value above; a
length code's entry also has `n` in bits 24..28, and the other literal/length entries have no
bits above 14. -/
def EntryOf (isd : Bool) (sym n e : Nat) : Prop :=
  e / 64 % 512 = sym ∧ ∃ extra, e % 64 = n + extra ∧ ExtraBase isd sym extra (EntryBase isd e) ∧
    (isd = false → sym < 256 → extra = 0) ∧
    (isd = false → 257 ≤ sym → sym ≤ 285 → e / 16777216 = n) ∧
    (isd = false → (sym ≤ 256 ∨ 285 < sym) → e < 32768)

/-- Reversing `n` bits twice gives a number below `2 ^ n` back. -/
theorem rev_rev (n : Nat) : ∀ c, c < 2 ^ n → rev (rev c n) n = c := by
  induction n with
  | zero =>
    intro c hc
    have h0 : c = 0 := by simpa using hc
    simp [rev, h0]
  | succ n ih =>
    intro c hc
    have hdef : rev c (n + 1) = 2 * rev c n + c / 2 ^ n % 2 := rfl
    have hb : c / 2 ^ n % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rw [hdef, RevFacts.rev_succ_low]
    have h1 : (2 * rev c n + c / 2 ^ n % 2) % 2 = c / 2 ^ n % 2 := by omega
    have h2 : (2 * rev c n + c / 2 ^ n % 2) / 2 = rev c n := by omega
    rw [h1, h2]
    have hm : rev c n = rev (c % 2 ^ n) n := (rev_mod c n n (Nat.le_refl n)).symm
    rw [hm, ih (c % 2 ^ n) (Nat.mod_lt _ (by positivity))]
    have hlt : c / 2 ^ n < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_succ']
      exact hc
    have hq : c / 2 ^ n % 2 = c / 2 ^ n := Nat.mod_eq_of_lt hlt
    rw [hq]
    exact Nat.div_add_mod c (2 ^ n)

@[step]
theorem entry_extra_correct (sym : U32) (isd : Bool) :
    entry_extra sym isd ⦃ e => e.val ≤ 13 ∧
      (isd = true → sym.val ≤ 29 → dextra_spec sym.val e.val) ∧
      (isd = false → 257 ≤ sym.val → sym.val ≤ 285 →
        lextra_spec ((sym.val : ℤ) - 257) e.val ∧ e.val ≤ 5) ∧
      (isd = false → sym.val < 256 → e.val = 0) ⦄ := by
  unfold entry_extra
  step*

@[step]
theorem entry_base_correct (sym : U32) (isd : Bool) :
    entry_base sym isd ⦃ b => b.val ≤ 24577 ∧
      (isd = true → sym.val ≤ 29 → dbase_spec sym.val b.val ∧ 1 ≤ b.val) ∧
      (isd = false → 257 ≤ sym.val → sym.val ≤ 285 →
        lbase_spec ((sym.val : ℤ) - 257) b.val ∧ 3 ≤ b.val ∧ b.val ≤ 258) ∧
      (isd = true → 29 < sym.val → b.val = 0) ∧
      (isd = false → sym.val ≤ 256 ∨ 285 < sym.val → b.val = 0) ⦄ := by
  unfold entry_base
  step*
  all_goals try (refine ⟨?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp
  all_goals try (intros; omega)
  all_goals try (intros; assumption)
  all_goals try (intro _ _ _; constructor <;> first | assumption | omega)
  all_goals try (intro _ _; constructor <;> first | assumption | omega)

/-- The packed entry's fields from its parts: the extra-bit count `x`, the base `b` and the
length field `f` (the codeword length `n` shifted up 24 bits for a length code, else zero). -/
theorem entry_of_parts (sym n x b f : Nat) (isd : Bool) (hs : sym < 512) (hn : n < 16)
    (hx : x ≤ 13) (hb : b ≤ 24577)
    (hxd : isd = true → sym ≤ 29 → dextra_spec sym x)
    (hxl : isd = false → 257 ≤ sym → sym ≤ 285 → lextra_spec ((sym : ℤ) - 257) x ∧ x ≤ 5)
    (hx0 : isd = false → sym < 256 → x = 0)
    (hbd : isd = true → sym ≤ 29 → dbase_spec sym b ∧ 1 ≤ b)
    (hbl : isd = false → 257 ≤ sym → sym ≤ 285 → lbase_spec ((sym : ℤ) - 257) b ∧ 3 ≤ b ∧ b ≤ 258)
    (hbd0 : isd = true → 29 < sym → b = 0)
    (hbl0 : isd = false → sym ≤ 256 ∨ 285 < sym → b = 0)
    (hf1 : isd = false → 256 < sym → sym ≤ 285 → f = 16777216 * n)
    (hf0 : isd = true ∨ sym ≤ 256 ∨ 285 < sym → f = 0) :
    EntryOf isd sym n (n + x + 64 * sym + 32768 * b + f) := by
  -- the length field as a multiple of 2 ^ 24
  obtain ⟨m, hm, hm16, hmz⟩ : ∃ m, f = 16777216 * m ∧ m ≤ 15 ∧
      (¬ (isd = false ∧ 256 < sym ∧ sym ≤ 285) → m = 0) := by
    by_cases hc : isd = false ∧ 256 < sym ∧ sym ≤ 285
    · exact ⟨n, hf1 hc.1 hc.2.1 hc.2.2, by omega, fun h => (h hc).elim⟩
    · refine ⟨0, ?_, by omega, fun _ => rfl⟩
      rw [hf0]
      cases isd <;> simp_all <;> omega
  have hsmall : n + x < 64 := by omega
  have hsym64 : (n + x + 64 * sym + 32768 * b + f) / 64 % 512 = sym := by
    rw [hm, show n + x + 64 * sym + 32768 * b + 16777216 * m =
      (n + x) + 64 * (sym + 512 * (b + 512 * m)) by ring,
      Nat.add_mul_div_left _ _ (by norm_num : 0 < 64), Nat.div_eq_of_lt hsmall, Nat.zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  have hlow : (n + x + 64 * sym + 32768 * b + f) % 64 = n + x := by
    rw [hm, show n + x + 64 * sym + 32768 * b + 16777216 * m =
      (n + x) + 64 * (sym + 512 * (b + 512 * m)) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsmall]
  have hmid : n + x + 64 * sym < 32768 := by omega
  have hbase : (n + x + 64 * sym + 32768 * b + f) / 32768 = b + 512 * m := by
    rw [hm, show n + x + 64 * sym + 32768 * b + 16777216 * m =
      (n + x + 64 * sym) + 32768 * (b + 512 * m) by ring,
      Nat.add_mul_div_left _ _ (by norm_num : 0 < 32768), Nat.div_eq_of_lt hmid, Nat.zero_add]
  cases isd
  · by_cases hlen : 256 < sym ∧ sym ≤ 285
    · have hmn : m = n := by
        have hf := hf1 rfl hlen.1 hlen.2
        omega
      obtain ⟨hb1, hb3, hb258⟩ := hbl rfl (by omega) hlen.2
      have htop : (n + x + 64 * sym + 32768 * b + f) / 16777216 = n := by
        rw [hm, hmn, show n + x + 64 * sym + 32768 * b + 16777216 * n =
          (n + x + 64 * sym + 32768 * b) + 16777216 * n by ring,
          Nat.add_mul_div_left _ _ (by norm_num : 0 < 16777216), Nat.div_eq_of_lt (by omega),
          Nat.zero_add]
      refine ⟨hsym64, x, hlow, ?_, fun _ hlt => hx0 rfl hlt, fun _ _ _ => htop,
        fun _ hout => by omega⟩
      simp only [ExtraBase, EntryBase, Bool.false_eq_true, if_false]
      rw [hbase, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : b < 512)]
      refine ⟨fun _ _ => ?_, fun hout => by omega⟩
      obtain ⟨hl1, hl5⟩ := hxl rfl (by omega) hlen.2
      exact ⟨hl1, hl5, hb1, hb3, hb258⟩
    · have hb0 : b = 0 := hbl0 rfl (by omega)
      have hm0 : m = 0 := hmz (by simpa using hlen)
      refine ⟨hsym64, x, hlow, ?_, fun _ hlt => hx0 rfl hlt, fun _ h257 h285 => by omega,
        fun _ _ => by rw [hm, hm0, hb0]; omega⟩
      simp only [ExtraBase, EntryBase, Bool.false_eq_true, if_false]
      rw [hbase, hm0, hb0]
      exact ⟨fun h257 h285 => by omega, fun _ => rfl⟩
  · have hm0 : m = 0 := hmz (by simp)
    refine ⟨hsym64, x, hlow, ?_, fun h => by simp at h, fun h => by simp at h,
      fun h => by simp at h⟩
    simp only [ExtraBase, EntryBase, if_true]
    rw [hbase, hm0, Nat.mul_zero, Nat.add_zero]
    refine ⟨fun h29 => ?_, fun hout => hbd0 rfl hout⟩
    obtain ⟨hb1, hb2⟩ := hbd rfl h29
    exact ⟨hxd rfl h29, hx, hb1, hb2, hb⟩

/-! ## the symbol parts of the entries, computed once

`entry_tab` holds, for each symbol, its extra-bit count `x`, the symbol and its base `b` packed
as `x + 64 * sym + 32768 * b`; `pack_fast` adds the codeword length (and a length code's
length field) to give `pack_entry`'s value. -/

/-- The extra-bit count `x` and base `b` of a symbol, as `entry_extra` and `entry_base` give
them. -/
def Parts (isd : Bool) (sym x b : Nat) : Prop :=
  x ≤ 13 ∧ b ≤ 24577 ∧
  (isd = true → sym ≤ 29 → dextra_spec sym x) ∧
  (isd = false → 257 ≤ sym → sym ≤ 285 → lextra_spec ((sym : ℤ) - 257) x ∧ x ≤ 5) ∧
  (isd = false → sym < 256 → x = 0) ∧
  (isd = true → sym ≤ 29 → dbase_spec sym b ∧ 1 ≤ b) ∧
  (isd = false → 257 ≤ sym → sym ≤ 285 → lbase_spec ((sym : ℤ) - 257) b ∧ 3 ≤ b ∧ b ≤ 258) ∧
  (isd = true → 29 < sym → b = 0) ∧
  (isd = false → sym ≤ 256 ∨ 285 < sym → b = 0)

/-- The first `k` entries of the table of parts are right. -/
def TabParts (isd : Bool) (t : List U32) (k : Nat) : Prop :=
  ∀ s, s < k → ∃ x b, Parts isd s x b ∧ (t[s]!).val = x + 64 * s + 32768 * b

theorem entry_tab_body (isd : Bool) (t : Array U32 320#usize) (sym : U32)
    (hs : sym.val ≤ 320) (h : TabParts isd t.val sym.val) :
    entry_tab_loop.body isd t sym ⦃ z => match z with
    | .done v => TabParts isd v.val 320
    | .cont (v, s1) => (s1.val ≤ 320 ∧ TabParts isd v.val s1.val) ∧
        320 - s1.val < 320 - sym.val ⦄ := by
  unfold entry_tab_loop.body
  step*
  all_goals try scalar_tac
  all_goals try (
    have he : sym.val = 320 := by scalar_tac
    rw [← he]
    exact h)
  have hlt : sym.val < 320 := by scalar_tac
  have hx := x_post
  have hb := b_post
  have hi4 : i4.val = sym.val := by
    rw [i4_post, UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  have hval : i3.val = x.val + 64 * sym.val + 32768 * b.val := by scalar_tac
  have hs1 : sym1.val = sym.val + 1 := by scalar_tac
  refine ⟨by scalar_tac, ?_, by scalar_tac⟩
  intro s hs'
  rw [a_post, Array.set_val_eq, Djinn.Vocab.getElem!_set _ _ _ _ (by scalar_tac)]
  by_cases hss : s = i4.val
  · rw [if_pos hss, hss, hi4]
    exact ⟨x.val, b.val, ⟨hx, hb, x_post1, x_post2, x_post3, b_post1, b_post2, b_post3, b_post4⟩, hval⟩
  · rw [if_neg hss]
    exact h s (by omega)

theorem entry_tab_correct (isd : Bool) : entry_tab isd ⦃ t => TabParts isd t.val 320 ⦄ := by
  unfold entry_tab entry_tab_loop
  apply loop.spec_decr_nat (fun (_, s) => 320 - s.val)
    (fun (v, s) => s.val ≤ 320 ∧ TabParts isd v.val s.val)
  · rintro ⟨v, s⟩ ⟨hs, hv⟩
    apply WP.spec_mono (entry_tab_body isd v s hs hv)
    intro z hz
    cases z <;> exact hz
  · exact ⟨by scalar_tac, fun s hs => by simp at hs⟩

theorem lit_tab_spec : LIT_TAB ⦃ t => TabParts false t.val 320 ⦄ := by
  unfold LIT_TAB
  exact entry_tab_correct false

theorem dist_tab_spec : DIST_TAB ⦃ t => TabParts true t.val 320 ⦄ := by
  unfold DIST_TAB
  exact entry_tab_correct true

/-- The entry from the parts: `n` plus the symbol's part plus the length field. -/
theorem entry_of_part (isd : Bool) (sym n x b f : Nat) (hs : sym < 512) (hn : n < 16)
    (hp : Parts isd sym x b)
    (hf1 : isd = false → 256 < sym → sym ≤ 285 → f = 16777216 * n)
    (hf0 : isd = true ∨ sym ≤ 256 ∨ 285 < sym → f = 0) :
    EntryOf isd sym n (n + (x + 64 * sym + 32768 * b) + f) := by
  obtain ⟨hx, hb, hxd, hxl, hx0, hbd, hbl, hbd0, hbl0⟩ := hp
  have he : n + (x + 64 * sym + 32768 * b) + f = n + x + 64 * sym + 32768 * b + f := by ring
  rw [he]
  exact entry_of_parts sym n x b f isd hs hn hx hb hxd hxl hx0 hbd hbl hbd0 hbl0 hf1 hf0

@[step]
theorem pack_fast_correct (sym n : U32) (isd : Bool) (hs : sym.val < 320) (hn : n.val < 16) :
    pack_fast sym n isd ⦃ e => EntryOf isd sym.val n.val e.val ⦄ := by
  unfold pack_fast
  cases isd
  · -- a literal/length table: the length field, then the part
    simp only [Bool.false_eq_true, if_false]
    split <;> (try split) <;> step*
    all_goals try scalar_tac
    all_goals (
      step with lit_tab_spec as ⟨a, ha⟩
      step as ⟨ic, ic_post⟩
      have hi : ic.val = sym.val := by
        rw [ic_post, UScalar.cast_val_eq]
        apply Nat.mod_eq_of_lt
        scalar_tac
      clear ic_post
      obtain ⟨x, b, hp, hpart⟩ := ha sym.val hs
      have hxb : x ≤ 13 ∧ b ≤ 24577 := ⟨hp.1, hp.2.1⟩
      have hal : a.val.length = 320 := by scalar_tac
      step as ⟨part, part_post⟩
      all_goals try scalar_tac
      have hpe : part = a.val[sym.val]! := by
        rw [← hi, getElem!_pos a.val ic.val (by omega)]
        exact part_post
      have hpv : part.val = x + 64 * sym.val + 32768 * b := by
        rw [hpe]
        exact hpart
      step*
      all_goals try scalar_tac)
    all_goals first
      | (have he : e.val = n.val + (x + 64 * sym.val + 32768 * b) + 16777216 * n.val := by scalar_tac
         rw [he]
         apply entry_of_part false sym.val n.val x b _ (by omega) hn hp
         · intros; rfl
         · intro hc
           rcases hc with hc | hc | hc
           · simp at hc
           · scalar_tac
           · scalar_tac)
      | (have he : e.val = n.val + (x + 64 * sym.val + 32768 * b) + 0 := by scalar_tac
         rw [he]
         apply entry_of_part false sym.val n.val x b _ (by omega) hn hp
         · intro _ h1 h2; scalar_tac
         · intros; rfl)
  · -- a distance table
    simp only [eq_self_iff_true, if_true]
    step*
    step with dist_tab_spec as ⟨a, ha⟩
    step as ⟨ic, ic_post⟩
    have hi : ic.val = sym.val := by
      rw [ic_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
    clear ic_post
    obtain ⟨x, b, hp, hpart⟩ := ha sym.val hs
    have hxb : x ≤ 13 ∧ b ≤ 24577 := ⟨hp.1, hp.2.1⟩
    have hal : a.val.length = 320 := by scalar_tac
    step as ⟨part, part_post⟩
    all_goals try scalar_tac
    have hpe : part = a.val[sym.val]! := by
      rw [← hi, getElem!_pos a.val ic.val (by omega)]
      exact part_post
    have hpv : part.val = x + 64 * sym.val + 32768 * b := by
      rw [hpe]
      exact hpart
    step*
    all_goals try scalar_tac
    have he : e.val = n.val + (x + 64 * sym.val + 32768 * b) + 0 := by scalar_tac
    rw [he]
    apply entry_of_part true sym.val n.val x b _ (by omega) hn hp
    · intro h; simp at h
    · intros; rfl

/-- Every entry of the decoding table that names a symbol (in bits 5..14) is right: the
symbol's codeword has at most `bits` bits and is the entry's index, read first bit lowest, and
the entry's other fields are the symbol's bit count and base value. Only the first `2 ^ bits`
entries are ever looked up, so only they are constrained; the distance table keeps its
symbols' codeword lengths in the others. -/
-- `Named`: every used entry is the sentinel (of symbol 320) or names a symbol of the table.
def Named (lens : List U8) (table : List U32) (bits : Nat) : Prop :=
  ∀ idx, idx < 2 ^ bits → table[idx]! = 20480#u32 ∨ (table[idx]!).val / 64 % 512 < lens.length

def Hints (lens : List U8) (codes table : List U32) (isd : Bool) (bits : Nat) : Prop :=
  table.length = 2048 ∧ (∀ idx, idx < 2 ^ bits → (table[idx]!).val / 64 % 512 < lens.length →
    1 ≤ (lens[(table[idx]!).val / 64 % 512]!).val ∧ (lens[(table[idx]!).val / 64 % 512]!).val ≤ bits ∧
    rev idx (lens[(table[idx]!).val / 64 % 512]!).val = (codes[(table[idx]!).val / 64 % 512]!).val ∧
    EntryOf isd ((table[idx]!).val / 64 % 512) (lens[(table[idx]!).val / 64 % 512]!).val (table[idx]!).val) ∧
  Named lens table bits

theorem sentinel_sym : (20480#u32).val / 64 % 512 = 320 := by simp

/-- The used part of a table of `bits` bits fits in it. -/
theorem pow_bits_le (bits : Nat) (hbits : bits ≤ 11) : 2 ^ bits ≤ 2048 := calc
  _ ≤ 2 ^ 11 := Nat.pow_le_pow_right (by omega) hbits
  _ = _ := by norm_num

/-- Two tables that agree on their used entries satisfy the same `Hints`. -/
theorem hints_of_agree (lens : List U8) (codes table v : List U32) (isd : Bool) (bits : Nat)
    (ht : Hints lens codes table isd bits) (hlen : v.length = 2048)
    (hagree : ∀ idx, idx < 2 ^ bits → v[idx]! = table[idx]!) : Hints lens codes v isd bits := by
  refine ⟨hlen, ?_, ?_⟩
  · intro idx hidx hlt
    rw [hagree idx hidx] at hlt ⊢
    exact ht.2.1 idx hidx hlt
  · intro idx hidx
    rw [hagree idx hidx]
    exact ht.2.2 idx hidx

/-- A table entry other than the sentinel names a symbol of the table. -/
theorem named_of_ne (lens : List U8) (codes table : List U32) (isd : Bool) (bits : Nat)
    (ht : Hints lens codes table isd bits) (idx : Nat) (hidx : idx < 2 ^ bits)
    (hne : table[idx]! ≠ 20480#u32) : (table[idx]!).val / 64 % 512 < lens.length := by
  rcases ht.2.2 idx hidx with h | h
  · exact absurd h hne
  · exact h

/-- A table entry that names a symbol other than the sentinel's names one of the table. -/
theorem named_symbol (lens : List U8) (codes table : List U32) (isd : Bool) (bits : Nat)
    (ht : Hints lens codes table isd bits) (idx : Nat) (hidx : idx < 2 ^ bits)
    (hne : (table[idx]!).val / 64 % 512 ≠ 320) : (table[idx]!).val / 64 % 512 < lens.length := by
  apply named_of_ne lens codes table isd bits ht idx hidx
  intro h
  apply hne
  rw [h]
  exact sentinel_sym

theorem reverse_body (code n rv c k : U32) (hn : n.val ≤ 16)
    (hk : k.val ≤ n.val) (hr : rv.val = rev code.val k.val) (hc : c.val = code.val / 2 ^ k.val) :
    reverse_bits_loop.body n rv c k ⦃ z => match z with
      | .done v => v.val = rev code.val n.val
      | .cont (rv1, c1, k1) => (k1.val ≤ n.val ∧ rv1.val = rev code.val k1.val ∧
          c1.val = code.val / 2 ^ k1.val) ∧ n.val - k1.val < n.val - k.val ⦄ := by
  unfold reverse_bits_loop.body
  have hlt := rev_lt code.val k.val
  have hpow : 2 ^ k.val ≤ 65536 := pow_two_le k.val (by omega)
  step*
  refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
  · rw [k1_post]
    simp only [rev]
    rw [← hr, ← hc]
    scalar_tac
  · rw [k1_post, pow_succ, ← Nat.div_div_eq_div_mul, ← hc]
    scalar_tac

@[step]
theorem reverse_bits_correct (code n : U32) (hn : n.val ≤ 16) :
    reverse_bits code n ⦃ v => v.val = rev code.val n.val ⦄ := by
  unfold reverse_bits reverse_bits_loop
  apply loop.spec_decr_nat (fun (_, _, k) => n.val - k.val)
    (fun (rv, c, k) => k.val ≤ n.val ∧ rv.val = rev code.val k.val ∧ c.val = code.val / 2 ^ k.val)
  · rintro ⟨rv, c, k⟩ ⟨hk, hr, hc⟩
    apply WP.spec_mono (reverse_body code n rv c k hn hk hr hc)
    intro z hz
    cases z <;> exact hz
  · exact ⟨by scalar_tac, by simp [rev], by simp⟩

/-- What the filling loop leaves: an entry is as before or is `entry`, the latter only at the
indices congruent to the first one. -/
def Filled (table0 : List U32) (entry : U32) (step k0 : Nat) (v : List U32) : Prop :=
  v.length = 2048 ∧ ∀ idx, idx < 2048 →
    v[idx]! = table0[idx]! ∨ (v[idx]! = entry ∧ idx % step = k0 % step)

/-- Writing `entry` at an index congruent to the first one keeps `Filled`. -/
theorem filled_set (table0 : List U32) (entry : U32) (step k0 : Nat) (v : Array U32 2048#usize)
    (idx : Usize) (hv : Filled table0 entry step k0 v.val) (hidx : idx.val % step = k0 % step)
    (hlt : idx.val < 2048) : Filled table0 entry step k0 (v.set idx entry).val := by
  obtain ⟨hlen, hent⟩ := hv
  refine ⟨by rw [Array.set_val_eq]; simp [hlen], ?_⟩
  intro j hj
  rw [Array.set_val_eq, getElem!_set _ _ _ _ (by omega)]
  split_ifs with he
  · right
    exact ⟨rfl, by rw [he]; exact hidx⟩
  · exact hent j hj

theorem hints_filled (lens : List U8) (codes table v : List U32) (sym k : Nat) (entry : U32)
    (isd : Bool) (bits : Nat) (hb : bits ≤ 11)
    (hs : sym < lens.length) (hn1 : 1 ≤ (lens[sym]!).val) (hn10 : (lens[sym]!).val ≤ bits)
    (hk : rev k (lens[sym]!).val = (codes[sym]!).val)
    (hent : EntryOf isd sym (lens[sym]!).val entry.val)
    (ht : Hints lens codes table isd bits)
    (hv : Filled table entry (2 ^ (lens[sym]!).val) k v) : Hints lens codes v isd bits := by
  have hpb := pow_bits_le bits hb
  refine ⟨hv.1, ?_, ?_⟩
  · intro idx hidx hlt
    rcases hv.2 idx (by omega) with he | ⟨he, hmod⟩
    · rw [he] at hlt ⊢
      exact ht.2.1 idx hidx hlt
    · rw [he] at hlt ⊢
      rw [hent.1] at hlt ⊢
      refine ⟨hn1, hn10, ?_, hent⟩
      rw [← rev_mod idx _ _ (Nat.le_refl _), hmod, rev_mod k _ _ (Nat.le_refl _)]
      exact hk
  · intro idx hidx
    rcases hv.2 idx (by omega) with he | ⟨he, _⟩
    · rw [he]
      exact ht.2.2 idx hidx
    · rw [he, hent.1]
      exact Or.inr hs

/-! ## the table built by levels

The symbols come grouped by codeword length (`sorted`, with the group of length `n` at
`start[n] .. start[n + 1]`). Level `n` writes one entry per code of `n` bits, at its reversed
codeword, which is below `2 ^ n`; then the first `2 ^ n` entries are doubled to `2 ^ (n + 1)`.
An entry of a code of at most `n` bits depends only on the index's low `n` bits, so the doubled
entries are right too. The grouping is only a hint: a symbol is used only where its length is
checked to be the level's, so nothing about `sorted` or `start` is assumed. -/

/-- Every used entry that names a symbol names one whose codeword has at most `m` bits. -/
def Below (lens : List U8) (table : List U32) (bits m : Nat) : Prop :=
  ∀ idx, idx < 2 ^ bits → table[idx]! = 20480#u32 ∨ (lens[(table[idx]!).val / 64 % 512]!).val ≤ m

theorem below_mono (lens : List U8) (table : List U32) (bits m m' : Nat)
    (h : Below lens table bits m) (hm : m ≤ m') : Below lens table bits m' := by
  intro idx hidx
  rcases h idx hidx with h | h
  · exact Or.inl h
  · exact Or.inr (_root_.le_trans h hm)

/-- The fresh table, all entries of symbol 320, names no symbol (the tables have at most 320). -/
theorem hints_fresh (lens : List U8) (codes : List U32) (isd : Bool) (bits : Nat) (hb : bits ≤ 11)
    (hl : lens.length ≤ 320) :
    Hints lens codes (Array.repeat 2048#usize 20480#u32).val isd bits := by
  have h2048 : (2048#usize).val = 2048 := by scalar_tac
  have hpb := pow_bits_le bits hb
  rw [Array.repeat_val, h2048]
  have hent : ∀ idx, idx < 2048 → (List.replicate 2048 20480#u32)[idx]! = 20480#u32 := by
    intro idx hidx
    have hm := getElem!_mem (List.replicate 2048 20480#u32) idx
      (by rw [List.length_replicate]; exact hidx)
    rw [List.mem_replicate] at hm
    exact hm.2
  refine ⟨List.length_replicate, ?_, ?_⟩
  · intro idx hidx hlt
    rw [hent idx (by omega), sentinel_sym] at hlt
    omega
  · intro idx hidx
    exact Or.inl (hent idx (by omega))

theorem below_fresh (lens : List U8) (bits : Nat) (hb : bits ≤ 11) :
    Below lens (Array.repeat 2048#usize 20480#u32).val bits 0 := by
  have h2048 : (2048#usize).val = 2048 := by scalar_tac
  have hpb := pow_bits_le bits hb
  intro idx hidx
  left
  rw [Array.repeat_val, h2048]
  have hm := getElem!_mem (List.replicate 2048 20480#u32) idx
    (by rw [List.length_replicate]; omega)
  rw [List.mem_replicate] at hm
  exact hm.2

/-- Writing the entry of a symbol whose codeword has `n` bits at its reversed codeword keeps
`Hints` and `Below n`. -/
theorem hints_write (lens : List U8) (codes : List U32) (table : Array U32 2048#usize)
    (isd : Bool) (bits n sym : Nat) (k : Usize) (entry : U32) (hb : bits ≤ 11)
    (hs : sym < lens.length) (hn : (lens[sym]!).val = n) (hn1 : 1 ≤ n) (hnb : n ≤ bits)
    (hk : rev k.val n = (codes[sym]!).val) (hent : EntryOf isd sym n entry.val)
    (hklt : k.val < 2048)
    (ht : Hints lens codes table.val isd bits) (hbl : Below lens table.val bits n) :
    Hints lens codes (table.set k entry).val isd bits ∧ Below lens (table.set k entry).val bits n := by
  have hlen : table.val.length = 2048 := ht.1
  have hpb := pow_bits_le bits hb
  have hfill : Filled table.val entry (2 ^ (lens[sym]!).val) k.val (table.set k entry).val := by
    refine ⟨by rw [Array.set_val_eq]; simp [hlen], ?_⟩
    intro idx hidx
    rw [Array.set_val_eq, Djinn.Vocab.getElem!_set _ _ _ _ (by omega)]
    split_ifs with he
    · exact Or.inr ⟨rfl, by rw [he]⟩
    · exact Or.inl rfl
  refine ⟨hints_filled lens codes table.val _ sym k.val entry isd bits hb hs (by omega) (by omega)
    (by rw [hn]; exact hk) (by rw [hn]; exact hent) ht hfill, ?_⟩
  intro idx hidx
  rw [Array.set_val_eq, Djinn.Vocab.getElem!_set _ _ _ _ (by omega)]
  split_ifs with he
  · right
    rw [hent.1]
    omega
  · exact hbl idx hidx

/-- Wraps a fact that `scalar_tac` must not rewrite with. -/
def Keep (p : Prop) : Prop := p

theorem Keep.intro {p : Prop} (h : p) : Keep p := h

theorem Keep.out {p : Prop} (h : Keep p) : p := h

theorem shift_usize_one' (n : Nat) (hn : n ≤ 16) :
    1 <<< n % Usize.size = 2 ^ n := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt]
  have hb := pow_two_le n hn
  scalar_tac

-- One symbol of a level: its entry is written when its length is the level's.
set_option maxHeartbeats 4000000 in
theorem sym_body (lens : Aeneas.Std.Slice U8) (codes : Aeneas.Std.Slice U32)
    (sorted : Array U16 512#usize) (isd : Bool) (r : Array U8 256#usize) (n step : U32)
    (end_ : Usize) (table : Array U32 2048#usize) (j : Usize) (bits : Nat)
    (hl : lens.val.length ≤ 320) (hc : codes.val.length = lens.val.length) (hb : bits ≤ 11)
    (hn1 : 1 ≤ n.val) (hnb : n.val ≤ bits) (hstep : step.val = 2 ^ n.val) (hr : RevTab r.val 256)
    (ht : Hints lens.val codes.val table.val isd bits) (hbl : Below lens.val table.val bits n.val) :
    decode_table_loop0_loop0.body lens codes sorted isd r n step end_ table j ⦃ z => match z with
    | .done v => Hints lens.val codes.val v.val isd bits ∧ Below lens.val v.val bits n.val
    | .cont (v, j1) => (Hints lens.val codes.val v.val isd bits ∧ Below lens.val v.val bits n.val) ∧
        end_.val - j1.val < end_.val - j.val ⦄ := by
  have hn11 : n.val ≤ 11 := by omega
  unfold decode_table_loop0_loop0.body
  step*
  all_goals try scalar_tac
  all_goals try exact ⟨ht, hbl⟩
  -- the loop runs: the symbol, then the nested tests
  have hsym : sym.val = i1.val := by
    rw [sym_post, UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  clear sym_post
  split
  · split
    · step as ⟨i4, i4_post⟩
      step as ⟨i5, i5_post⟩
      split
      · rename_i hi5n
        have hslen : sym.val < lens.val.length := by scalar_tac
        have hclen : sym.val < codes.val.length := by scalar_tac
        have hi4 : i4 = lens.val[sym.val]! := by
          rw [getElem!_pos lens.val sym.val hslen]; exact i4_post
        have hi5 : i5.val = i4.val := by
          rw [i5_post]; exact Gzip.Proofs.Decode.ReaderImpl.cast_byte i4
        have hlsym : (lens.val[sym.val]!).val = n.val := by rw [← hi4, ← hi5, hi5n]
        step as ⟨code, code_post⟩
        split
        · -- the write
          have hcodelt : code.val < 2 ^ n.val := by rw [← hstep]; scalar_tac
          have hcode' : code = codes.val[sym.val]! := by
            rw [getElem!_pos codes.val sym.val hclen]; exact code_post
          step with (reverse_fast_correct r code n hr hn1 (by omega)) as ⟨rev, rev_post⟩
          step as ⟨i6, i6_post⟩
          have hi6 : i6.val = sym.val := by
            rw [i6_post, UScalar.cast_val_eq]
            apply Nat.mod_eq_of_lt
            scalar_tac
          step with (pack_fast_correct i6 n isd (by omega) (by omega)) as ⟨i7, i7_post⟩
          step as ⟨i8, i8_post⟩
          have hi8 : i8.val = rev.val := by
            rw [i8_post, UScalar.cast_val_eq]
            apply Nat.mod_eq_of_lt
            scalar_tac
          clear i8_post
          have hrevlt : rev.val < 2048 := by
            rw [rev_post]
            exact _root_.lt_of_lt_of_le (rev_lt code.val n.val)
              (_root_.le_trans (Nat.pow_le_pow_right (by omega) hn11) (by norm_num))
          step as ⟨i9, i9_post⟩
          have hi9 : i9.val = rev.val := by
            rw [i9_post, hi8]
            exact Nat.mod_eq_of_lt hrevlt
          step as ⟨table1, table1_post⟩
          step as ⟨j1, j1_post⟩
          have hw := hints_write lens.val codes.val table isd bits n.val sym.val i9 i7 hb hslen hlsym
            hn1 hnb (by rw [hi9, rev_post, ← hcode']; exact rev_rev n.val code.val hcodelt)
            (by rw [← hi6]; exact i7_post) (by omega) ht hbl
          rw [← table1_post] at hw
          have hw1 := hw.1
          have hw2 := hw.2
          step*
          all_goals exact ⟨hw1, hw2, by scalar_tac⟩
        · step*
          all_goals exact ⟨ht, hbl, by scalar_tac⟩
      · step*
        all_goals exact ⟨ht, hbl, by scalar_tac⟩
    · step*
      all_goals exact ⟨ht, hbl, by scalar_tac⟩
  · step*
    all_goals exact ⟨ht, hbl, by scalar_tac⟩

theorem sym_loop_correct (lens : Aeneas.Std.Slice U8) (codes : Aeneas.Std.Slice U32)
    (sorted : Array U16 512#usize) (isd : Bool) (r : Array U8 256#usize) (n step : U32)
    (end_ : Usize) (table : Array U32 2048#usize) (j : Usize) (bits : Nat)
    (hl : lens.val.length ≤ 320) (hc : codes.val.length = lens.val.length) (hb : bits ≤ 11)
    (hn1 : 1 ≤ n.val) (hnb : n.val ≤ bits) (hstep : step.val = 2 ^ n.val) (hr : RevTab r.val 256)
    (ht : Hints lens.val codes.val table.val isd bits) (hbl : Below lens.val table.val bits n.val) :
    decode_table_loop0_loop0 lens codes sorted isd r table n step end_ j ⦃ v =>
      Hints lens.val codes.val v.val isd bits ∧ Below lens.val v.val bits n.val ⦄ := by
  unfold decode_table_loop0_loop0
  apply loop.spec_decr_nat (fun (_, j) => end_.val - j.val)
    (fun (v, _) => Hints lens.val codes.val v.val isd bits ∧ Below lens.val v.val bits n.val)
  · rintro ⟨v, j⟩ ⟨hv, hbv⟩
    apply WP.spec_mono (sym_body lens codes sorted isd r n step end_ v j bits hl hc hb hn1 hnb hstep hr hv hbv)
    intro z hz
    cases z <;> exact hz
  · exact ⟨ht, hbl⟩

/-- What the doubling loop has done after `k` steps: entries `st .. st + k` are copies of the
entries `k` below them, the rest is as before. -/
def Copied (t0 : List U32) (st k : Nat) (v : List U32) : Prop :=
  v.length = 2048 ∧ ∀ idx, idx < 2048 →
    v[idx]! = if st ≤ idx ∧ idx < st + k then t0[idx - st]! else t0[idx]!

theorem copy_body (t0 : List U32) (st : Usize) (table : Array U32 2048#usize) (k : Usize)
    (hst : 2 * st.val ≤ 2048) (hk : k.val ≤ st.val) (h : Copied t0 st.val k.val table.val) :
    decode_table_loop0_loop1.body st table k ⦃ z => match z with
    | .done v => Copied t0 st.val st.val v.val
    | .cont (v, k1) => (k1.val ≤ st.val ∧ Copied t0 st.val k1.val v.val) ∧
        st.val - k1.val < st.val - k.val ⦄ := by
  have hlen : table.val.length = 2048 := h.1
  unfold decode_table_loop0_loop1.body
  step*
  all_goals try scalar_tac
  have hklt : k.val < st.val := by scalar_tac
  have hi : i = table.val[k.val]! := by
    rw [getElem!_pos table.val k.val (by omega)]; exact i_post
  have hi1 : i1.val = st.val + k.val := by scalar_tac
  have hk1 : k1.val = k.val + 1 := by scalar_tac
  refine ⟨by omega, ⟨?_, ?_⟩, by omega⟩
  · rw [a_post, Array.set_val_eq]
    simp [hlen]
  · intro idx hidx
    rw [a_post, Array.set_val_eq, Djinn.Vocab.getElem!_set _ _ _ _ (by omega), hi1, hk1]
    by_cases he : idx = st.val + k.val
    · rw [if_pos he, if_pos (by omega), he, Nat.add_sub_cancel_left, hi, h.2 k.val (by omega),
        if_neg (by omega)]
    · rw [if_neg he, h.2 idx hidx]
      by_cases hin : st.val ≤ idx ∧ idx < st.val + k.val
      · rw [if_pos hin, if_pos (by omega)]
      · rw [if_neg hin, if_neg (by omega)]

theorem copy_loop_correct (table : Array U32 2048#usize) (st : Usize) (hst : 2 * st.val ≤ 2048)
    (hlen : table.val.length = 2048) :
    decode_table_loop0_loop1 table st 0#usize ⦃ v => Copied table.val st.val st.val v.val ⦄ := by
  unfold decode_table_loop0_loop1
  apply loop.spec_decr_nat (fun (_, k) => st.val - k.val)
    (fun (v, k) => k.val ≤ st.val ∧ Copied table.val st.val k.val v.val)
  · rintro ⟨v, k⟩ ⟨hk, hv⟩
    apply WP.spec_mono (copy_body table.val st v k hst hk hv)
    intro z hz
    cases z <;> exact hz
  · refine ⟨by scalar_tac, hlen, fun idx hidx => ?_⟩
    rw [if_neg (by scalar_tac)]

/-- Doubling the first `2 ^ n` entries keeps `Hints` and `Below n`: an entry of a code of at
most `n` bits is right at every index with the same low `n` bits. -/
theorem hints_copy (lens : List U8) (codes table v : List U32) (isd : Bool) (bits n : Nat)
    (hb : bits ≤ 11) (hl : lens.length ≤ 320) (h2 : 2 * 2 ^ n ≤ 2 ^ bits)
    (ht : Hints lens codes table isd bits) (hbl : Below lens table bits n)
    (hv : Copied table (2 ^ n) (2 ^ n) v) :
    Hints lens codes v isd bits ∧ Below lens v bits n := by
  have hpb := pow_bits_le bits hb
  have hentry : ∀ idx, idx < 2 ^ bits → ∃ src, src < 2 ^ bits ∧ v[idx]! = table[src]! ∧
      ∀ m, m ≤ n → rev idx m = rev src m := by
    intro idx hidx
    rw [hv.2 idx (by omega)]
    split_ifs with hin
    · refine ⟨idx - 2 ^ n, by omega, rfl, ?_⟩
      intro m hm
      rw [← rev_mod idx n m hm, ← rev_mod (idx - 2 ^ n) n m hm]
      congr 1
      calc idx % 2 ^ n = (idx - 2 ^ n + 2 ^ n) % 2 ^ n := by congr 1; omega
        _ = (idx - 2 ^ n) % 2 ^ n := Nat.add_mod_right _ _
    · exact ⟨idx, hidx, rfl, fun _ _ => rfl⟩
  refine ⟨⟨hv.1, ?_, ?_⟩, ?_⟩
  · intro idx hidx hlt
    obtain ⟨src, hsrc, he, hrev⟩ := hentry idx hidx
    rw [he] at hlt ⊢
    obtain ⟨h1, h2', h3, h4⟩ := ht.2.1 src hsrc hlt
    refine ⟨h1, h2', ?_, h4⟩
    rw [hrev _ ?_]
    · exact h3
    · rcases hbl src hsrc with hs | hs
      · exfalso
        rw [hs, sentinel_sym] at hlt
        omega
      · exact hs
  · intro idx hidx
    obtain ⟨src, hsrc, he, _⟩ := hentry idx hidx
    rw [he]
    exact ht.2.2 src hsrc
  · intro idx hidx
    obtain ⟨src, hsrc, he, _⟩ := hentry idx hidx
    rw [he]
    exact hbl src hsrc

-- One level: the entries of its codes, then the doubling.
set_option maxHeartbeats 4000000 in
theorem level_body (lens : Aeneas.Std.Slice U8) (codes : Aeneas.Std.Slice U32)
    (sorted : Array U16 512#usize) (start : Array Usize 17#usize) (isd : Bool) (bits : U32)
    (r : Array U8 256#usize) (size : Usize) (table : Array U32 2048#usize) (n : U32)
    (hl : lens.val.length ≤ 320) (hc : codes.val.length = lens.val.length)
    (hbits : bits.val ≤ 11) (hsize : size.val = 2 ^ bits.val) (hr : RevTab r.val 256)
    (hn1 : 1 ≤ n.val) (hn12 : n.val ≤ 12)
    (ht : Hints lens.val codes.val table.val isd bits.val)
    (hbl : Below lens.val table.val bits.val (n.val - 1)) :
    decode_table_loop0.body lens codes sorted start isd bits r size table n ⦃ z => match z with
    | .done v => Hints lens.val codes.val v.val isd bits.val
    | .cont (v, n1) => (1 ≤ n1.val ∧ n1.val ≤ 12 ∧ Hints lens.val codes.val v.val isd bits.val ∧
        Below lens.val v.val bits.val (n1.val - 1)) ∧ 12 - n1.val < 12 - n.val ⦄ := by
  have hlen : table.val.length = 2048 := ht.1
  unfold decode_table_loop0.body
  step*
  all_goals try scalar_tac
  all_goals try exact ht
  have hnb : n.val ≤ bits.val := by scalar_tac
  have hn11 : n.val ≤ 11 := by scalar_tac
  have hstep : step.val = 2 ^ n.val := by rw [step_post, shift_one _ (by omega)]
  have hpow : 2 ^ n.val ≤ 2048 := calc
    _ ≤ 2 ^ 11 := Nat.pow_le_pow_right (by omega) hn11
    _ = _ := by norm_num
  have hst : st.val = 2 ^ n.val := by
    rw [st_post, UScalar.cast_val_eq, hstep]
    apply Nat.mod_eq_of_lt
    scalar_tac
  clear st_post
  have hbl' : Below lens.val table.val bits.val n.val := below_mono _ _ _ _ _ hbl (by omega)
  step with (sym_loop_correct lens codes sorted isd r n step «end» table j bits.val hl hc hbits hn1 hnb
    hstep hr ht hbl') as ⟨table1, ht1, hb1⟩
  have hl1 : table1.val.length = 2048 := ht1.1
  have hpb := pow_bits_le bits.val hbits
  step*
  all_goals try scalar_tac
  · -- the doubling
    have h2 : 2 * 2 ^ n.val ≤ 2 ^ bits.val := by rw [← hst, ← i3_post, ← hsize]; scalar_tac
    step with (copy_loop_correct table1 st (by scalar_tac) hl1) as ⟨table2, hcopy⟩
    rw [hst] at hcopy
    have hw := hints_copy lens.val codes.val table1.val table2.val isd bits.val n.val hbits hl h2 ht1 hb1 hcopy
    have hw1 := hw.1
    have hw2 := hw.2
    step as ⟨n1, n1_post⟩
    have hn1' : n1.val - 1 = n.val := by scalar_tac
    step*
    all_goals (rw [hn1']; exact ⟨by scalar_tac, by scalar_tac, hw1, hw2, by scalar_tac⟩)
  · -- no room to double: the level is the last used one
    have hn1' : n1.val - 1 = n.val := by scalar_tac
    rw [hn1']
    exact ⟨by scalar_tac, by scalar_tac, ht1, hb1, by scalar_tac⟩

theorem level_loop_correct (lens : Aeneas.Std.Slice U8) (codes : Aeneas.Std.Slice U32)
    (sorted : Array U16 512#usize) (start : Array Usize 17#usize) (isd : Bool) (bits : U32)
    (r : Array U8 256#usize) (table : Array U32 2048#usize) (size : Usize) (n : U32)
    (hl : lens.val.length ≤ 320) (hc : codes.val.length = lens.val.length)
    (hbits : bits.val ≤ 11) (hsize : size.val = 2 ^ bits.val) (hr : RevTab r.val 256)
    (hn1 : 1 ≤ n.val) (hn12 : n.val ≤ 12)
    (ht : Hints lens.val codes.val table.val isd bits.val)
    (hbl : Below lens.val table.val bits.val (n.val - 1)) :
    decode_table_loop0 lens codes sorted start isd bits r table size n ⦃ v =>
      Hints lens.val codes.val v.val isd bits.val ⦄ := by
  unfold decode_table_loop0
  apply loop.spec_decr_nat (fun (_, n) => 12 - n.val)
    (fun (v, n) => 1 ≤ n.val ∧ n.val ≤ 12 ∧ Hints lens.val codes.val v.val isd bits.val ∧
      Below lens.val v.val bits.val (n.val - 1))
  · rintro ⟨v, m⟩ ⟨hm1, hm12, hv, hbv⟩
    apply WP.spec_mono (level_body lens codes sorted start isd bits r size v m hl hc hbits hsize hr
      hm1 hm12 hv hbv)
    intro z hz
    cases z <;> exact hz
  · exact ⟨hn1, hn12, ht, hbl⟩

@[step]
theorem decode_table_correct (lens : Aeneas.Std.Slice U8) (codes : Aeneas.Std.Slice U32)
    (sorted : Array U16 512#usize) (start : Array Usize 17#usize)
    (isd : Bool) (bits : U32) (r : Array U8 256#usize)
    (hl : lens.val.length ≤ 320) (hc : codes.val.length = lens.val.length)
    (hbits : bits.val ≤ 11) (hr : RevTab r.val 256) :
    decode_table lens codes sorted start isd bits r ⦃ v => Hints lens.val codes.val v.val isd bits.val ⦄ := by
  unfold decode_table
  split
  · step as ⟨size, size_post⟩
    · rcases System.Platform.numBits_eq with hbits' | hbits' <;> rw [hbits'] <;> omega
    have hsize : size.val = 2 ^ bits.val := by
      rw [size_post]
      exact shift_usize_one' bits.val (_root_.le_trans hbits (by norm_num))
    clear size_post
    exact level_loop_correct lens codes sorted start isd bits r _ size 1#u32 hl hc hbits hsize hr
      (by scalar_tac) (by scalar_tac) (hints_fresh lens.val codes.val isd bits.val hbits hl)
      (by
        have h0 : (1#u32).val - 1 = 0 := by scalar_tac
        rw [h0]
        exact below_fresh lens.val bits.val hbits)
  · exfalso
    scalar_tac

/-! ## the code lengths as an array indexed by any nine-bit symbol -/

/-- `a` agrees with `lens` on the symbols of the table. -/
def LensArr (lens a : List U8) : Prop := ∀ j, j < lens.length → a[j]! = lens[j]!

theorem lens_body (lens : Aeneas.Std.Slice U8) (a : Array U8 512#usize) (i : Usize)
    (hl : lens.val.length ≤ 320) (hi : i.val ≤ lens.val.length)
    (h : ∀ j, j < i.val → a.val[j]! = lens.val[j]!) :
    lens_array_loop.body lens a i ⦃ r => match r with
    | .done v => LensArr lens.val v.val
    | .cont (v, j) => (j.val ≤ lens.val.length ∧ ∀ q, q < j.val → v.val[q]! = lens.val[q]!) ∧
        lens.val.length - j.val < lens.val.length - i.val ⦄ := by
  unfold lens_array_loop.body
  step*
  all_goals try scalar_tac
  · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    intro q hq
    have hql : q < a.val.length := by scalar_tac
    rw [a1_post, Array.set_val_eq, Djinn.Vocab.getElem!_set _ _ _ _ hql]
    by_cases hqi : q = i.val
    · rw [if_pos hqi, hqi, getElem!_pos lens.val i.val (by scalar_tac)]
      exact i2_post
    · rw [if_neg hqi]
      exact h q (by omega)
  · intro j hj
    exact h j (by scalar_tac)

@[step]
theorem lens_array_correct (lens : Aeneas.Std.Slice U8) (hl : lens.val.length ≤ 320) :
    lens_array lens ⦃ a => LensArr lens.val a.val ⦄ := by
  unfold lens_array lens_array_loop
  apply loop.spec_decr_nat (fun (_, i) => lens.val.length - i.val)
    (fun (v, i) => i.val ≤ lens.val.length ∧ ∀ q, q < i.val → v.val[q]! = lens.val[q]!)
  · rintro ⟨v, j⟩ ⟨hj, hv⟩
    apply WP.spec_mono (lens_body lens v j hl hj hv)
    intro r hr
    cases r <;> exact hr
  · exact ⟨by scalar_tac, fun q hq => by simp at hq⟩

/-! ## the distance codeword lengths indexed like the distance table

The distance table is looked up with ten bits. `dist_lens` builds, at each of the 1024 indices,
the codeword length of the symbol of the table entry there, so that the decoder finds the
length of a distance code at the index it already has. -/

/-- `q[idx]` is the codeword length of the symbol of entry `idx` of the table, for every entry
that names a symbol of the table. -/
def DistQ (lens : List U8) (table : List U32) (q : List U8) : Prop :=
  ∀ idx, idx < 1024 → (table[idx]!).val / 64 % 512 < lens.length →
    q[idx]! = lens[(table[idx]!).val / 64 % 512]!

/-- The loop's invariant: filled up to `i`. -/
def DistQInv (lens : List U8) (table : List U32) (q : List U8) (i : Nat) : Prop :=
  ∀ idx, idx < i → (table[idx]!).val / 64 % 512 < lens.length →
    q[idx]! = lens[(table[idx]!).val / 64 % 512]!

set_option maxHeartbeats 8000000 in
theorem dist_body (lens : List U8) (table : Array U32 2048#usize) (distn : Array U8 512#usize)
    (a : Array U8 1024#usize) (i : Usize)
    (hda : LensArr lens distn.val) (hi : i.val ≤ 1024) (h : DistQInv lens table.val a.val i.val) :
    dist_lens_loop.body table distn a i ⦃ r => match r with
    | .done v => DistQ lens table.val v.val
    | .cont (v, j) => (j.val ≤ 1024 ∧ DistQInv lens table.val v.val j.val) ∧
        1024 - j.val < 1024 - i.val ⦄ := by
  have hdl : distn.val.length = 512 := by scalar_tac
  have hal : a.val.length = 1024 := by scalar_tac
  have htl : table.val.length = 2048 := by scalar_tac
  unfold dist_lens_loop.body
  step*
  all_goals try scalar_tac
  · -- one more entry: i3 is the entry's symbol, i4 its cast, i5 the length
    have hilt : i.val < 1024 := by scalar_tac
    have hi4 : i4.val = i3.val := by
      rw [i4_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
    have h512 : i3.val < 512 := by
      rw [i3_post]
      exact Nat.mod_lt _ (by norm_num)
    have hi1 : i1 = table.val[i.val]! := by
      rw [getElem!_pos table.val i.val (by omega)]
      exact i1_post
    have hsym : i3.val = (table.val[i.val]!).val / 64 % 512 := by
      rw [i3_post, i2_post, hi1]
    have hi6 : i6.val = i.val + 1 := by scalar_tac
    refine ⟨?_, ?_, ?_⟩
    · show i6.val ≤ 1024
      omega
    · intro idx hidx hs
      have hidx' : idx < i.val + 1 := by omega
      rw [a1_post, Array.set_val_eq, Djinn.Vocab.getElem!_set _ _ _ _ (by omega)]
      by_cases hie : idx = i.val
      · rw [if_pos (by omega), hie]
        rw [hie, ← hsym] at hs
        have hi5 : i5 = lens[i3.val]! := by
          rw [← hda i3.val hs, ← hi4, getElem!_pos distn.val i4.val (by omega)]
          exact i5_post
        rw [hi5, hsym]
      · rw [if_neg (by omega)]
        exact h idx (by omega) hs
    · omega
  · -- done: every index is filled
    have hi' : i.val = 1024 := by scalar_tac
    exact fun idx hidx => h idx (by omega)

theorem dist_lens_correct (table : Array U32 2048#usize) (distn : Array U8 512#usize)
    (lens : List U8) (hda : LensArr lens distn.val) :
    dist_lens table distn ⦃ v => DistQ lens table.val v.val ⦄ := by
  unfold dist_lens dist_lens_loop
  apply loop.spec_decr_nat (fun (_, i) => 1024 - i.val)
    (fun (v, i) => i.val ≤ 1024 ∧ DistQInv lens table.val v.val i.val)
  · rintro ⟨v, j⟩ ⟨hj, hv⟩
    apply WP.spec_mono (dist_body lens table distn v j hda hj hv)
    intro r hr
    cases r <;> exact hr
  · exact ⟨by scalar_tac, fun idx hidx => by simp at hidx⟩

end Gzip.Proofs.Decode.DecodeTable
