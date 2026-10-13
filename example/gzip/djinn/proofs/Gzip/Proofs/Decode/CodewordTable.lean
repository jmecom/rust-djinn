import Gzip.Proofs.Decode.CodewordImpl
import Gzip.Vocab
import Gzip.Proofs.Decode.FourHistogramImpl
import Gzip.Proofs.Decode.FourHistogramMerge

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.CodewordImpl Gzip.Proofs.Decode.BaseImpl Gzip.Proofs.Decode.ReaderImpl
open Gzip.Proofs.Decode.FourHistogramFacts Gzip.Proofs.Decode.FourHistogramImpl
open Gzip.Proofs.Decode.FourHistogramMerge

namespace Gzip.Proofs.Decode.CodewordTable

def Entries (lens : List U8) (table : List U32) : Prop :=
  ∀ k, k < table.length → codeword_spec lens k (table[k]!).val

theorem entries_push (lens : List U8) (table : List U32) (v : U32)
    (h : Entries lens table) (hv : codeword_spec lens table.length v.val) :
    Entries lens (table ++ [v]) := by
  intro k hk
  by_cases he : k < table.length
  · rw [getElem!_pos _ k (by simp; omega), List.getElem_append, dif_pos he,
      ← getElem!_pos table k he]
    exact h k he
  · have heq : k = table.length := by simp only [List.length_append, List.length_singleton] at hk; omega
    subst k
    simpa using hv

def ShortTab (lens : List U8) (t : Array U32 16#usize) (n : Nat) : Prop :=
  ∀ m : Nat, m < n → shorter_spec lens lens.length m (t.val[m]!).val ∧
    (t.val[m]!).val ≤ lens.length * 2 ^ m

def SeenTab (lens : List U8) (t : Array U32 16#usize) (sym : Nat) : Prop :=
  ∀ m : Nat, m < 16 → earlier_spec lens sym m (t.val[m]!).val ∧ (t.val[m]!).val ≤ sym

/-! ## the counting recurrence, at the level of the relations

`count_shorter(lens, k, n + 1) = 2 * (count_shorter(lens, k, n) + count_earlier(lens, k, n))`
for `n ≥ 1`: every shorter code doubles and the codes of length `n` join, each worth two. -/

theorem shorter_succ (lens : List U8) (k n a e : ℤ) (hn : 1 ≤ n)
    (ha : shorter_spec lens k n a) (he : earlier_spec lens k n e) :
    shorter_spec lens k (n + 1) (2 * (a + e)) := by
  generalize hq : k.toNat = q
  induction q using Nat.strong_induction_on generalizing k a e with
  | h q ih =>
    rw [shorter_spec] at ha
    rw [earlier_spec] at he
    have hp := ha.1
    have hab := ha.2 hp
    have heb := he.2 hp
    rw [shorter_spec]
    refine ⟨hp, fun _ => ⟨fun hk => ?_, fun hk => ?_⟩⟩
    · rw [hab.1 hk, heb.1 hk]; simp
    · have hlt : (k - 1).toNat < q := hq ▸ Decoding.int_step_decreases k hp.1 hk
      have ih' := ih _ hlt
      have hab := hab.2 hk
      have heb := heb.2 hk
      refine ⟨fun hln => ?_, fun hln => ?_⟩
      · by_cases hlm : 1 ≤ ((lens[(k - 1).toNat]!).val : ℤ) ∧
            ((lens[(k - 1).toNat]!).val : ℤ) < n
        · obtain ⟨a', ha', rfl⟩ := hab.1 hlm
          have he' := heb.2 (by omega)
          refine ⟨2 * (a' + e), ih' _ _ _ ha' he' rfl, ?_⟩
          have hexp : (n + 1 - ((lens[(k - 1).toNat]!).val : ℤ)).toNat =
              (n - ((lens[(k - 1).toNat]!).val : ℤ)).toNat + 1 := by omega
          rw [hexp, pow_succ]; ring
        · have hle : ((lens[(k - 1).toNat]!).val : ℤ) = n := by omega
          obtain ⟨e', he', rfl⟩ := heb.1 hle
          have ha' := hab.2 hlm
          refine ⟨2 * (a + e'), ih' _ _ _ ha' he' rfl, ?_⟩
          have hexp : (n + 1 - ((lens[(k - 1).toNat]!).val : ℤ)).toNat = 1 := by omega
          rw [hexp]; ring
      · have hlm : ¬ (1 ≤ ((lens[(k - 1).toNat]!).val : ℤ) ∧
            ((lens[(k - 1).toNat]!).val : ℤ) < n) := by omega
        have ha' := hab.2 hlm
        have hle : ¬ ((lens[(k - 1).toNat]!).val : ℤ) = n := by omega
        have he' := heb.2 hle
        exact ih' _ _ _ ha' he' rfl

/-- The codes shorter than `n` and those of length `n` together: at most `k * 2 ^ (n - 1)`. -/
theorem shorter_earlier_bound (lens : List U8) (k n a e : ℤ) (hn : 1 ≤ n)
    (ha : shorter_spec lens k n a) (he : earlier_spec lens k n e) :
    0 ≤ a ∧ 0 ≤ e ∧ a + e ≤ k * 2 ^ (n - 1).toNat := by
  generalize hq : k.toNat = q
  induction q using Nat.strong_induction_on generalizing k a e with
  | h q ih =>
    rw [shorter_spec] at ha
    rw [earlier_spec] at he
    have hp := ha.1
    have hab := ha.2 hp
    have heb := he.2 hp
    have hpow : (0 : ℤ) < 2 ^ (n - 1).toNat := by positivity
    by_cases hk : k = 0
    · rw [hab.1 hk, heb.1 hk, hk]; simp
    · have hlt : (k - 1).toNat < q := hq ▸ Decoding.int_step_decreases k hp.1 hk
      have ih' := ih _ hlt
      have hab := hab.2 hk
      have heb := heb.2 hk
      by_cases hlm : 1 ≤ ((lens[(k - 1).toNat]!).val : ℤ) ∧
          ((lens[(k - 1).toNat]!).val : ℤ) < n
      · obtain ⟨a', ha', rfl⟩ := hab.1 hlm
        have he' := heb.2 (by omega)
        obtain ⟨h1, h2, h3⟩ := ih' _ _ _ ha' he' rfl
        have hle : (2 : ℤ) ^ (n - ((lens[(k - 1).toNat]!).val : ℤ)).toNat ≤ 2 ^ (n - 1).toNat :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hpos : (0 : ℤ) ≤ 2 ^ (n - ((lens[(k - 1).toNat]!).val : ℤ)).toNat := by positivity
        refine ⟨by omega, h2, ?_⟩
        nlinarith
      · have ha' := hab.2 hlm
        by_cases hle : ((lens[(k - 1).toNat]!).val : ℤ) = n
        · obtain ⟨e', he', rfl⟩ := heb.1 hle
          obtain ⟨h1, h2, h3⟩ := ih' _ _ _ ha' he' rfl
          refine ⟨h1, by omega, ?_⟩
          nlinarith
        · have he' := heb.2 hle
          obtain ⟨h1, h2, h3⟩ := ih' _ _ _ ha' he' rfl
          refine ⟨h1, h2, ?_⟩
          nlinarith

/-- No code is shorter than one bit. -/
theorem shorter_small (lens : List U8) (k n : ℤ) (hk : 0 ≤ k) (hkl : k ≤ lens.length) (hn : n ≤ 1) :
    shorter_spec lens k n 0 := by
  generalize hq : k.toNat = q
  induction q using Nat.strong_induction_on generalizing k with
  | h q ih =>
    rw [shorter_spec]
    refine ⟨⟨hk, hkl⟩, fun _ => ⟨fun _ => rfl, fun hk0 => ⟨fun hl => by omega, fun _ => ?_⟩⟩⟩
    have hlt : (k - 1).toNat < q := hq ▸ Decoding.int_step_decreases k hk hk0
    exact ih _ hlt (k - 1) (by omega) (by omega) rfl

/-! ## the recurrence loop: `shorter[n + 1] = 2 * (shorter[n] + count[n])` -/

theorem rec_body (lens : Aeneas.Std.Slice U8) (count shorter : Array U32 16#usize) (n : Usize)
    (hl : lens.val.length ≤ 320) (hn1 : 1 ≤ n.val) (hn : n.val ≤ 15)
    (hc : SeenTab lens.val count lens.val.length) (h : ShortTab lens.val shorter (n.val + 1)) :
    codeword_table_loop3.body count shorter n ⦃ r => match r with
    | .done t => ShortTab lens.val t 16
    | .cont (t, j) => (1 ≤ j.val ∧ j.val ≤ 15 ∧ ShortTab lens.val t (j.val + 1)) ∧
        16 - j.val < 16 - n.val ⦄ := by
  unfold codeword_table_loop3.body
  have hcn : (UScalar.cast .U32 n).val = n.val := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  step*
  all_goals try (
    have q : i = shorter.val[n.val]! := by
      rw [Djinn.Vocab.val_getElem! shorter.val n.val (by scalar_tac)]; exact i_post
    have q1 : i1 = count.val[n.val]! := by
      rw [Djinn.Vocab.val_getElem! count.val n.val (by scalar_tac)]; exact i1_post
    obtain ⟨hshort, hsb⟩ := h n.val (by omega)
    obtain ⟨hearly, heb⟩ := hc n.val (by omega)
    rw [← q] at hshort hsb
    rw [← q1] at hearly heb
    have hbound := shorter_earlier_bound lens.val lens.val.length n.val i.val i1.val (by omega)
      hshort hearly
    have hpow : (2 : ℤ) ^ ((n.val : ℤ) - 1).toNat ≤ 2 ^ 14 :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hbig : (i.val : ℤ) + i1.val ≤ 320 * 2 ^ 14 := by
      have hk : (lens.val.length : ℤ) * 2 ^ ((n.val : ℤ) - 1).toNat ≤ 320 * 2 ^ 14 := by
        have := Int.ofNat_le.mpr hl
        nlinarith
      omega)
  all_goals try scalar_tac
  · refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
    intro m hm
    have hml : m < shorter.val.length := by scalar_tac
    rw [a_post, Array.set_val_eq, Djinn.Vocab.getElem!_set _ _ _ _ hml]
    by_cases hmn : m = i4.val
    · rw [if_pos hmn]
      have hsucc := shorter_succ lens.val lens.val.length n.val i.val i1.val (by omega) hshort hearly
      have hm' : m = n.val + 1 := by scalar_tac
      refine ⟨?_, ?_⟩
      · rw [hm']
        convert hsucc using 1 <;> push_cast <;> scalar_tac
      · rw [hm', pow_succ]
        have hb3 := hbound.2.2
        have h2 : (2 : ℤ) ^ n.val = 2 * 2 ^ ((n.val : ℤ) - 1).toNat := by
          rw [← pow_succ']
          congr 1
          omega
        have hv : (i3.val : ℤ) = 2 * (i.val + i1.val) := by scalar_tac
        have hgoal : (i3.val : ℤ) ≤ lens.val.length * (2 ^ n.val * 2) := by
          rw [hv, h2]; nlinarith
        exact_mod_cast hgoal
    · rw [if_neg hmn]
      exact h m (by scalar_tac)

@[step]
theorem rec_loop_correct (lens : Aeneas.Std.Slice U8) (count shorter : Array U32 16#usize) (n : Usize)
    (hl : lens.val.length ≤ 320) (hn1 : 1 ≤ n.val) (hn : n.val ≤ 15)
    (hc : SeenTab lens.val count lens.val.length) (h : ShortTab lens.val shorter (n.val + 1)) :
    codeword_table_loop3 count shorter n ⦃ t => ShortTab lens.val t 16 ⦄ := by
  unfold codeword_table_loop3
  apply loop.spec_decr_nat (fun (_, n) => 16 - n.val)
    (fun (t, n) => 1 ≤ n.val ∧ n.val ≤ 15 ∧ ShortTab lens.val t (n.val + 1))
  · rintro ⟨t, j⟩ ⟨hj1, hj, ht⟩
    apply WP.spec_mono (rec_body lens count t j hl hj1 hj hc ht)
    intro r hr
    cases r <;> exact hr
  · exact ⟨hn1, hn, h⟩

/-! ## the group starts: `start[n + 1] = start[n] + count[n]`; only their size matters -/

/-- The first `n + 1` group starts are small (at most `320 * m` for start `m`). -/
def StartBound (t : Array Usize 17#usize) (n : Nat) : Prop :=
  ∀ m : Nat, m ≤ n → (t.val[m]!).val ≤ 320 * m

theorem start_body (lens : Aeneas.Std.Slice U8) (count : Array U32 16#usize)
    (start : Array Usize 17#usize) (n : Usize)
    (hl : lens.val.length ≤ 320) (hn : n.val ≤ 16)
    (hc : SeenTab lens.val count lens.val.length) (h : StartBound start n.val) :
    codeword_table_loop4.body count start n ⦃ r => match r with
    | .done t => StartBound t 16
    | .cont (t, j) => (j.val ≤ 16 ∧ StartBound t j.val) ∧ 16 - j.val < 16 - n.val ⦄ := by
  unfold codeword_table_loop4.body
  step*
  all_goals try (
    have hlt : n.val < 16 := by scalar_tac
    have hi : i = start.val[n.val]! := by
      rw [Djinn.Vocab.val_getElem! start.val n.val (by scalar_tac)]; exact i_post
    have hi1 : i1 = count.val[n.val]! := by
      rw [Djinn.Vocab.val_getElem! count.val n.val (by scalar_tac)]; exact i1_post
    have hsb := h n.val le_rfl
    have hcb := (hc n.val hlt).2
    rw [← hi] at hsb
    rw [← hi1] at hcb
    have hi2 : i2.val = i1.val := by
      rw [i2_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac)
  all_goals try scalar_tac
  · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    intro m hm
    have hml : m < start.val.length := by scalar_tac
    rw [a_post, Array.set_val_eq, Djinn.Vocab.getElem!_set _ _ _ _ hml]
    split_ifs with hmn
    · have hm' : m = n.val + 1 := by scalar_tac
      have hv : i3.val = i.val + i2.val := by scalar_tac
      rw [hm', hv, hi2]
      omega
    · exact h m (by scalar_tac)

theorem start_loop_correct (lens : Aeneas.Std.Slice U8) (count : Array U32 16#usize)
    (start : Array Usize 17#usize) (n : Usize)
    (hl : lens.val.length ≤ 320) (hn : n.val ≤ 16)
    (hc : SeenTab lens.val count lens.val.length) (h : StartBound start n.val) :
    codeword_table_loop4 count start n ⦃ t => StartBound t 16 ⦄ := by
  unfold codeword_table_loop4
  apply loop.spec_decr_nat (fun (_, n) => 16 - n.val)
    (fun (t, n) => n.val ≤ 16 ∧ StartBound t n.val)
  · rintro ⟨t, j⟩ ⟨hj, ht⟩
    apply WP.spec_mono (start_body lens count t j hl hj hc ht)
    intro r hr
    cases r <;> exact hr
  · exact ⟨hn, h⟩

/-! ## the main loop: the codes, and the symbols grouped by length (a hint, unconstrained) -/

/-- The first `k` codes are right. -/
def EntriesUpTo (lens : List U8) (table : List U32) (k : Nat) : Prop :=
  ∀ j, j < k → codeword_spec lens j (table[j]!).val

set_option maxHeartbeats 4000000 in
theorem table_body (lens : Aeneas.Std.Slice U8) (shorter : Array U32 16#usize)
    (start : Array Usize 17#usize) (seen : Array U32 16#usize) (sorted : Array U16 512#usize)
    (table : alloc.vec.Vec U32) (sym : Usize)
    (hl : lens.val.length ≤ 320)
    (hb : ∀ j, j < lens.val.length → (lens.val[j]!).val ≤ 15)
    (hs : ShortTab lens.val shorter 16)
    (hst : StartBound start 16)
    (hn : sym.val ≤ lens.val.length)
    (hlen : table.val.length = lens.val.length) (h : EntriesUpTo lens.val table.val sym.val)
    (he : SeenTab lens.val seen sym.val) :
    codeword_table_loop5.body lens shorter start seen sorted table sym ⦃ r => match r with
    | .done z => z.2.val.length = lens.val.length ∧ Entries lens.val z.2.val
    | .cont (t, _, v, j) => j.val ≤ lens.val.length ∧ v.val.length = lens.val.length ∧
        EntriesUpTo lens.val v.val j.val ∧ SeenTab lens.val t j.val ∧
        lens.val.length - j.val < lens.val.length - sym.val ⦄ := by
  unfold codeword_table_loop5.body
  step*
  all_goals try (
    have he' : sym.val = lens.val.length := by scalar_tac
    refine ⟨hlen, ?_⟩
    intro k hk
    exact h k (by omega))
  have hlt : sym.val < lens.val.length := by scalar_tac
  have hsl : sym.val < table.val.length := by rw [hlen]; exact hlt
  have hn' : n.val = (lens.val[sym.val]!).val := by
    rw [n_post, UScalar.cast_val_eq, i1_post, getElem!_pos lens.val sym.val hlt]
    apply Nat.mod_eq_of_lt
    scalar_tac
  have hn15 := hb sym.val hlt
  split
  · have hn16 : n.val < 16 := by scalar_tac
    obtain ⟨hshort, hsbound⟩ := hs n.val hn16
    obtain ⟨hearly, hebound⟩ := he n.val hn16
    have hp := pow_two_le n.val (by omega)
    have hsb : (shorter.val[n.val]!).val ≤ 320 * 65536 :=
      _root_.le_trans hsbound (Nat.mul_le_mul hl hp)
    have hstb : (start.val[n.val]!).val ≤ 320 * 16 := by
      have := hst n.val (by omega)
      omega
    step as ⟨i2, i2_post⟩
    step as ⟨i3, i3_post⟩
    have q2 : i2 = shorter.val[n.val]! := by
      rw [Djinn.Vocab.val_getElem! shorter.val n.val (by scalar_tac)]; exact i2_post
    have q3 : i3 = seen.val[n.val]! := by
      rw [Djinn.Vocab.val_getElem! seen.val n.val (by scalar_tac)]; exact i3_post
    rw [← q2] at hshort hsb
    rw [← q3] at hearly hebound
    step as ⟨c, c_post⟩
    step as ⟨i4, i4_post⟩
    have q4 : i4 = start.val[n.val]! := by
      rw [Djinn.Vocab.val_getElem! start.val n.val (by scalar_tac)]; exact i4_post
    rw [← q4] at hstb
    step as ⟨i5, i5_post⟩
    have hi5 : i5.val = i3.val := by
      rw [i5_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
    step as ⟨i6, i6_post⟩
    step as ⟨i7, i7_post⟩
    step as ⟨i8, i8_post⟩
    step as ⟨a0, a0_post⟩
    step as ⟨i9, i9_post⟩
    step as ⟨a, a_post⟩
    have hcw : codeword_spec lens.val sym.val c.val := by
      refine ⟨trivial, ⟨by omega, by omega⟩, i2.val, ?_, i3.val, ?_, ?_⟩
      · simpa only [Int.toNat_natCast, ← hn'] using hshort
      · simpa only [Int.toNat_natCast, ← hn'] using hearly
      · scalar_tac
    have hseen1 : SeenTab lens.val a (sym.val + 1) := by
      intro m hm
      have hml : m < seen.val.length := by scalar_tac
      obtain ⟨hem, hemb⟩ := he m hm
      have hnext := earlier_next lens.val sym.val m _ hlt hem
      rw [a_post]
      simp only [Array.set_val_eq]
      rw [Djinn.Vocab.getElem!_set _ _ _ _ hml]
      by_cases hmn : m = n.val
      · rw [if_pos hmn]
        rw [if_pos (by omega), hmn, ← q3] at hnext
        refine ⟨?_, by scalar_tac⟩
        convert hnext using 1 <;> push_cast <;> scalar_tac
      · rw [if_neg hmn]
        rw [if_neg (by omega), add_zero] at hnext
        refine ⟨?_, by scalar_tac⟩
        convert hnext using 1 <;> push_cast <;> scalar_tac
    step*
    all_goals (
      have hset : (index_mut_back c).val = table.val.set sym.val c := by
        rw [index_mut_back_post, alloc.vec.Vec.set_val_eq]
      have hsym1 : sym1.val = sym.val + 1 := by scalar_tac
      refine ⟨by scalar_tac, by rw [hset, List.length_set]; exact hlen, ?_, by rw [hsym1]; exact hseen1,
        by scalar_tac⟩
      intro k hk
      rw [hset, Djinn.Vocab.getElem!_set _ _ _ _ (by omega)]
      split_ifs with hks
      · rw [hks]; exact hcw
      · exact h k (by omega))
  · exfalso
    scalar_tac

theorem table_loop_correct (lens : Aeneas.Std.Slice U8) (shorter : Array U32 16#usize)
    (start : Array Usize 17#usize) (seen : Array U32 16#usize) (sorted : Array U16 512#usize)
    (table : alloc.vec.Vec U32) (sym : Usize)
    (hl : lens.val.length ≤ 320)
    (hb : ∀ j, j < lens.val.length → (lens.val[j]!).val ≤ 15)
    (hs : ShortTab lens.val shorter 16)
    (hst : StartBound start 16)
    (hn : sym.val ≤ lens.val.length)
    (hlen : table.val.length = lens.val.length) (h : EntriesUpTo lens.val table.val sym.val)
    (he : SeenTab lens.val seen sym.val) :
    codeword_table_loop5 lens shorter start seen sorted table sym
      ⦃ z => z.2.val.length = lens.val.length ∧ Entries lens.val z.2.val ⦄ := by
  unfold codeword_table_loop5
  apply loop.spec_decr_nat (fun (_, _, _, j) => lens.val.length - j.val)
    (fun (t, _, v, j) => j.val ≤ lens.val.length ∧ v.val.length = lens.val.length ∧
      EntriesUpTo lens.val v.val j.val ∧ SeenTab lens.val t j.val)
  · rintro ⟨t, so, v, j⟩ ⟨hj, hv, hent, hseen⟩
    apply WP.spec_mono (table_body lens shorter start t so v j hl hb hs hst hj hv hent hseen)
    intro r hr
    cases r with
    | done v => exact hr
    | cont v => exact ⟨⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩, hr.2.2.2.2⟩
  · exact ⟨hn, hlen, h, he⟩

/-- The codes are right; the sorted symbols and group starts are unconstrained (the table
builder checks every symbol's length itself). -/
@[step]
theorem codeword_table_correct (lens : Aeneas.Std.Slice U8) (hl : lens.val.length ≤ 320)
    (hb : ∀ j, j < lens.val.length → (lens.val[j]!).val ≤ 15) :
    codeword_table lens ⦃ z => z.1.val.length = lens.val.length ∧ Entries lens.val z.1.val ⦄ := by
  unfold codeword_table
  have hfrom (n : Usize) := alloc.vec.from_elem_spec core.clone.CloneU32 0#u32 n rfl
  have hz : ∀ m, m < 16 → ((Array.repeat 16#usize 0#u32).val[m]!).val = 0 := by
    intro m hm
    interval_cases m <;> simp
  have hseen0 : SeenTab lens.val (Array.repeat 16#usize 0#u32) 0 := by
    intro m hm
    rw [hz m hm]
    exact ⟨earlier_zero _ _, by omega⟩
  have hshort2 : ShortTab lens.val (Array.repeat 16#usize 0#u32) 2 := by
    intro m hm
    rw [hz m (by omega)]
    refine ⟨?_, by omega⟩
    have hs := shorter_small lens.val lens.val.length m (by omega) le_rfl (by omega)
    simpa using hs
  have hstart0 : StartBound (Array.repeat 17#usize 0#usize) 0 := by
    intro m hm
    have hm0 : m = 0 := by omega
    rw [hm0]
    have hmem := Djinn.Vocab.getElem!_mem (Array.repeat 17#usize 0#usize).val 0 (by simp)
    rw [Array.repeat_val, List.mem_replicate] at hmem
    rw [Array.repeat_val, hmem.2]
    simp
  have hsum0 : SummedSeen lens.val (Array.repeat 16#usize 0#u32).val
      (Array.repeat 16#usize 0#u32).val (Array.repeat 16#usize 0#u32).val
      (Array.repeat 16#usize 0#u32).val (0#usize).val := by
    simpa [Array.repeat_val] using summed_zero lens.val
  step with (four_loop_correct lens (Array.repeat 16#usize 0#u32)
    (Array.repeat 16#usize 0#u32) (Array.repeat 16#usize 0#u32)
    (Array.repeat 16#usize 0#u32) 0#usize hl hb hsum0) as ⟨a1, b1, c1, d1, i, hsum1⟩
  step with (tail_loop_correct lens a1 b1 c1 d1 i hl hb hsum1) as ⟨a2, hsum2⟩
  have hmerge0 : MergeSeen lens.val a2.val b1.val c1.val d1.val (0#usize).val := by
    intro m hm
    simpa only [show ¬ m < (0#usize).val by simp, if_false] using hsum2.2 m hm
  step with (merge_loop_correct lens a2 b1 c1 d1 0#usize hl (by scalar_tac) hmerge0)
    as ⟨count1, hcount1⟩
  have hcount : SeenTab lens.val count1 lens.val.length := hcount1
  step with (rec_loop_correct lens count1 (Array.repeat 16#usize 0#u32) 1#usize hl
    (by scalar_tac) (by scalar_tac) hcount hshort2) as ⟨shorter1, hshorter1⟩
  step with (start_loop_correct lens count1 (Array.repeat 17#usize 0#usize) 0#usize hl
    (by scalar_tac) hcount1 hstart0) as ⟨start1, hstart1⟩
  step as ⟨table, htable, htlen⟩
  have hlen0 : table.val.length = lens.val.length := by
    rw [htable, List.length_replicate]
    simp [Slice.len]
  step with (table_loop_correct lens shorter1 start1 (Array.repeat 16#usize 0#u32)
    (Array.repeat 512#usize 0#u16) table 0#usize hl hb hshorter1 hstart1
    (by scalar_tac) hlen0 (fun k hk => by simp at hk) hseen0) as ⟨z, hz1, hz2⟩
  step*

@[step]
theorem cached_codeword_correct (lens : Aeneas.Std.Slice U8) (codes : Aeneas.Std.Slice U32) (sym : Usize)
    (hs : sym.val < lens.val.length)
    (hlen : codes.val.length = lens.val.length) (htable : Entries lens.val codes.val) :
    cached_codeword lens codes sym ⦃ c => codeword_spec lens.val sym.val c.val ⦄ := by
  unfold cached_codeword
  step as ⟨c, hc⟩
  step*
  have he : c = codes.val[sym.val]! := by
    rw [getElem!_pos codes.val sym.val (by omega)]; exact hc
  rw [he]
  exact htable sym.val (by omega)

end Gzip.Proofs.Decode.CodewordTable
