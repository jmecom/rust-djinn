import Aeneas
import Gzip.Code.Funs
import Gzip.Proofs.Crc
import Gzip.Proofs.CrcWord

open Aeneas Std Result
open Gzip.solution

namespace Gzip.Proofs.Crc

theorem inner_body (c : U32) (n : I32) (hn : 0 ≤ n.val ∧ n.val ≤ 8) :
    crc32_loop0_loop0.body c n ⦃ r =>
      match r with
      | .done d => d = c ∧ n.val = 8
      | .cont (d, m) => d.val = one c.val ∧ m.val = n.val + 1 ∧ n.val < 8 ⦄ := by
  unfold crc32_loop0_loop0.body
  step*
  · rename_i hlt
    have hnlt : n.val < 8 := by simpa [IScalar.lt_equiv] using hlt
    have hi : i.val = c.val % 2 := by
      rw [i_post, UScalar.val_and]
      change c.val &&& 1 = c.val % 2
      exact Nat.and_two_pow_sub_one_eq_mod c.val 1
    split
    · rename_i h
      step*
      have he : i.val = 1 := by simpa using congrArg UScalar.val h
      have hp : c.val % 2 = 1 := by omega
      refine ⟨?_, n1_post, hnlt⟩
      simp only [UScalar.val_xor, x_post, Nat.shiftRight_eq_div_pow, one, hp, if_true]
      rfl
    · rename_i h
      step*
      have he : i.val ≠ 1 := by
        intro he
        apply h
        apply (UScalar.eq_equiv i 1#u32).mpr
        exact he
      have hp : ¬ c.val % 2 = 1 := by omega
      refine ⟨?_, n1_post, hnlt⟩
      simp only [c1_post, Nat.shiftRight_eq_div_pow, one, hp, if_false]


@[step]
theorem inner (c : U32) (n : I32) (hn : 0 ≤ n.val ∧ n.val ≤ 8) :
    crc32_loop0_loop0 c n ⦃ d => d.val = bits c.val (8 - n.val).toNat ⦄ := by
  unfold crc32_loop0_loop0
  apply loop.spec_decr_nat (fun (_, m) => (8 - m.val).toNat)
    (fun (d, m) => (0 ≤ m.val ∧ m.val ≤ 8) ∧
      bits d.val (8 - m.val).toNat = bits c.val (8 - n.val).toNat)
  · rintro ⟨d, m⟩ ⟨hm, hi⟩
    refine WP.spec_mono (inner_body d m hm) ?_
    intro r hr
    cases r with
    | done e =>
        obtain ⟨rfl, he⟩ := hr
        simpa [he, bits] using hi
    | cont state =>
        obtain ⟨e, k⟩ := state
        obtain ⟨he, hk, hlt⟩ := hr
        simp only at *
        have hdiff : (8 - m.val).toNat = (8 - k.val).toNat + 1 := by omega
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [he, bits_commute]
        rw [hdiff, bits] at hi
        exact hi
  · exact ⟨hn, rfl⟩

/-- The table so far: entry `256 * j + b` is the register after the byte `b` and `j` more
zero bytes. -/
def Table (table : alloc.vec.Vec U32) (n : ℕ) : Prop :=
  table.val.length = n ∧ ∀ k < n, (table.val[k]!).val = bits (k % 256) (8 * (k / 256 + 1))

theorem table_body (table : alloc.vec.Vec U32) (i : U32)
    (hi : i.val ≤ 256) (ht : Table table i.val) :
    crc32_loop0.body table i ⦃ r =>
      match r with
      | .done t => Table t 256
      | .cont (t, m) => Table t m.val ∧ m.val = i.val + 1 ∧ m.val ≤ 256 ⦄ := by
  unfold crc32_loop0.body
  step*
  · refine ⟨⟨?_, ?_⟩, i1_post, ?_⟩
    · simp only [table1_post, List.length_append, List.length_singleton, ht.1, i1_post]
    · intro k hk
      by_cases hk0 : k < i.val
      · have hklen : k < table.val.length := by rw [ht.1]; exact hk0
        rw [table1_post, List.getElem!_append_left table.val [c] k hklen]
        exact ht.2 k hk0
      · have he : k = i.val := by omega
        subst k
        have hm : i.val % 256 = i.val := Nat.mod_eq_of_lt (by scalar_tac)
        have hd : i.val / 256 = 0 := Nat.div_eq_of_lt (by scalar_tac)
        rw [hm, hd, table1_post, ← ht.1]
        simpa [ht.1] using c_post
    · scalar_tac

@[step]
theorem table_loop (table : alloc.vec.Vec U32) (i : U32)
    (hi : i.val ≤ 256) (ht : Table table i.val) :
    crc32_loop0 table i ⦃ t => Table t 256 ⦄ := by
  unfold crc32_loop0
  apply loop.spec_decr_nat (fun (_, m) => 256 - m.val)
    (fun (t, m) => m.val ≤ 256 ∧ Table t m.val)
  · rintro ⟨t, m⟩ ⟨hm, hh⟩
    refine WP.spec_mono (table_body t m hm hh) ?_
    intro r hr
    cases r with
    | done t => exact hr
    | cont state =>
        obtain ⟨t, k⟩ := state
        obtain ⟨ht, hk, hkbound⟩ := hr
        simp only at *
        exact ⟨⟨hkbound, ht⟩, by omega⟩
  · exact ⟨hi, ht⟩

-- ================================================================ the other fifteen tables

theorem extend_body (table : alloc.vec.Vec U32) (k : Usize)
    (hk : 256 ≤ k.val ∧ k.val ≤ 4096) (ht : Table table k.val) :
    crc32_loop1.body table k ⦃ r =>
      match r with
      | .done t => Table t 4096
      | .cont (t, m) => Table t m.val ∧ m.val = k.val + 1 ∧ 256 ≤ m.val ∧ m.val ≤ 4096 ⦄ := by
  obtain ⟨hlen, hval⟩ := ht
  unfold crc32_loop1.body
  step*
  · -- the second lookup stays in the table built so far
    have h2 : i2.val = prev.val % 256 := by
      rw [i2_post, UScalar.val_and]
      change prev.val &&& 255 = prev.val % 256
      exact Nat.and_two_pow_sub_one_eq_mod prev.val 8
    have h3 : i3.val = i2.val := by
      rw [i3_post]
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      scalar_tac
    simp only [alloc.vec.Vec.length]
    rw [hlen, h3, h2]
    have := Nat.mod_lt prev.val (show 0 < 256 by decide)
    omega
  · have h2 : i2.val = prev.val % 256 := by
      rw [i2_post, UScalar.val_and]
      change prev.val &&& 255 = prev.val % 256
      exact Nat.and_two_pow_sub_one_eq_mod prev.val 8
    have h3 : i3.val = i2.val := by
      rw [i3_post]
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      scalar_tac
    have hklt : k.val < 4096 := by scalar_tac
    have hprev : prev.val = bits ((k.val - 256) % 256) (8 * ((k.val - 256) / 256 + 1)) := by
      rw [prev_post, ← getElem!_pos table.val i.val (by rw [hlen]; omega), i_post]
      exact hval (k.val - 256) (by omega)
    have h3b : i3.val < k.val := by
      rw [h3, h2]
      have := Nat.mod_lt prev.val (show 0 < 256 by decide)
      omega
    have h4 : i4.val = bits (prev.val % 256) 8 := by
      rw [i4_post, ← getElem!_pos table.val i3.val (by rw [hlen]; exact h3b), hval i3.val h3b, h3, h2]
      have hm : prev.val % 256 % 256 = prev.val % 256 := Nat.mod_mod _ _
      have hd : prev.val % 256 / 256 = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ (by decide))
      rw [hm, hd]
    have h1 : i1.val = prev.val / 256 := by
      simpa only [Nat.shiftRight_eq_div_pow] using i1_post
    have hc : c.val = bits (k.val % 256) (8 * (k.val / 256 + 1)) := by
      rw [c_post, UScalar.val_xor, h1, h4, ← bits_table, hprev, ← bits_add]
      have e1 : (k.val - 256) % 256 = k.val % 256 := by omega
      have e2 : 8 * ((k.val - 256) / 256 + 1) + 8 = 8 * (k.val / 256 + 1) := by omega
      rw [e1, e2]
    refine ⟨⟨?_, ?_⟩, k1_post, by omega, by scalar_tac⟩
    · simp only [table1_post, List.length_append, List.length_singleton, hlen, k1_post]
    · intro j hj
      by_cases hj0 : j < k.val
      · have hjlen : j < table.val.length := by rw [hlen]; exact hj0
        rw [table1_post, List.getElem!_append_left table.val [c] j hjlen]
        exact hval j hj0
      · have he : j = k.val := by omega
        subst j
        rw [table1_post, ← hlen]
        simpa [hlen] using hc
  · have he : k.val = 4096 := by scalar_tac
    rw [he] at hlen hval
    exact ⟨hlen, hval⟩

@[step]
theorem extend_loop (table : alloc.vec.Vec U32) (k : Usize)
    (hk : 256 ≤ k.val ∧ k.val ≤ 4096) (ht : Table table k.val) :
    crc32_loop1 table k ⦃ t => Table t 4096 ⦄ := by
  unfold crc32_loop1
  apply loop.spec_decr_nat (fun (_, m) => 4096 - m.val)
    (fun (t, m) => (256 ≤ m.val ∧ m.val ≤ 4096) ∧ Table t m.val)
  · rintro ⟨t, m⟩ ⟨hm, hh⟩
    refine WP.spec_mono (extend_body t m hm hh) ?_
    intro r hr
    cases r with
    | done t => exact hr
    | cont state =>
        obtain ⟨t, k⟩ := state
        obtain ⟨ht, hk, hk0, hk1⟩ := hr
        simp only at *
        exact ⟨⟨⟨hk0, hk1⟩, ht⟩, by omega⟩
  · exact ⟨hk, ht⟩

-- ================================================================ sixteen bytes at a time

/-- An element of a slice of a list, as an element of the list. -/
theorem slice_getElem! (l : List U8) (a b i : ℕ) (h : i < b - a) (hb : b ≤ l.length) :
    (List.slice a b l)[i]! = l[a + i]! := by
  unfold List.slice
  have h1 : i < (List.take (b - a) (List.drop a l)).length := by simp; omega
  have h2 : a + i < l.length := by omega
  rw [getElem!_pos (List.take (b - a) (List.drop a l)) i h1, getElem!_pos l (a + i) h2]
  simp [List.getElem_take, List.getElem_drop]

/-- The word of four bytes, read through a subslice of length four. -/
@[step]
theorem word_spec (data : Aeneas.Std.Slice U8) (p : Usize) (hp : p.val + 4 ≤ data.val.length) :
    word data p ⦃ r => r.val = (data.val[p.val]!).val + (data.val[p.val + 1]!).val * 256 +
      (data.val[p.val + 2]!).val * 65536 + (data.val[p.val + 3]!).val * 16777216 ⦄ := by
  unfold word
  step as ⟨i, hi⟩
  have hsub := core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    ({ start := p, «end» := i } : core.ops.range.Range Usize) data (by simp; scalar_tac) (by simp; scalar_tac)
  step as ⟨w, hw1, hw2⟩
  have hwlen : w.val.length = 4 := by
    have h := hw2
    simp only [Slice.length] at h
    omega
  have hb : ∀ j, j < 4 → w.val[j]! = data.val[p.val + j]! := by
    intro j hj
    rw [hw1]
    exact slice_getElem! data.val p.val i.val j (by omega) (by omega)
  have hl0 : (data.val[p.val]!).val < 256 := by scalar_tac
  have hl1 : (data.val[p.val + 1]!).val < 256 := by scalar_tac
  have hl2 : (data.val[p.val + 2]!).val < 256 := by scalar_tac
  have hl3 : (data.val[p.val + 3]!).val < 256 := by scalar_tac
  step as ⟨b0, hb0⟩
  have e0 : b0 = data.val[p.val]! := by
    rw [hb0, ← getElem!_pos w.val 0 (by simp [hwlen])]
    simpa using hb 0 (by omega)
  step as ⟨c0, hc0⟩
  have hc0v : c0.val = (data.val[p.val]!).val := by
    rw [hc0, ← e0]
    apply UScalar.cast_val_mod_pow_of_inBounds_eq
    scalar_tac
  step as ⟨b1, hb1⟩
  have e1 : b1 = data.val[p.val + 1]! := by
    rw [hb1, ← getElem!_pos w.val 1 (by simp [hwlen])]
    simpa using hb 1 (by omega)
  step as ⟨c1, hc1⟩
  have hc1v : c1.val = (data.val[p.val + 1]!).val := by
    rw [hc1, ← e1]
    apply UScalar.cast_val_mod_pow_of_inBounds_eq
    scalar_tac
  step as ⟨m1, hm1⟩
  step as ⟨s1, hs1⟩
  step as ⟨b2, hb2⟩
  have e2 : b2 = data.val[p.val + 2]! := by
    rw [hb2, ← getElem!_pos w.val 2 (by simp [hwlen])]
    simpa using hb 2 (by omega)
  step as ⟨c2, hc2⟩
  have hc2v : c2.val = (data.val[p.val + 2]!).val := by
    rw [hc2, ← e2]
    apply UScalar.cast_val_mod_pow_of_inBounds_eq
    scalar_tac
  step as ⟨m2, hm2⟩
  step as ⟨s2, hs2⟩
  step as ⟨b3, hb3⟩
  have e3 : b3 = data.val[p.val + 3]! := by
    rw [hb3, ← getElem!_pos w.val 3 (by simp [hwlen])]
    simpa using hb 3 (by omega)
  step as ⟨c3, hc3⟩
  have hc3v : c3.val = (data.val[p.val + 3]!).val := by
    rw [hc3, ← e3]
    apply UScalar.cast_val_mod_pow_of_inBounds_eq
    scalar_tac
  step as ⟨m3, hm3⟩
  step as ⟨r, hr⟩
  omega

@[step]
theorem look_spec (table : alloc.vec.Vec U32) (base : Usize) (x : U32)
    (ht : Table table 4096) (hb : base.val ≤ 3840) (hm : base.val % 256 = 0) :
    look table base x ⦃ r => r.val = bits (x.val % 256) (8 * (base.val / 256 + 1)) ⦄ := by
  obtain ⟨hlen, hval⟩ := ht
  have hlow : (x &&& 255#u32).val = x.val % 256 := by
    rw [UScalar.val_and]
    change x.val &&& 255 = x.val % 256
    exact Nat.and_two_pow_sub_one_eq_mod x.val 8
  have hmod := Nat.mod_lt x.val (show 0 < 256 by decide)
  unfold look
  step*
  have hi1 : i1.val = i.val := by
    rw [i1_post]
    apply UScalar.cast_val_mod_pow_of_inBounds_eq
    scalar_tac
  have hi2 : i2.val = base.val + x.val % 256 := by rw [i2_post, hi1, i_post, hlow]
  have hi2b : i2.val < 4096 := by rw [hi2]; omega
  rw [r_post, ← getElem!_pos table.val i2.val (by rw [hlen]; exact hi2b), hval i2.val hi2b, hi2]
  have e1 : (base.val + x.val % 256) % 256 = x.val % 256 := by omega
  have e2 : (base.val + x.val % 256) / 256 = base.val / 256 := by omega
  rw [e1, e2]

/-- The four lookups of a block's first word: the word shifted all the way. -/
@[step]
theorem head_spec (table : alloc.vec.Vec U32) (w0 : U32) (ht : Table table 4096) :
    crc_head table w0 ⦃ r => r.val = bits w0.val 128 ⦄ := by
  unfold crc_head
  step*
  have hw0b : w0.val < 4294967296 := by scalar_tac
  have h1 : i1.val = w0.val / 256 := by simpa only [Nat.shiftRight_eq_div_pow] using i1_post
  have h4 : i4.val = w0.val / 65536 := by simpa only [Nat.shiftRight_eq_div_pow] using i4_post
  have h6 : i6.val = w0.val / 16777216 := by simpa only [Nat.shiftRight_eq_div_pow] using i6_post
  have e6 : w0.val / 16777216 % 256 = w0.val / 16777216 := Nat.mod_eq_of_lt (by omega)
  have hb := bits_bytes w0.val 96
  simp only [Nat.reduceAdd] at hb
  rw [hb]
  simp only [UScalar.val_xor, i3_post, i8_post]
  rw [i_post, i2_post, i5_post, i7_post, h1, h4, h6, e6]
  simp only [Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul]
  simp only [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

set_option maxHeartbeats 8000000 in
/-- The twelve lookups of a block's last three words. -/
@[step]
theorem rest_spec (data : Aeneas.Std.Slice U8) (table : alloc.vec.Vec U32) (p : Usize)
    (ht : Table table 4096) (hp : p.val + 16 ≤ data.val.length) :
    crc_rest data table p ⦃ r => r.val = rest data.val p.val ⦄ := by
  unfold crc_rest
  step*
  have hw1 : w1.val = (data.val[p.val + 4]!).val + (data.val[p.val + 5]!).val * 256 +
      (data.val[p.val + 6]!).val * 65536 + (data.val[p.val + 7]!).val * 16777216 := by
    rw [w1_post, i_post]
  have hw2 : w2.val = (data.val[p.val + 8]!).val + (data.val[p.val + 9]!).val * 256 +
      (data.val[p.val + 10]!).val * 65536 + (data.val[p.val + 11]!).val * 16777216 := by
    rw [w2_post, i1_post]
  have hw3 : w3.val = (data.val[p.val + 12]!).val + (data.val[p.val + 13]!).val * 256 +
      (data.val[p.val + 14]!).val * 65536 + (data.val[p.val + 15]!).val * 16777216 := by
    rw [w3_post, i2_post]
  have hl4 : (data.val[p.val + 4]!).val < 256 := by
    have := (data.val[p.val + 4]!).hBounds
    scalar_tac
  have hl5 : (data.val[p.val + 5]!).val < 256 := by
    have := (data.val[p.val + 5]!).hBounds
    scalar_tac
  have hl6 : (data.val[p.val + 6]!).val < 256 := by
    have := (data.val[p.val + 6]!).hBounds
    scalar_tac
  have hl7 : (data.val[p.val + 7]!).val < 256 := by
    have := (data.val[p.val + 7]!).hBounds
    scalar_tac
  have hl8 : (data.val[p.val + 8]!).val < 256 := by
    have := (data.val[p.val + 8]!).hBounds
    scalar_tac
  have hl9 : (data.val[p.val + 9]!).val < 256 := by
    have := (data.val[p.val + 9]!).hBounds
    scalar_tac
  have hl10 : (data.val[p.val + 10]!).val < 256 := by
    have := (data.val[p.val + 10]!).hBounds
    scalar_tac
  have hl11 : (data.val[p.val + 11]!).val < 256 := by
    have := (data.val[p.val + 11]!).hBounds
    scalar_tac
  have hl12 : (data.val[p.val + 12]!).val < 256 := by
    have := (data.val[p.val + 12]!).hBounds
    scalar_tac
  have hl13 : (data.val[p.val + 13]!).val < 256 := by
    have := (data.val[p.val + 13]!).hBounds
    scalar_tac
  have hl14 : (data.val[p.val + 14]!).val < 256 := by
    have := (data.val[p.val + 14]!).hBounds
    scalar_tac
  have hl15 : (data.val[p.val + 15]!).val < 256 := by
    have := (data.val[p.val + 15]!).hBounds
    scalar_tac
  have h3 : i3.val = w1.val / 256 := by simpa only [Nat.shiftRight_eq_div_pow] using i3_post
  have h4 : i4.val = w1.val / 65536 := by simpa only [Nat.shiftRight_eq_div_pow] using i4_post
  have h5 : i5.val = w1.val / 16777216 := by simpa only [Nat.shiftRight_eq_div_pow] using i5_post
  have h6 : i6.val = w2.val / 256 := by simpa only [Nat.shiftRight_eq_div_pow] using i6_post
  have h7 : i7.val = w2.val / 65536 := by simpa only [Nat.shiftRight_eq_div_pow] using i7_post
  have h8 : i8.val = w2.val / 16777216 := by simpa only [Nat.shiftRight_eq_div_pow] using i8_post
  have h9 : i9.val = w3.val / 256 := by simpa only [Nat.shiftRight_eq_div_pow] using i9_post
  have h10 : i10.val = w3.val / 65536 := by simpa only [Nat.shiftRight_eq_div_pow] using i10_post
  have h11 : i11.val = w3.val / 16777216 := by simpa only [Nat.shiftRight_eq_div_pow] using i11_post
  have e4 : w1.val % 256 = (data.val[p.val + 4]!).val := by rw [hw1]; omega
  have e5 : w1.val / 256 % 256 = (data.val[p.val + 5]!).val := by rw [hw1]; omega
  have e6 : w1.val / 65536 % 256 = (data.val[p.val + 6]!).val := by rw [hw1]; omega
  have e7 : w1.val / 16777216 % 256 = (data.val[p.val + 7]!).val := by rw [hw1]; omega
  have e8 : w2.val % 256 = (data.val[p.val + 8]!).val := by rw [hw2]; omega
  have e9 : w2.val / 256 % 256 = (data.val[p.val + 9]!).val := by rw [hw2]; omega
  have e10 : w2.val / 65536 % 256 = (data.val[p.val + 10]!).val := by rw [hw2]; omega
  have e11 : w2.val / 16777216 % 256 = (data.val[p.val + 11]!).val := by rw [hw2]; omega
  have e12 : w3.val % 256 = (data.val[p.val + 12]!).val := by rw [hw3]; omega
  have e13 : w3.val / 256 % 256 = (data.val[p.val + 13]!).val := by rw [hw3]; omega
  have e14 : w3.val / 65536 % 256 = (data.val[p.val + 14]!).val := by rw [hw3]; omega
  have e15 : w3.val / 16777216 % 256 = (data.val[p.val + 15]!).val := by rw [hw3]; omega
  simp only [UScalar.val_xor, i12_post, i13_post, i14_post, i15_post, i16_post, i17_post,
    i18_post, i19_post, i20_post, i21_post]
  rw [t4_post, t5_post, t6_post, t7_post, t8_post, t9_post, t10_post, t11_post,
    t12_post, t13_post, t14_post, t15_post]
  rw [h3, h4, h5, h6, h7, h8, h9, h10, h11,
    e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  simp only [Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul, rest]
  simp only [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

/-- One block of the pipelined loop: the register of the block and the part of the next
block's last twelve bytes, computed one block ahead. -/
theorem pipe_body (data : Aeneas.Std.Slice U8) (table : alloc.vec.Vec U32) (c : U32) (p : Usize)
    (x : U32) (ht : Table table 4096) (hp : p.val ≤ data.val.length)
    (hc : c.val = reg data.val p.val)
    (hx : p.val + 16 ≤ data.val.length → x.val = rest data.val p.val) :
    crc32_loop2.body data table c p x ⦃ r =>
      match r with
      | .done (d, m, y) => d.val = reg data.val m.val ∧ m.val ≤ data.val.length ∧
          (m.val + 16 ≤ data.val.length → y.val = rest data.val m.val)
      | .cont (d, m, y) => d.val = reg data.val m.val ∧ m.val = p.val + 16 ∧
          m.val ≤ data.val.length ∧ (m.val + 16 ≤ data.val.length → y.val = rest data.val m.val) ⦄ := by
  unfold crc32_loop2.body
  step*
  · have hp16 : p.val + 16 ≤ data.val.length := by scalar_tac
    refine ⟨?_, i3_post, by scalar_tac, fun _ => by rw [next_post]⟩
    have hw : w0.val = c.val ^^^ i2.val := by rw [w0_post, UScalar.val_xor]
    rw [c1_post, UScalar.val_xor, i4_post, hx hp16, i3_post, hw]
    exact reg_split data.val p.val hp16 c.val i2.val hc i2_post
  all_goals exact ⟨hc, hp, hx⟩

@[step]
theorem pipe_loop (data : Aeneas.Std.Slice U8) (table : alloc.vec.Vec U32) (c : U32) (p : Usize)
    (x : U32) (ht : Table table 4096) (hp : p.val ≤ data.val.length)
    (hc : c.val = reg data.val p.val)
    (hx : p.val + 16 ≤ data.val.length → x.val = rest data.val p.val) :
    crc32_loop2 data table c p x ⦃ r =>
      r.1.val = reg data.val r.2.1.val ∧ r.2.1.val ≤ data.val.length ∧
        (r.2.1.val + 16 ≤ data.val.length → r.2.2.val = rest data.val r.2.1.val) ⦄ := by
  unfold crc32_loop2
  apply loop.spec_decr_nat (fun (_, m, _) => data.val.length - m.val)
    (fun (d, m, y) => m.val ≤ data.val.length ∧ d.val = reg data.val m.val ∧
      (m.val + 16 ≤ data.val.length → y.val = rest data.val m.val))
  · rintro ⟨d, m, y⟩ ⟨hm, hh, hy⟩
    refine WP.spec_mono (pipe_body data table d m y ht hm hh hy) ?_
    intro r hr
    cases r with
    | done state =>
        obtain ⟨d', m', y'⟩ := state
        exact hr
    | cont state =>
        obtain ⟨d', k, y'⟩ := state
        obtain ⟨hd, hk, hkbound, hy'⟩ := hr
        simp only at *
        exact ⟨⟨hkbound, hd, hy'⟩, by omega⟩
  · exact ⟨hp, hc, hx⟩

-- ================================================================ the last bytes

theorem data_body (data : Aeneas.Std.Slice U8) (table : alloc.vec.Vec U32) (c : U32) (p : Usize)
    (ht : Table table 4096) (hp : p.val ≤ data.val.length)
    (hc : c.val = reg data.val p.val) :
    crc32_loop3.body data table c p ⦃ r =>
      match r with
      | .done d => d.val = reg data.val data.val.length
      | .cont (d, m) => d.val = reg data.val m.val ∧
          m.val = p.val + 1 ∧ p.val < data.val.length ⦄ := by
  unfold crc32_loop3.body
  step*
  · have h5 : i5.val = i4.val % 256 := by
      rw [i5_post, UScalar.val_and]
      change i4.val &&& 255 = i4.val % 256
      exact Nat.and_two_pow_sub_one_eq_mod i4.val 8
    have h6 : i6.val = i5.val := by
      rw [i6_post]
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      scalar_tac
    simp only [alloc.vec.Vec.length]
    rw [ht.1, h6, h5]
    have := Nat.mod_lt i4.val (show 0 < 256 by decide)
    omega
  · have hplen : p.val < data.val.length := by
      have hp' := (UScalar.lt_equiv p (Aeneas.Std.Slice.len data)).mp (by assumption)
      simpa only [Aeneas.Std.Slice.len_val, Aeneas.Std.Slice.length] using hp'
    have h5 : i5.val = i4.val % 256 := by
      rw [i5_post, UScalar.val_and]
      change i4.val &&& 255 = i4.val % 256
      exact Nat.and_two_pow_sub_one_eq_mod i4.val 8
    have h6 : i6.val = i5.val := by
      rw [i6_post]
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      scalar_tac
    have h6bound : i6.val < 256 := by rw [h6, h5]; exact Nat.mod_lt _ (by decide)
    have h7 : i7.val = bits i6.val 8 := by
      have hk : i6.val < table.val.length := by rw [ht.1]; omega
      rw [i7_post, ← getElem!_pos table.val i6.val hk, ht.2 i6.val (by omega),
        Nat.mod_eq_of_lt h6bound, Nat.div_eq_of_lt h6bound]
    have h3 : i3.val = i2.val := by
      rw [i3_post]
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      scalar_tac
    have h4 : i4.val = c.val ^^^ i2.val := by rw [i4_post, UScalar.val_xor, h3]
    have hbyte : i2 = data.val[p.val]! := by
      rw [i2_post, getElem!_pos data.val p.val hplen]
    refine ⟨?_, p1_post, hplen⟩
    rw [c1_post, UScalar.val_xor, i1_post, Nat.shiftRight_eq_div_pow, h7, h6, h5, h4]
    change c.val / 256 ^^^ bits ((c.val ^^^ i2.val) % 256) 8 = reg data.val p1.val
    rw [p1_post, reg, ← hc, ← hbyte, table_byte]


@[step]
theorem data_loop (data : Aeneas.Std.Slice U8) (table : alloc.vec.Vec U32) (c : U32) (p : Usize)
    (ht : Table table 4096) (hp : p.val ≤ data.val.length)
    (hc : c.val = reg data.val p.val) :
    crc32_loop3 data table c p ⦃ d => d.val = reg data.val data.val.length ⦄ := by
  unfold crc32_loop3
  apply loop.spec_decr_nat (fun (_, m) => data.val.length - m.val)
    (fun (d, m) => m.val ≤ data.val.length ∧ d.val = reg data.val m.val)
  · rintro ⟨d, m⟩ ⟨hm, hh⟩
    refine WP.spec_mono (data_body data table d m ht hm hh) ?_
    intro r hr
    cases r with
    | done d => exact hr
    | cont state =>
        obtain ⟨d, k⟩ := state
        obtain ⟨hd, hk, hkbound⟩ := hr
        simp only at *
        exact ⟨⟨by omega, hd⟩, by omega⟩
  · exact ⟨hp, hc⟩

theorem correct (data : Aeneas.Std.Slice U8) :
    Gzip.solution.crc32 data ⦃ c => Gzip.Spec.crc32_spec data.val c ⦄ := by
  unfold Gzip.solution.crc32
  have ht0 : Table (alloc.vec.Vec.with_capacity U32 4096#usize) 0 := by
    simp [Table, alloc.vec.Vec.with_capacity]
  step as ⟨table, htable⟩
  have hk : 256 ≤ (256#usize).val ∧ (256#usize).val ≤ 4096 := by simp
  step as ⟨table1, htable1⟩
  have hc0 : (4294967295#u32).val = reg data.val (0#usize).val := rfl
  have hx0 : (if Slice.len data >= 16#usize then crc_rest data table1 0#usize else ok 0#u32) ⦃ x =>
      (0#usize).val + 16 ≤ data.val.length → x.val = rest data.val (0#usize).val ⦄ := by
    split
    · rename_i h
      have h16 : 16 ≤ data.val.length := by scalar_tac
      exact WP.spec_mono (rest_spec data table1 0#usize htable1 (by simpa using h16))
        (fun r hr _ => hr)
    · rename_i h
      simp only [WP.spec_ok]
      intro h16
      exfalso
      apply h
      scalar_tac
  step with hx0 as ⟨x, hx⟩
  step as ⟨c, p, x1, hcp, hpl, hx1⟩
  step as ⟨i2, hi2⟩
  split
  · rename_i h16
    have hp16 : p.val + 16 ≤ data.val.length := by scalar_tac
    step as ⟨i3, hi3⟩
    step as ⟨w0, hw0⟩
    step as ⟨i4, hi4⟩
    step as ⟨c2, hc2⟩
    step as ⟨p2, hp2⟩
    have hreg : c2.val = reg data.val p2.val := by
      have hw : w0.val = c.val ^^^ i3.val := by rw [hw0, UScalar.val_xor]
      rw [hc2, UScalar.val_xor, hi4, hx1 hp16, hp2, hw]
      exact reg_split data.val p.val hp16 c.val i3.val hcp hi3
    step as ⟨c1, hc1⟩
    try simp only [WP.spec_ok]
    refine ⟨trivial, reg data.val data.val.length,
      reg_spec data.val data.val.length (by omega),
      (reg data.val data.val.length ^^^ 4294967295 : ℕ),
      xor_nat _ _, ?_⟩
    simp [UScalar.val_xor, hc1]
  · step as ⟨c1, hc1⟩
    try simp only [WP.spec_ok]
    refine ⟨trivial, reg data.val data.val.length,
      reg_spec data.val data.val.length (by omega),
      (reg data.val data.val.length ^^^ 4294967295 : ℕ),
      xor_nat _ _, ?_⟩
    simp [UScalar.val_xor, hc1]

end Gzip.Proofs.Crc
