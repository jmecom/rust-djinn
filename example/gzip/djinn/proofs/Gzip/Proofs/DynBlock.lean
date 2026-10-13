import Gzip.Proofs.Build
import Gzip.Proofs.Stored
import Gzip.Proofs.Fused
import Gzip.Proofs.Counting

open Aeneas Std Result
open Gzip.solution Gzip.Spec Gzip.Proofs.Writer Gzip.Proofs.Plans Gzip.Proofs.Runtime
open Gzip.Proofs.Codes Gzip.Proofs.Header Gzip.Proofs.Dyn Gzip.Proofs.Build Gzip.Proofs.Matches
open Gzip.Proofs.Indices

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

namespace Gzip.Proofs.DynBlock

theorem space' (w : Gzip.solution.Writer) (n : ℕ)
    (h : (stream w).length + 8 * n ≤ 34359738360) :
    w.out.val.length + n ≤ Usize.max := by
  simp only [stream_length] at h
  scalar_tac

def tab (c : Code) : Tab := ⟨c.lens.val, c.words.val⟩

theorem cast_u32_val (x : U8) : (UScalar.cast .U32 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by scalar_tac)

theorem cast_u32_usize_val (x : Usize) (hx : x.val < 4294967296) : (UScalar.cast .U32 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by scalar_tac)

theorem cast_usize_u8_val (x : U8) : (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by scalar_tac)

/-- A copy's two packed fields use one writer update when their combined width fits. -/
theorem pair_stream (self : Gzip.solution.Writer) (first firstCount second secondCount : U32)
    (hc : self.count.val < 32) (hw : self.bits.val < 2 ^ self.count.val)
    (hf : firstCount.val < 32) (hs : secondCount.val ≤ 32)
    (hfv : first.val < 2 ^ firstCount.val) (hsv : second.val < 2 ^ secondCount.val)
    (hb : self.out.val.length + 12 ≤ Usize.max) :
    Gzip.solution.Writer.pair self first firstCount second secondCount ⦃ r =>
      stream r = stream self ++
        (lowBits first.val firstCount.val ++ lowBits second.val secondCount.val) ∧
        r.count.val < 32 ∧ r.bits.val < 2 ^ r.count.val ⦄ := by
  unfold Gzip.solution.Writer.pair
  step as ⟨count, hcount⟩
  split
  · rename_i hfit
    have hfit' : count.val ≤ 32 := by scalar_tac
    unfold Gzip.solution.Writer.bits2
    step as ⟨shift, hshift⟩
    step as ⟨joined, hjoined⟩
    step as ⟨width, hwidth⟩
    have hjv : joined.val = first.val ||| ((second.val * 2 ^ firstCount.val) % 4294967296) := by
      rw [hjoined, UScalar.val_or, hshift]
      simp only [Nat.shiftLeft_eq, U32.size, U32.numBits_eq]
      rfl
    have hjb : joined.val < 2 ^ width.val := by
      rw [hjv, hwidth]
      exact joined_bound _ _ _ _ hfv hsv
    have hwidth' : width.val ≤ 32 := by omega
    have hbits := bits_stream self joined width hc hw hwidth' hjb (by scalar_tac)
    refine WP.spec_mono hbits ?_
    intro r ⟨hstream, hc', hw'⟩
    refine ⟨?_, hc', hw'⟩
    rw [hjv, hwidth, lowBits_put _ _ _ _ hfv (by omega)] at hstream
    exact hstream
  · rename_i hwide
    have hbits := bits_stream self first firstCount hc hw (by omega) hfv (by scalar_tac)
    step as ⟨middle, hstream, hcm, hwm⟩
    change stream middle = stream self ++ lowBits first.val firstCount.val at hstream
    have hlen := congrArg List.length hstream
    simp only [stream_length, List.length_append, lowBits_length] at hlen
    have hspace : middle.out.val.length + (middle.count.val + secondCount.val) / 8 ≤ Usize.max := by
      omega
    have hbits' := bits_stream middle second secondCount hcm hwm hs hsv hspace
    refine WP.spec_mono hbits' ?_
    intro r ⟨hstream', hc', hw'⟩
    refine ⟨?_, hc', hw'⟩
    change stream r = stream middle ++ lowBits second.val secondCount.val at hstream'
    rw [hstream', hstream, List.append_assoc]

/-! ### The code-length lengths -/

theorem cl_body (c : Code) (hclen : Usize) (w : Gzip.solution.Writer) (k : Usize) (front : List Bool)
    (hcl : c.lens.val.length = 19) (hb7 : ∀ s < 19, (c.lens.val[s]!).val ≤ 7)
    (hh : hclen.val ≤ 19) (hk : k.val ≤ hclen.val) (hw : Buffered w)
    (hs : stream w = front ++ clBits c.lens.val k.val)
    (hbudget : front.length + 200 ≤ 34359738360) :
    dynamic_loop0.body c hclen w k ⦃ r =>
      match r with
      | .done (w', c') => c' = c ∧ Buffered w' ∧ stream w' = front ++ clBits c.lens.val hclen.val
      | .cont (w', k') => k'.val = k.val + 1 ∧ k'.val ≤ hclen.val ∧ Buffered w' ∧
          stream w' = front ++ clBits c.lens.val k'.val ⦄ := by
  have hslen : (stream w).length = front.length + 3 * k.val := by
    rw [hs, List.length_append, clBits_length]
  unfold dynamic_loop0.body
  split
  · rename_i hlt
    have hlt' : k.val < hclen.val := by scalar_tac
    have hk19 : k.val < 19 := by omega
    have hklen : k.val < CL_ORDER.val.length := by rw [cl_order_len]; exact hk19
    step as ⟨i1, hi1⟩
    have hi1v : i1.val = clOrder[k.val]! := by
      rw [hi1, ← getElem!_pos CL_ORDER.val k.val hklen]
      have := cl_order_table ⟨k.val, hk19⟩
      simpa using this
    have hi1l : i1.val < c.lens.val.length := by rw [hcl, hi1v]; exact clOrder_lt k.val hk19
    step as ⟨i2, hi2⟩
    have hi2v : i2 = c.lens.val[clOrder[k.val]!]! := by
      rw [hi2, ← getElem!_pos c.lens.val i1.val hi1l, hi1v]
    step as ⟨i3, hi3⟩
    have hi3v : i3.val = (c.lens.val[clOrder[k.val]!]!).val := by rw [hi3, cast_u32_val, hi2v]
    have hi3b : i3.val < 2 ^ (3#u32).val := by
      rw [hi3v]
      have := hb7 (clOrder[k.val]!) (clOrder_lt k.val hk19)
      scalar_tac
    have hspace : w.out.val.length + 8 ≤ Usize.max := space' w 8 (by omega)
    have hcw := hw.1
    have hbits := bits_stream w i3 3#u32 hw.1 hw.2 (by scalar_tac) hi3b (by scalar_tac)
    step as ⟨w1, hstream1, hc1, hw1⟩
    step as ⟨k1, hk1⟩
    try simp only [WP.spec_ok]
    refine ⟨hk1, by omega, ⟨hc1, hw1⟩, ?_⟩
    change stream w1 = stream w ++ lowBits i3.val (3#u32).val at hstream1
    rw [hstream1, hs, hk1, hi3v, List.append_assoc]
    rfl
  · rename_i hge
    have he : k.val = hclen.val := by scalar_tac
    try simp only [WP.spec_ok]
    refine ⟨by first | trivial | rfl, hw, ?_⟩
    rw [hs, he]

@[step]
theorem cl_loop (c : Code) (hclen : Usize) (w : Gzip.solution.Writer) (k : Usize) (front : List Bool)
    (hcl : c.lens.val.length = 19) (hb7 : ∀ s < 19, (c.lens.val[s]!).val ≤ 7)
    (hh : hclen.val ≤ 19) (hk : k.val ≤ hclen.val) (hw : Buffered w)
    (hs : stream w = front ++ clBits c.lens.val k.val)
    (hbudget : front.length + 200 ≤ 34359738360) :
    dynamic_loop0 w c hclen k ⦃ r => r.2 = c ∧ Buffered r.1 ∧
      stream r.1 = front ++ clBits c.lens.val hclen.val ⦄ := by
  unfold dynamic_loop0
  apply loop.spec_decr_nat (fun (_, k') => hclen.val - k'.val)
    (fun (w', k') => k'.val ≤ hclen.val ∧ Buffered w' ∧ stream w' = front ++ clBits c.lens.val k'.val)
  · rintro ⟨w', k'⟩ ⟨hk', hw', hs'⟩
    refine WP.spec_mono (cl_body c hclen w' k' front hcl hb7 hh hk' hw' hs' hbudget) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨w'', k''⟩ := state
        obtain ⟨h1, h2, h3, h4⟩ := hr
        exact ⟨⟨h2, h3, h4⟩, by change hclen.val - k''.val < hclen.val - k'.val; omega⟩
  · exact ⟨hk, hw, hs⟩

/-! ### The run-length coded lengths -/

theorem item_extra_spec (w : Gzip.solution.Writer) (s : Usize) (e : U32) (hw : Buffered w)
    (he : s.val < 16 ∨ e.val < 2 ^ extraWidth s.val) (hspace : w.out.val.length + 8 ≤ Usize.max) :
    item_extra w s e ⦃ r => Buffered r ∧ stream r = stream w ++ lowBits e.val (extraWidth s.val) ⦄ := by
  have hcw := hw.1
  unfold item_extra
  split
  · rename_i h16
    have hs16 : s.val = 16 := by have := (UScalar.eq_equiv _ _).mp h16; simpa using this
    have hwidth : extraWidth s.val = 2 := by simp [extraWidth, hs16]
    have hev : e.val < 2 ^ (2#u32).val := by
      rcases he with h | h
      · omega
      · rw [hwidth] at h; scalar_tac
    have hbits := bits_stream w e 2#u32 hw.1 hw.2 (by scalar_tac) hev (by scalar_tac)
    step as ⟨w1, hstream1, hc1, hw1⟩
    refine ⟨⟨hc1, hw1⟩, ?_⟩
    change stream w1 = stream w ++ lowBits e.val (2#u32).val at hstream1
    rw [hstream1, hwidth]
    rfl
  · rename_i h16
    split
    · rename_i h17
      have hs17 : s.val = 17 := by have := (UScalar.eq_equiv _ _).mp h17; simpa using this
      have hwidth : extraWidth s.val = 3 := by simp [extraWidth, hs17]
      have hev : e.val < 2 ^ (3#u32).val := by
        rcases he with h | h
        · omega
        · rw [hwidth] at h; scalar_tac
      have hbits := bits_stream w e 3#u32 hw.1 hw.2 (by scalar_tac) hev (by scalar_tac)
      step as ⟨w1, hstream1, hc1, hw1⟩
      refine ⟨⟨hc1, hw1⟩, ?_⟩
      change stream w1 = stream w ++ lowBits e.val (3#u32).val at hstream1
      rw [hstream1, hwidth]
      rfl
    · rename_i h17
      split
      · rename_i h18
        have hs18 : s.val = 18 := by have := (UScalar.eq_equiv _ _).mp h18; simpa using this
        have hwidth : extraWidth s.val = 7 := by simp [extraWidth, hs18]
        have hev : e.val < 2 ^ (7#u32).val := by
          rcases he with h | h
          · omega
          · rw [hwidth] at h; scalar_tac
        have hbits := bits_stream w e 7#u32 hw.1 hw.2 (by scalar_tac) hev (by scalar_tac)
        step as ⟨w1, hstream1, hc1, hw1⟩
        refine ⟨⟨hc1, hw1⟩, ?_⟩
        change stream w1 = stream w ++ lowBits e.val (7#u32).val at hstream1
        rw [hstream1, hwidth]
        rfl
      · rename_i h18
        have hn16 : s.val ≠ 16 := fun h => h16 ((UScalar.eq_equiv _ _).mpr (by simp [h]))
        have hn17 : s.val ≠ 17 := fun h => h17 ((UScalar.eq_equiv _ _).mpr (by simp [h]))
        have hn18 : s.val ≠ 18 := fun h => h18 ((UScalar.eq_equiv _ _).mpr (by simp [h]))
        have hwidth : extraWidth s.val = 0 := by simp [extraWidth, hn16, hn17, hn18]
        try simp only [WP.spec_ok]
        refine ⟨hw, ?_⟩
        rw [hwidth]
        simp [lowBits]

theorem covers_head {all : List U8} {p : ℕ} {s e : Usize} {ss es : List Usize}
    (h : Covers all p (s :: ss) (e :: es)) :
    (s.val < 16 ∨ e.val < 2 ^ extraWidth s.val) ∧ ∃ q, Covers all q ss es := by
  cases h with
  | lit _ _ _ _ _ hp hs he tail => exact ⟨Or.inl hs, _, tail⟩
  | rep _ _ _ _ _ hs hp he hn hall tail =>
      refine ⟨Or.inr ?_, _, tail⟩
      rw [hs]
      simpa [extraWidth] using he
  | zeros _ _ _ _ _ hs he hn hz tail =>
      refine ⟨Or.inr ?_, _, tail⟩
      rw [hs]
      simpa [extraWidth] using he
  | zeros2 _ _ _ _ _ hs he hn hz tail =>
      refine ⟨Or.inr ?_, _, tail⟩
      rw [hs]
      simpa [extraWidth] using he

theorem items_body (all : List U8) (c : Code) (ss es : alloc.vec.Vec Usize) (front : List Bool)
    (w : Gzip.solution.Writer) (i : Usize)
    (hcode : Canon.CodeOk c 7) (hcl : c.lens.val.length = 19) (hu : Usable c.lens.val ss.val)
    (hlen : ss.val.length = es.val.length) (hsmall : ss.val.length ≤ 1024)
    (hcov : ∃ p, Covers all p (ss.val.drop i.val) (es.val.drop i.val))
    (hi : i.val ≤ ss.val.length) (hw : Buffered w)
    (hs : stream w = front ++ itemsBits (tab c) (ss.val.take i.val) (es.val.take i.val))
    (hbudget : front.length + 14 * ss.val.length + 80 ≤ 34359738360) :
    dynamic_loop1.body c ss es w i ⦃ r =>
      match r with
      | .done w' => Buffered w' ∧ stream w' = front ++ itemsBits (tab c) ss.val es.val
      | .cont (w', i') => i'.val = i.val + 1 ∧ i'.val ≤ ss.val.length ∧
          (∃ p, Covers all p (ss.val.drop i'.val) (es.val.drop i'.val)) ∧ Buffered w' ∧
          stream w' = front ++ itemsBits (tab c) (ss.val.take i'.val) (es.val.take i'.val) ⦄ := by
  have hb7 : ∀ s < 19, (c.lens.val[s]!).val ≤ 7 := fun s hs => hcode.kraft.1 s (by rw [hcl]; exact hs)
  have hitems_le : ∀ (ss' es' : List Usize), Usable c.lens.val ss' →
      (itemsBits (tab c) ss' es').length ≤ 14 * ss'.length := by
    intro ss' es' hu'
    induction ss' generalizing es' with
    | nil => simp
    | cons s ss ih =>
        cases es' with
        | nil => simp
        | cons e es =>
            simp only [itemsBits_cons, List.length_append, itemBits, encodeSym_length, lowBits_length,
              List.length_cons]
            have h1 := ih es (fun x hx => hu' x (List.mem_cons_of_mem _ hx))
            have h2 := hu' s (List.mem_cons_self ..)
            have h3 : (c.lens.val[s.val]!).val ≤ 7 := hb7 s.val (by rw [← hcl]; exact h2.1)
            have h4 : extraWidth s.val ≤ 7 := by unfold extraWidth; split_ifs <;> omega
            change (c.lens.val[s.val]!).val + extraWidth s.val + _ ≤ 14 * (ss.length + 1)
            omega
  have hslen : (stream w).length ≤ front.length + 14 * i.val := by
    rw [hs, List.length_append]
    have := hitems_le (ss.val.take i.val) (es.val.take i.val)
      (fun x hx => hu x (List.mem_of_mem_take hx))
    rw [List.length_take] at this
    omega
  unfold dynamic_loop1.body
  dsimp only
  split
  · rename_i hlt
    have hlt' : i.val < ss.val.length := by scalar_tac
    have hlte : i.val < es.val.length := by rw [← hlen]; exact hlt'
    step as ⟨s, hsget⟩
    step as ⟨i2, hi2⟩
    step as ⟨e, he⟩
    have hsv : s = ss.val[i.val]! := by rw [hsget, getElem!_pos ss.val i.val hlt']
    have hi2v : i2 = es.val[i.val]! := by rw [hi2, getElem!_pos es.val i.val hlte]
    obtain ⟨p, hcovp⟩ := hcov
    rw [List.drop_eq_getElem_cons hlt', List.drop_eq_getElem_cons hlte, ← getElem!_pos ss.val i.val hlt',
      ← getElem!_pos es.val i.val hlte, ← hsv, ← hi2v] at hcovp
    obtain ⟨hextra, q, hcovq⟩ := covers_head hcovp
    have hus := hu s (by rw [hsv]; exact Djinn.Vocab.getElem!_mem ss.val i.val hlt')
    have hs19 : s.val < c.rev.val.length := by rw [hcode.rev]; exact hus.1
    step as ⟨i3, hi3⟩
    have hs19' : s.val < c.lens.val.length := hus.1
    step as ⟨i4, hi4⟩
    step as ⟨i5, hi5⟩
    have hi5v : i5.val = (c.lens.val[s.val]!).val := by
      rw [hi5, cast_u32_val, hi4, getElem!_pos c.lens.val s.val hs19']
    have hi3v : i3 = c.rev.val[s.val]! := by rw [hi3, getElem!_pos c.rev.val s.val hs19]
    have hl16 : (c.lens.val[s.val]!).val ≤ 16 := by have := hb7 s.val (by rw [← hcl]; exact hus.1); omega
    have hi3b : i3.val < 2 ^ i5.val := by
      rw [hi3v, hi5v]
      exact rev_bound c.lens.val c.words.val c.rev.val s.val hcode.reversed hus.1 hus.2 hl16
    have hspace : w.out.val.length + 8 ≤ Usize.max := space' w 8 (by omega)
    have hcw := hw.1
    have hbits := bits_stream w i3 i5 hw.1 hw.2 (by rw [hi5v]; omega) hi3b (by scalar_tac)
    step as ⟨w1, hstream1, hc1, hw1⟩
    change stream w1 = stream w ++ lowBits i3.val i5.val at hstream1
    have hrev : lowBits i3.val i5.val = encodeSym c.lens.val c.words.val s.val := by
      rw [hi3v, hi5v]
      exact rev_bits c.lens.val c.words.val c.rev.val s.val hcode.reversed hus.1 hus.2 hl16
    have hev : e.val = i2.val ∨ s.val < 16 := by
      rcases hextra with h | h
      · exact Or.inr h
      · left
        rw [he]
        apply cast_u32_usize_val
        have : extraWidth s.val ≤ 7 := by unfold extraWidth; split_ifs <;> omega
        have h2 : 2 ^ extraWidth s.val ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) this
        omega
    have hextra' : s.val < 16 ∨ e.val < 2 ^ extraWidth s.val := by
      rcases hev with h | h
      · rcases hextra with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by rw [h]; exact h')
      · exact Or.inl h
    have hstream1len : (stream w1).length ≤ front.length + 14 * i.val + 7 := by
      rw [hstream1, List.length_append, lowBits_length, hi5v]
      have := hb7 s.val (by rw [← hcl]; exact hus.1)
      omega
    have hspace1 : w1.out.val.length + 8 ≤ Usize.max := space' w1 8 (by omega)
    have hie := item_extra_spec w1 s e ⟨hc1, hw1⟩ hextra' hspace1
    step as ⟨w2, hw2, hstream2⟩
    step as ⟨i6, hi6⟩
    try simp only [WP.spec_ok]
    refine ⟨hi6, by omega, ⟨q, by rw [hi6]; exact hcovq⟩, hw2, ?_⟩
    have hitem : lowBits i3.val i5.val ++ lowBits e.val (extraWidth s.val) = itemBits (tab c) s.val i2.val := by
      rw [hrev]
      unfold itemBits
      congr 1
      rcases hev with h | h
      · rw [h]
      · have hw0 : extraWidth s.val = 0 := by unfold extraWidth; split_ifs <;> omega
        rw [hw0]
        simp [lowBits]
    rw [hstream2, hstream1, hs, hi6, List.take_succ_eq_append_getElem hlt', List.take_succ_eq_append_getElem hlte,
      itemsBits_append (tab c) _ _ _ _ (by simp [List.length_take]; omega), ← getElem!_pos ss.val i.val hlt',
      ← getElem!_pos es.val i.val hlte, ← hsv, ← hi2v]
    simp only [itemsBits_cons, itemsBits_nil, List.append_nil, List.append_assoc]
    rw [hitem]
  · rename_i hge
    have he : i.val = ss.val.length := by scalar_tac
    try simp only [WP.spec_ok]
    refine ⟨hw, ?_⟩
    rw [hs, he, List.take_length, hlen, List.take_length]

@[step]
theorem items_loop (all : List U8) (c : Code) (ss es : alloc.vec.Vec Usize) (front : List Bool)
    (w : Gzip.solution.Writer) (i : Usize)
    (hcode : Canon.CodeOk c 7) (hcl : c.lens.val.length = 19) (hu : Usable c.lens.val ss.val)
    (hlen : ss.val.length = es.val.length) (hsmall : ss.val.length ≤ 1024)
    (hcov : ∃ p, Covers all p (ss.val.drop i.val) (es.val.drop i.val))
    (hi : i.val ≤ ss.val.length) (hw : Buffered w)
    (hs : stream w = front ++ itemsBits (tab c) (ss.val.take i.val) (es.val.take i.val))
    (hbudget : front.length + 14 * ss.val.length + 80 ≤ 34359738360) :
    dynamic_loop1 w c ss es i ⦃ r => Buffered r ∧ stream r = front ++ itemsBits (tab c) ss.val es.val ⦄ := by
  unfold dynamic_loop1
  apply loop.spec_decr_nat (fun (_, i') => ss.val.length - i'.val)
    (fun (w', i') => i'.val ≤ ss.val.length ∧ (∃ p, Covers all p (ss.val.drop i'.val) (es.val.drop i'.val)) ∧
      Buffered w' ∧ stream w' = front ++ itemsBits (tab c) (ss.val.take i'.val) (es.val.take i'.val))
  · rintro ⟨w', i'⟩ ⟨hi', hcov', hw', hs'⟩
    refine WP.spec_mono (items_body all c ss es front w' i' hcode hcl hu hlen hsmall hcov' hi' hw' hs' hbudget) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨w'', i''⟩ := state
        obtain ⟨h1, h2, h3, h4, h5⟩ := hr
        exact ⟨⟨h2, h3, h4, h5⟩, by change ss.val.length - i''.val < ss.val.length - i'.val; omega⟩
  · exact ⟨hi, hcov, hw, hs⟩

/-! ### The tokens -/

structure TokState (data : List U8) (start stop : ℕ) (front : List Bool) (ls ds : List U16)
    (lit dist : Code) (w : Gzip.solution.Writer) (p t : Usize) : Prop where
  position : start ≤ p.val ∧ p.val ≤ stop ∧ stop ≤ data.length
  located : p.val = Body.pos ls start t.val
  lengths : ls.length = ds.length
  index : t.val ≤ ls.length
  runs : Runs data stop p.val stop (ls.drop t.val) (ds.drop t.val)
  buffer : Buffered w
  emitted : ∃ bits, stream w = front ++ bits ∧ bits.length ≤ 16 * (p.val - start) ∧
    Emitted (tab lit) (tab dist) data start p.val bits

theorem tok_body (data : Aeneas.Std.Slice U8) (start stop : ℕ) (front : List Bool)
    (ls ds : alloc.vec.Vec U16) (lsym dsym : alloc.vec.Vec U8) (lit dist : Code) (w : Gzip.solution.Writer) (p t : Usize)
    (hsym : Symbolize.Symbolized ls.val ds.val lsym.val dsym.val)
    (husable : Body.Usable data.val start ls.val ds.val lsym.val dsym.val lit.lens.val dist.lens.val)
    (hlit : Canon.CodeOk lit 15) (hdist : Canon.CodeOk dist 15)
    (h : TokState data.val start stop front ls.val ds.val lit dist w p t)
    (hbudget : front.length + 16 * (stop - start) + 80 ≤ 34359738360) :
    dynamic_loop2.body data ls ds lsym dsym lit.lens lit.rev dist.lens dist.rev w p t ⦃ r =>
      match r with
      | .done w' => Buffered w' ∧ ∃ bits, stream w' = front ++ bits ∧ bits.length ≤ 16 * (stop - start) ∧
          Emitted (tab lit) (tab dist) data.val start stop bits
      | .cont (w', p', t') => TokState data.val start stop front ls.val ds.val lit dist w' p' t' ∧
          t'.val = t.val + 1 ⦄ := by
  obtain ⟨hp, hloc, hlen, ht, hr, hb, bits, hstream, hsize, hemit⟩ := h
  have hc := hb.1
  have hw := hb.2
  have hslen := congrArg List.length hstream
  simp only [List.length_append] at hslen
  have hspace : w.out.val.length + 8 ≤ Usize.max := space' w 8 (by omega)
  unfold dynamic_loop2.body
  dsimp only
  split
  · rename_i hlt
    have hlt' : t.val < ls.val.length := by scalar_tac
    obtain ⟨hstep, htail⟩ := Tokens.runs_head hr hlt' hlen
    have hpos := step_positive hstep
    have hpend := runs_bound htail
    step as ⟨rawlen, hlenget⟩
    step as ⟨len, hlcast⟩
    step as ⟨rawdist, hdistget⟩
    step as ⟨dist0, hdcast⟩
    have hlget : len.val = (ls.val[t.val]!).val := by
      rw [hlcast]
      change (widen rawlen).val = _
      rw [widen_val, hlenget, getElem!_pos ls.val t.val hlt']
    have hdget : dist0.val = (ds.val[t.val]!).val := by
      rw [hdcast]
      change (widen rawdist).val = _
      rw [widen_val, hdistget, getElem!_pos ds.val t.val (by omega)]
    simp only [Step] at hstep
    rw [← hlget, ← hdget] at hstep
    rw [← hlget] at htail hpos hpend
    have hus := husable.1 t.val hlt'
    unfold Body.UsableAt at hus
    split
    · rename_i hz
      have hdz : dist0.val = 0 := by scalar_tac
      have hdz' : (ds.val[t.val]!).val = 0 := by rw [← hdget]; exact hdz
      rw [if_pos hdz', ← hloc] at hus
      have hlone : len.val = 1 := by
        rcases hstep with hstep | ⟨hmatch, hd⟩
        · exact hstep.1
        · omega
      have hpdata : p.val < data.val.length := by omega
      step as ⟨b, hget⟩
      step as ⟨s, hs⟩
      have hbget : b = data.val[p.val]! := by rw [hget, getElem!_pos data.val p.val hpdata]
      have hsv : s.val = (data.val[p.val]!).val := by rw [hs, cast_usize_u8_val, hbget]
      have hsl : s.val < lit.rev.val.length := by rw [hlit.rev, hsv]; exact hus.1
      step as ⟨i2, hi2⟩
      have hsl' : s.val < lit.lens.val.length := by rw [hsv]; exact hus.1
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = (lit.lens.val[s.val]!).val := by
        rw [hi4, cast_u32_val, hi3, getElem!_pos lit.lens.val s.val hsl']
      have hi2v : i2 = lit.rev.val[s.val]! := by rw [hi2, getElem!_pos lit.rev.val s.val hsl]
      have hpos1 : 1 ≤ (lit.lens.val[s.val]!).val := by rw [hsv]; exact hus.2
      have hl16 : (lit.lens.val[s.val]!).val ≤ 16 := by
        have := (hlit.table.2 s.val hsl' hpos1).1; omega
      have hi2b : i2.val < 2 ^ i4.val := by
        rw [hi2v, hi4v]
        exact rev_bound lit.lens.val lit.words.val lit.rev.val s.val hlit.reversed hsl' hpos1 hl16
      have hbits := bits_stream w i2 i4 hc hw (by rw [hi4v]; omega) hi2b (by scalar_tac)
      step as ⟨w', hwstream, hwcount, hwword⟩
      step as ⟨p', hp'⟩
      step as ⟨t', ht'⟩
      change stream w' = stream w ++ lowBits i2.val i4.val at hwstream
      have hrev : lowBits i2.val i4.val = encodeSym lit.lens.val lit.words.val (data.val[p.val]!).val := by
        rw [hi2v, hi4v, ← hsv]
        exact rev_bits lit.lens.val lit.words.val lit.rev.val s.val hlit.reversed hsl' hpos1 hl16
      try simp only [WP.spec_ok]
      refine ⟨⟨⟨by omega, by omega, hp.2.2⟩, ?_, hlen, by omega, ?_,
        ⟨hwcount, hwword⟩, bits ++ encodeSym lit.lens.val lit.words.val (data.val[p.val]!).val, ?_, ?_, ?_⟩, ht'⟩
      · rw [hp', ht', Body.pos_succ ls.val start t.val hlt', hloc, hlget]
      · simpa only [hp', ht', hlone] using htail
      · rw [hwstream, hrev, hstream, List.append_assoc]
      · simp only [List.length_append, encodeSym_length]
        have := (hlit.table.2 s.val hsl' hpos1).1
        rw [hsv] at this
        omega
      · have this : Emitted (tab lit) (tab dist) data.val start (p.val + 1)
            (bits ++ encodeSym lit.lens.val lit.words.val (data.val[p.val]!).val) :=
          Dyn.emitted_literal hemit hpdata ⟨hus.1, hus.2⟩
        simpa only [hp', hlone] using this
    · rename_i hnz
      have hdz : dist0.val ≠ 0 := by scalar_tac
      have hdz' : (ds.val[t.val]!).val ≠ 0 := by rw [← hdget]; exact hdz
      rw [if_neg hdz'] at hus
      have hm : ValidMatch data.val p.val stop len.val dist0.val := by
        rcases hstep with hstep | ⟨hm, _⟩
        · omega
        · exact hm
      rcases hm with hm | hm
      · omega
      obtain ⟨hsl, hsd, hsy⟩ := hsym
      have hsi := hsy t.val hlt' hdz'
      have htl : t.val < lsym.val.length := by rw [hsl]; exact hlt'
      have htd : t.val < dsym.val.length := by rw [hsd]; exact hlt'
      step as ⟨rawl, hl⟩
      step as ⟨l, hlcast⟩
      step as ⟨rawd, hd⟩
      step as ⟨d, hdcast⟩
      have hlv : l.val = (lsym.val[t.val]!).val := by
        rw [hlcast, cast_usize_u8_val, hl, getElem!_pos lsym.val t.val htl]
      have hdv : d.val = (dsym.val[t.val]!).val := by
        rw [hdcast, cast_usize_u8_val, hd, getElem!_pos dsym.val t.val htd]
      rw [← hlv, ← hdv] at hus
      rw [← hlv, ← hdv, ← hlget, ← hdget] at hsi
      obtain ⟨hl28, hd29, hlb, hlf, hdb, hdf⟩ := hsi
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = 257 + l.val := hi1
      have hi1l : i1.val < lit.rev.val.length := by rw [hlit.rev, hi1v]; exact hus.1
      step as ⟨i2, hi2⟩
      have hi1l' : i1.val < lit.lens.val.length := by rw [hi1v]; exact hus.1
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = (lit.lens.val[257 + l.val]!).val := by
        rw [hi4, cast_u32_val, hi3, ← getElem!_pos lit.lens.val i1.val hi1l', hi1v]
      have hi2v : i2 = lit.rev.val[257 + l.val]! := by rw [hi2, ← getElem!_pos lit.rev.val i1.val hi1l, hi1v]
      have hpos1 : 1 ≤ (lit.lens.val[257 + l.val]!).val := hus.2.1
      have hl16 : (lit.lens.val[257 + l.val]!).val ≤ 16 := by
        have := (hlit.table.2 (257 + l.val) hus.1 hpos1).1; omega
      have hi2b : i2.val < 2 ^ i4.val := by
        rw [hi2v, hi4v]
        exact rev_bound lit.lens.val lit.words.val lit.rev.val (257 + l.val) hlit.reversed hus.1 hpos1 hl16
      have hrev1 : lowBits i2.val i4.val = encodeSym lit.lens.val lit.words.val (257 + l.val) := by
        rw [hi2v, hi4v]
        exact rev_bits lit.lens.val lit.words.val lit.rev.val (257 + l.val) hlit.reversed hus.1 hpos1 hl16
      step as ⟨i5, hi5⟩
      have hlget' := lb_get l (by omega)
      have hi5v : i5.val = lb l.val := by rw [hi5, hlget']
      step as ⟨i6, hi6⟩
      step as ⟨i7, hi7⟩
      have hi6v : i6.val = len.val - lb l.val := by rw [hi6, hi5v]
      have hi7v : i7.val = len.val - lb l.val := by
        rw [hi7, cast_u32_usize_val i6 (by rw [hi6v]; omega), hi6v]
      step as ⟨i8, hi8⟩
      have hle := Costs.length_extra_bound l.val (by omega)
      have hll : l.val < LENGTH_EXTRA.val.length := by simp [LENGTH_EXTRA, Array.make]; omega
      rw [getElem!_pos LENGTH_EXTRA.val l.val hll] at hle
      have hi8v : i8.val = le l.val := by
        rw [hi8]
        unfold le
        rw [getElem!_pos LENGTH_EXTRA.val l.val hll]
      have hi7b : i7.val < 2 ^ i8.val := by rw [hi7v, hi8v]; exact hlf
      step as ⟨firstShift, hfirstShift⟩
      step as ⟨first, hfirst⟩
      step as ⟨firstCount, hfirstCount⟩
      have hfirstv : first.val = i2.val ||| ((i7.val * 2 ^ i4.val) % 4294967296) := by
        rw [hfirst, UScalar.val_or, hfirstShift]
        simp only [Nat.shiftLeft_eq, U32.size, U32.numBits_eq]
        rfl
      have hfirstb : first.val < 2 ^ firstCount.val := by
        rw [hfirstv, hfirstCount]
        exact joined_bound _ _ _ _ hi2b hi7b
      have hfirstBits : lowBits first.val firstCount.val = lowBits i2.val i4.val ++ lowBits i7.val i8.val := by
        rw [hfirstv, hfirstCount]
        apply lowBits_put _ _ _ _ hi2b
        rw [hi4v, hi8v]
        unfold le
        rw [getElem!_pos LENGTH_EXTRA.val l.val hll]
        omega
      have hdl : d.val < dist.rev.val.length := by rw [hdist.rev]; exact hus.2.2.1
      step as ⟨i9, hi9⟩
      have hdl' : d.val < dist.lens.val.length := hus.2.2.1
      step as ⟨i10, hi10⟩
      step as ⟨i11, hi11⟩
      have hi11v : i11.val = (dist.lens.val[d.val]!).val := by
        rw [hi11, cast_u32_val, hi10, getElem!_pos dist.lens.val d.val hdl']
      have hi9v : i9 = dist.rev.val[d.val]! := by rw [hi9, getElem!_pos dist.rev.val d.val hdl]
      have hpos2 : 1 ≤ (dist.lens.val[d.val]!).val := hus.2.2.2
      have hd16 : (dist.lens.val[d.val]!).val ≤ 16 := by
        have := (hdist.table.2 d.val hdl' hpos2).1; omega
      have hi9b : i9.val < 2 ^ i11.val := by
        rw [hi9v, hi11v]
        exact rev_bound dist.lens.val dist.words.val dist.rev.val d.val hdist.reversed hdl' hpos2 hd16
      have hrev2 : lowBits i9.val i11.val = encodeSym dist.lens.val dist.words.val d.val := by
        rw [hi9v, hi11v]
        exact rev_bits dist.lens.val dist.words.val dist.rev.val d.val hdist.reversed hdl' hpos2 hd16
      step as ⟨i12, hi12⟩
      have hdget' := db_get d (by omega)
      have hi12v : i12.val = db d.val := by rw [hi12, hdget']
      step as ⟨i13, hi13⟩
      step as ⟨i14, hi14⟩
      have hi13v : i13.val = dist0.val - db d.val := by rw [hi13, hi12v]
      have hi14v : i14.val = dist0.val - db d.val := by
        rw [hi14, cast_u32_usize_val i13 (by rw [hi13v]; omega), hi13v]
      step as ⟨i15, hi15⟩
      have hde := Costs.distance_extra_bound d.val (by omega)
      have hdd : d.val < DIST_EXTRA.val.length := by simp [DIST_EXTRA, Array.make]; omega
      rw [getElem!_pos DIST_EXTRA.val d.val hdd] at hde
      have hi15v : i15.val = de d.val := by
        rw [hi15]
        unfold de
        rw [getElem!_pos DIST_EXTRA.val d.val hdd]
      have hi14b : i14.val < 2 ^ i15.val := by rw [hi14v, hi15v]; exact hdf
      step as ⟨secondShift, hsecondShift⟩
      step as ⟨second, hsecond⟩
      step as ⟨secondCount, hsecondCount⟩
      have hsecondv : second.val = i9.val ||| ((i14.val * 2 ^ i11.val) % 4294967296) := by
        rw [hsecond, UScalar.val_or, hsecondShift]
        simp only [Nat.shiftLeft_eq, U32.size, U32.numBits_eq]
        rfl
      have hsecondb : second.val < 2 ^ secondCount.val := by
        rw [hsecondv, hsecondCount]
        exact joined_bound _ _ _ _ hi9b hi14b
      have hsecondBits : lowBits second.val secondCount.val = lowBits i9.val i11.val ++ lowBits i14.val i15.val := by
        rw [hsecondv, hsecondCount]
        apply lowBits_put _ _ _ _ hi9b
        rw [hi11v, hi15v]
        unfold de
        rw [getElem!_pos DIST_EXTRA.val d.val hdd]
        omega
      have hfirstWidth : firstCount.val < 32 := by
        rw [hfirstCount, hi4v, hi8v]
        unfold le
        rw [getElem!_pos LENGTH_EXTRA.val l.val hll]
        omega
      have hsecondWidth : secondCount.val ≤ 32 := by
        rw [hsecondCount, hi11v, hi15v]
        unfold de
        rw [getElem!_pos DIST_EXTRA.val d.val hdd]
        omega
      have hspace12 : w.out.val.length + 12 ≤ Usize.max := space' w 12 (by omega)
      have hpair := pair_stream w first firstCount second secondCount hc hw hfirstWidth hsecondWidth hfirstb hsecondb hspace12
      step as ⟨w5, hstream5, hc5, hw5⟩
      step as ⟨p', hp'⟩
      step as ⟨t', ht'⟩
      have hencode : stream w5 = stream w ++ encodeCopy (tab lit) (tab dist) len.val dist0.val l.val d.val := by
        rw [hstream5, hfirstBits, hsecondBits, hrev1, hrev2, hi7v, hi8v, hi14v, hi15v]
        simp only [encodeCopy, tab, List.append_assoc]
      have hm' : 3 ≤ len.val ∧ len.val ≤ 258 ∧ p.val + len.val ≤ data.val.length ∧
          0 < dist0.val ∧ dist0.val ≤ p.val ∧ dist0.val ≤ 32768 ∧
          EqualRun data.val p.val (p.val - dist0.val) len.val :=
        ⟨hm.1, hm.2.1, by omega, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1, hm.2.2.2.2.2.2⟩
      have hle5 : le l.val ≤ 5 := by unfold le; rw [getElem!_pos LENGTH_EXTRA.val l.val hll]; omega
      have hde13 : de d.val ≤ 13 := by unfold de; rw [getElem!_pos DIST_EXTRA.val d.val hdd]; omega
      have hlitlen : (lit.lens.val[257 + l.val]!).val ≤ 15 := (hlit.table.2 (257 + l.val) hus.1 hpos1).1
      have hdistlen : (dist.lens.val[d.val]!).val ≤ 15 := (hdist.table.2 d.val hdl' hpos2).1
      try simp only [WP.spec_ok]
      refine ⟨⟨⟨by omega, by omega, hp.2.2⟩, ?_, hlen, by omega, ?_,
        ⟨hc5, hw5⟩, bits ++ encodeCopy (tab lit) (tab dist) len.val dist0.val l.val d.val, ?_, ?_, ?_⟩, ht'⟩
      · rw [hp', ht', Body.pos_succ ls.val start t.val hlt', hloc, hlget]
      · simpa only [hp', ht'] using htail
      · rw [hencode, hstream, List.append_assoc]
      · simp only [List.length_append, encodeCopy, tab, encodeSym_length, lowBits_length]
        omega
      · have := Dyn.emitted_copy (lit := tab lit) (dist := tab dist) hemit hm'
          ⟨hl28, hd29, hlb, hdb, hlf, hdf⟩ ⟨hus.1, hpos1, hdl', hpos2⟩
        simpa only [hp'] using this
  · rename_i hge
    have htend : t.val = ls.val.length := by scalar_tac
    have hpeq : p.val = stop := by
      rw [htend, hlen, List.drop_length, ← hlen, List.drop_length] at hr
      cases hr
      rfl
    try simp only [WP.spec_ok]
    refine ⟨hb, bits, hstream, by omega, ?_⟩
    rw [hpeq] at hemit
    exact hemit

@[step]
theorem tok_loop (data : Aeneas.Std.Slice U8) (start stop : ℕ) (front : List Bool)
    (ls ds : alloc.vec.Vec U16) (lsym dsym : alloc.vec.Vec U8) (lit dist : Code) (w : Gzip.solution.Writer) (p t : Usize)
    (hsym : Symbolize.Symbolized ls.val ds.val lsym.val dsym.val)
    (husable : Body.Usable data.val start ls.val ds.val lsym.val dsym.val lit.lens.val dist.lens.val)
    (hlit : Canon.CodeOk lit 15) (hdist : Canon.CodeOk dist 15)
    (h : TokState data.val start stop front ls.val ds.val lit dist w p t)
    (hbudget : front.length + 16 * (stop - start) + 80 ≤ 34359738360) :
    dynamic_loop2 w data ls ds lsym dsym lit.lens lit.rev dist.lens dist.rev p t ⦃ w' =>
      Buffered w' ∧ ∃ bits, stream w' = front ++ bits ∧ bits.length ≤ 16 * (stop - start) ∧
        Emitted (tab lit) (tab dist) data.val start stop bits ⦄ := by
  unfold dynamic_loop2
  apply loop.spec_decr_nat (fun (_, _, t') => ls.val.length - t'.val)
    (fun (w', p', t') => TokState data.val start stop front ls.val ds.val lit dist w' p' t')
  · rintro ⟨w', p', t'⟩ hi
    refine WP.spec_mono (tok_body data start stop front ls ds lsym dsym lit dist w' p' t' hsym husable hlit hdist hi hbudget) ?_
    intro r hr
    cases r with
    | done w'' => exact hr
    | cont state => exact ⟨hr.1, by have := hr.1.index; have := hr.2; simp only at *; omega⟩
  · exact h

/-! ### The block -/

theorem itemsBits_bound (c : Code) (ss es : List Usize) (hcode : Canon.CodeOk c 7) (hcl : c.lens.val.length = 19)
    (hu : Usable c.lens.val ss) : (itemsBits (tab c) ss es).length ≤ 14 * ss.length := by
  induction ss generalizing es with
  | nil => simp
  | cons s ss ih =>
      cases es with
      | nil => simp
      | cons e es =>
          simp only [itemsBits_cons, List.length_append, itemBits, encodeSym_length, lowBits_length,
            List.length_cons]
          have h1 := ih es (fun x hx => hu x (List.mem_cons_of_mem _ hx))
          have h2 := hu s (List.mem_cons_self ..)
          have h3 : (c.lens.val[s.val]!).val ≤ 7 := hcode.kraft.1 s.val h2.1
          have h4 : extraWidth s.val ≤ 7 := by unfold extraWidth; split_ifs <;> omega
          change (c.lens.val[s.val]!).val + extraWidth s.val + _ ≤ 14 * (ss.length + 1)
          omega

theorem dynamic_correct (data : Aeneas.Std.Slice U8) (start stop : Usize) (w : Gzip.solution.Writer)
    (ls ds : alloc.vec.Vec U16) (lsym dsym : alloc.vec.Vec U8) (tb : Tables) (final : Bool)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length) (hspan : stop.val - start.val ≤ 1048576)
    (hr : Runs data.val stop.val start.val stop.val ls.val ds.val)
    (hsym : Symbolize.Symbolized ls.val ds.val lsym.val dsym.val)
    (htb : TablesOk data.val start.val ls.val ds.val lsym.val dsym.val tb)
    (hb : Buffered w) (hbudget : (stream w).length + 16 * (stop.val - start.val) + 5000 ≤ 34359738360) :
    dynamic w data start ls ds lsym dsym tb final ⦃ r =>
      Buffered r ∧ ∃ bits, stream r = stream w ++ bits ∧
        bits.length ≤ 16 * (stop.val - start.val) + 5000 ∧ 3 ≤ bits.length ∧
        Fragment data.val start.val stop.val (stream w) bits final ⦄ := by
  have hc := hb.1
  have hw := hb.2
  have hspace : w.out.val.length + 8 ≤ Usize.max := space' w 8 (by omega)
  have hlitlen := htb.litLen
  have hdistlen := htb.distLen
  have hcl19 := htb.clLen
  have hlit := htb.lit
  have hdist := htb.dist
  have hcl := htb.cl
  have hitemslen := htb.itemsLen
  have hcovl := covers_lengths htb.covers
  have hib := itemsBits_bound tb.cl tb.syms.val tb.extras.val hcl hcl19 htb.items
  unfold dynamic
  dsimp only
  -- the three-bit block header
  have hheaderSpec : (if final then ok 5#u32 else ok 4#u32) ⦃ h => h.val = (if final then 1 else 0) + 2 * 2 ⦄ := by
    split <;> step*
  step as ⟨header, hh⟩
  have hv : header.val < 2 ^ (3#u32).val := by rw [hh]; split <;> scalar_tac
  have hb1 := bits_stream w header 3#u32 hc hw (by scalar_tac) hv (by scalar_tac)
  step as ⟨w1, hstream1, hc1, hw1⟩
  change stream w1 = stream w ++ lowBits header.val (3#u32).val at hstream1
  have hlen1 : (stream w1).length = (stream w).length + 3 := by
    rw [hstream1, List.length_append, lowBits_length]; simp
  -- HLIT
  step as ⟨i1, hi1⟩
  have hi1v : i1.val = tb.lit.lens.val.length - 257 := by
    rw [hi1]; simp [alloc.vec.Vec.len_val, alloc.vec.Vec.length]
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = tb.lit.lens.val.length - 257 := by
    rw [hi2, cast_u32_usize_val i1 (by rw [hi1v]; omega), hi1v]
  have hi2b : i2.val < 2 ^ (5#u32).val := by rw [hi2v]; scalar_tac
  have hspace1 : w1.out.val.length + 8 ≤ Usize.max := space' w1 8 (by omega)
  have hb2 := bits_stream w1 i2 5#u32 hc1 hw1 (by scalar_tac) hi2b (by scalar_tac)
  step as ⟨w2, hstream2, hc2, hw2⟩
  change stream w2 = stream w1 ++ lowBits i2.val (5#u32).val at hstream2
  have hlen2 : (stream w2).length = (stream w).length + 8 := by
    rw [hstream2, List.length_append, lowBits_length, hlen1]; simp
  -- HDIST
  step as ⟨i4, hi4⟩
  have hi4v : i4.val = tb.dist.lens.val.length - 1 := by
    rw [hi4]; simp [alloc.vec.Vec.len_val, alloc.vec.Vec.length]
  step as ⟨i5, hi5⟩
  have hi5v : i5.val = tb.dist.lens.val.length - 1 := by
    rw [hi5, cast_u32_usize_val i4 (by rw [hi4v]; omega), hi4v]
  have hi5b : i5.val < 2 ^ (5#u32).val := by rw [hi5v]; scalar_tac
  have hspace2 : w2.out.val.length + 8 ≤ Usize.max := space' w2 8 (by omega)
  have hb3 := bits_stream w2 i5 5#u32 hc2 hw2 (by scalar_tac) hi5b (by scalar_tac)
  step as ⟨w3, hstream3, hc3, hw3⟩
  change stream w3 = stream w2 ++ lowBits i5.val (5#u32).val at hstream3
  have hlen3 : (stream w3).length = (stream w).length + 13 := by
    rw [hstream3, List.length_append, lowBits_length, hlen2]; simp
  -- HCLEN
  have hhclen := htb.hclen
  step as ⟨i6, hi6⟩
  have hi6v : i6.val = tb.hclen.val - 4 := hi6
  step as ⟨i7, hi7⟩
  have hi7v : i7.val = tb.hclen.val - 4 := by
    rw [hi7, cast_u32_usize_val i6 (by rw [hi6v]; omega), hi6v]
  have hi7b : i7.val < 2 ^ (4#u32).val := by rw [hi7v]; scalar_tac
  have hspace3 : w3.out.val.length + 8 ≤ Usize.max := space' w3 8 (by omega)
  have hb4 := bits_stream w3 i7 4#u32 hc3 hw3 (by scalar_tac) hi7b (by scalar_tac)
  step as ⟨w4, hstream4, hc4, hw4⟩
  change stream w4 = stream w3 ++ lowBits i7.val (4#u32).val at hstream4
  have hlen4 : (stream w4).length = (stream w).length + 17 := by
    rw [hstream4, List.length_append, lowBits_length, hlen3]; simp
  have hfront4 : stream w4 = stream w ++ lowBits header.val 3 ++ lowBits (tb.lit.lens.val.length - 257) 5 ++
      lowBits (tb.dist.lens.val.length - 1) 5 ++ lowBits (tb.hclen.val - 4) 4 := by
    rw [hstream4, hstream3, hstream2, hstream1, hi2v, hi5v, hi7v]
    simp
  -- the code-length lengths
  have hb7 : ∀ s < 19, (tb.cl.lens.val[s]!).val ≤ 7 := fun s hs => hcl.kraft.1 s (by rw [hcl19]; exact hs)
  have hclloop := cl_loop tb.cl tb.hclen w4 0#usize
    (stream w ++ lowBits header.val 3 ++ lowBits (tb.lit.lens.val.length - 257) 5 ++
      lowBits (tb.dist.lens.val.length - 1) 5 ++ lowBits (tb.hclen.val - 4) 4)
    hcl19 hb7 hhclen.2 (by simp) ⟨hc4, hw4⟩ (by rw [hfront4]; simp [clBits])
    (by simp only [List.length_append, lowBits_length]; omega)
  step as ⟨w5, c, hceq, hw5, hstream5⟩
  subst hceq
  have hlen5 : (stream w5).length = (stream w).length + 17 + 3 * tb.hclen.val := by
    rw [hstream5]; simp <;> omega
  -- the run-length coded lengths
  have hitems := items_loop (tb.lit.lens.val ++ tb.dist.lens.val) tb.cl tb.syms tb.extras
    (stream w ++ lowBits header.val 3 ++ lowBits (tb.lit.lens.val.length - 257) 5 ++
      lowBits (tb.dist.lens.val.length - 1) 5 ++ lowBits (tb.hclen.val - 4) 4 ++
      clBits tb.cl.lens.val tb.hclen.val) w5 0#usize
    hcl hcl19 htb.items hcovl (by omega) ⟨0, by simpa using htb.covers⟩ (by simp) hw5
    (by rw [hstream5]; simp) (by simp only [List.length_append, lowBits_length, clBits_length]; omega)
  step as ⟨w6, hw6, hstream6⟩
  have hlen6 : (stream w6).length ≤ (stream w).length + 17 + 57 + 14 * 316 := by
    rw [hstream6]
    simp only [List.length_append, lowBits_length, clBits_length]
    omega
  -- the tokens
  have hinit : TokState data.val start.val stop.val (stream w6) ls.val ds.val tb.lit tb.dist w6 start 0#usize := by
    refine ⟨⟨Nat.le_refl _, hs, hd⟩, by simp, (runs_lengths hr).1, by simp, by simpa using hr, hw6,
      [], by simp, by simp, Dyn.emitted_nil _ _ _ _⟩
  have htok := tok_loop data start.val stop.val (stream w6) ls ds lsym dsym tb.lit tb.dist w6 start 0#usize hsym
    htb.usable hlit hdist hinit (by omega)
  step as ⟨w7, hw7, tokbits, hstream7, htoklen, hemit⟩
  -- the end-of-block symbol
  have h256 : 256 < tb.lit.rev.val.length := by rw [hlit.rev]; omega
  have h256' : 256 < tb.lit.lens.val.length := by omega
  step as ⟨i8, hi8⟩
  step as ⟨i9, hi9⟩
  step as ⟨i10, hi10⟩
  have hi10v : i10.val = (tb.lit.lens.val[256]!).val := by
    rw [hi10, cast_u32_val, hi9, getElem!_pos tb.lit.lens.val 256 h256']
  have hi8v : i8 = tb.lit.rev.val[256]! := by rw [hi8, getElem!_pos tb.lit.rev.val 256 h256]
  have hpos256 : 1 ≤ (tb.lit.lens.val[256]!).val := htb.usable.2.2
  have hl16 : (tb.lit.lens.val[256]!).val ≤ 16 := by have := (hlit.table.2 256 h256' hpos256).1; omega
  have hi8b : i8.val < 2 ^ i10.val := by
    rw [hi8v, hi10v]
    exact rev_bound _ _ _ 256 hlit.reversed h256' hpos256 hl16
  have hs7len : (stream w7).length ≤ (stream w).length + 17 + 57 + 14 * 316 + 16 * (stop.val - start.val) := by
    rw [hstream7, List.length_append]; omega
  have hspace7 : w7.out.val.length + 8 ≤ Usize.max := space' w7 8 (by omega)
  have hc7 := hw7.1
  have hb8 := bits_stream w7 i8 i10 hw7.1 hw7.2 (by rw [hi10v]; omega) hi8b (by scalar_tac)
  refine WP.spec_mono hb8 ?_
  intro r ⟨hstream8, hc8, hw8⟩
  change stream r = stream w7 ++ lowBits i8.val i10.val at hstream8
  have hrev : lowBits i8.val i10.val = encodeSym tb.lit.lens.val tb.lit.words.val 256 := by
    rw [hi8v, hi10v]
    exact rev_bits _ _ _ 256 hlit.reversed h256' hpos256 hl16
  rw [hrev] at hstream8
  -- assemble
  have hfront6 : stream w6 = stream w ++ lowBits header.val 3 ++
      headerBits tb.lit.lens.val.length tb.dist.lens.val.length tb.hclen.val (tab tb.cl) tb.syms.val tb.extras.val := by
    rw [hstream6]
    simp only [headerBits, tab, List.append_assoc]
  have hhdrlen : (headerBits tb.lit.lens.val.length tb.dist.lens.val.length tb.hclen.val (tab tb.cl)
      tb.syms.val tb.extras.val).length ≤ 14 + 57 + 14 * 316 := by
    simp only [headerBits, List.length_append, lowBits_length, clBits_length]
    omega
  have hbits : stream r = stream w ++ (lowBits header.val 3 ++
      headerBits tb.lit.lens.val.length tb.dist.lens.val.length tb.hclen.val (tab tb.cl) tb.syms.val tb.extras.val ++
      tokbits ++ encodeSym tb.lit.lens.val tb.lit.words.val 256) := by
    rw [hstream8, hstream7, hfront6]
    simp only [List.append_assoc]
  have hencodes : Encodes (tab tb.lit) (tab tb.dist) data.val start.val stop.val
      (tokbits ++ encodeSym tb.lit.lens.val tb.lit.words.val 256) :=
    hemit stop.val _ (Encodes.finish stop.val ⟨h256', hpos256⟩)
  refine ⟨⟨hc8, hw8⟩, _, hbits, ?_, by simp, ?_⟩
  · simp only [List.length_append, lowBits_length, encodeSym_length]
    have := (hlit.table.2 256 h256' hpos256).1
    omega
  intro s tail hss
  have hhbits := header_bits s (stream w)
    ((headerBits tb.lit.lens.val.length tb.dist.lens.val.length tb.hclen.val (tab tb.cl) tb.syms.val tb.extras.val ++
      tokbits ++ encodeSym tb.lit.lens.val tb.lit.words.val 256) ++ tail)
    final 2 (by omega) (by simpa only [hh, List.append_assoc] using hss)
  have hzero : ¬ field_spec s ((stream w).length + 1) 2 0 := by
    intro hz
    have := field_unique s ((stream w).length + 1) 2 0 2 hz hhbits.2
    omega
  have hone : ¬ field_spec s ((stream w).length + 1) 2 1 := by
    intro hz
    have := field_unique s ((stream w).length + 1) 2 1 2 hz hhbits.2
    omega
  have htables := tables_decode s (stream w ++ lowBits header.val 3)
    (tokbits ++ encodeSym tb.lit.lens.val tb.lit.words.val 256 ++ tail) tb.lit.lens.val tb.dist.lens.val
    (tab tb.cl) tb.syms.val tb.extras.val tb.hclen.val hlitlen hdistlen hcl19 hcl.table hcl.kraft
    hlit.kraft hdist.kraft hhclen htb.trailing htb.covers htb.items
    (by simpa only [List.append_assoc] using hss)
  obtain ⟨tokens, hwrites⟩ := Dyn.decode hlit.table hdist.table hencodes s
    (stream w ++ lowBits header.val 3 ++
      headerBits tb.lit.lens.val.length tb.dist.lens.val.length tb.hclen.val (tab tb.cl) tb.syms.val tb.extras.val)
    tail (by simpa only [List.append_assoc] using hss)
  refine ⟨hhbits.1, ?_⟩
  simp only [List.length_append, lowBits_length, Nat.cast_add] at htables hwrites
  have hidx : ((stream w).length : ℤ) + ((3 : ℕ) : ℤ) = ((stream w).length : ℤ) + 1 + 2 := by
    push_cast; ring
  rw [hidx] at htables hwrites
  have hblock := Dyn.block_decode hzero hone hhbits.2 htables hwrites
  convert hblock using 1 <;> (try simp only [List.length_append, lowBits_length]) <;> push_cast <;> ring

theorem fixed_correct (data : Aeneas.Std.Slice U8) (start stop : Usize)
    (w : Gzip.solution.Writer) (ls ds : alloc.vec.Vec U16) (final : Bool)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length)
    (hr : Runs data.val stop.val start.val stop.val ls.val ds.val) (hb : Buffered w)
    (hbudget : (stream w).length + 11 * (stop.val - start.val) + 208 ≤ 34359738360) :
    fixed w data start ls ds final ⦃ r =>
      Buffered r ∧ ∃ bits, stream r = stream w ++ bits ∧
        bits.length ≤ 11 * (stop.val - start.val) + 10 ∧ 3 ≤ bits.length ∧
        Fragment data.val start.val stop.val (stream w) bits final ⦄ := by
  unfold fixed
  have hc := hb.1
  have hw := hb.2
  have hspace : w.out.val.length + 10 ≤ Usize.max := space w 10 (by omega)
  have hheaderSpec : (if final then ok 3#u32 else ok 2#u32) ⦃ h =>
      h.val = (if final then 1 else 0) + 2 ⦄ := by
    split <;> step*
  step as ⟨header, hh⟩
  have hv : header.val < 2 ^ (3#u32).val := by rw [hh]; split <;> scalar_tac
  have he := bits_stream w header 3#u32 hc hw (by scalar_tac) hv (by scalar_tac)
  step as ⟨w1, hemit, hc1, hw1⟩
  have hstream1 : stream w1 = stream w ++ lowBits header.val 3 := by simpa [stream] using hemit
  have hsz1 := congrArg List.length hstream1
  simp only [List.length_append, lowBits_length] at hsz1
  have hlen := runs_lengths hr
  have hi : TokenState data.val start.val stop.val (stream w1) ls.val ds.val w1 start 0#usize := by
    refine ⟨⟨Nat.le_refl _, hs, hd⟩, hlen.1, by scalar_tac, ?_, ⟨hc1, hw1⟩,
      [], by simp, by simp, Tokens.emitted_nil _ _⟩
    simpa using hr
  step as ⟨w2, hb2, bits, hout2, hbitslen, henc⟩
  have hc2 := hb2.1
  have hw2 := hb2.2
  have hsz2 := congrArg List.length hout2
  simp only [List.length_append] at hsz2
  have hspace2 : w2.out.val.length + 8 ≤ Usize.max := space w2 8 (by omega)
  step as ⟨r, hemit3, hc3, hw3⟩
  have hstream3 : stream r = stream w1 ++ (bits ++ Symbols.encode 256) := by
    change stream r = stream w2 ++ Symbols.encode (256#usize).val at hemit3
    simpa only [hout2, List.append_assoc, UScalar.ofNatCore_val_eq] using hemit3
  have hfinish : (Symbols.encode 256).length = 7 := by norm_num [Symbols.encode, Symbols.width]
  refine ⟨⟨hc3, hw3⟩, lowBits header.val 3 ++ (bits ++ Symbols.encode 256),
    by rw [hstream3, hstream1, List.append_assoc], ?_, by simp, ?_⟩
  · simp only [List.length_append, lowBits_length, hfinish]
    omega
  intro s tail hss
  have hhbits := header_bits s (stream w) ((bits ++ Symbols.encode 256) ++ tail) final 1 (by omega)
    (by simpa only [hh, Nat.mul_one, List.append_assoc] using hss)
  obtain ⟨tokens, hwrite⟩ := Encoding.decode henc s (stream w ++ lowBits header.val 3) tail
    (by simpa only [List.append_assoc] using hss)
  have hzero : ¬ field_spec s ((stream w).length + 1) 2 0 := by
    intro hz
    have := field_unique s ((stream w).length + 1) 2 0 1 hz hhbits.2
    omega
  refine ⟨hhbits.1, ?_⟩
  have hdblock := Encoder.fixed_block_decode Huffman.fixed_lengths Symbols.distance_lengths hzero hhbits.2
    (by
      simp only [List.length_append, lowBits_length, Nat.cast_add] at hwrite
      convert hwrite using 1 <;> omega)
  convert hdblock using 1 <;> simp only [List.length_append, lowBits_length, Nat.cast_add] <;> omega

/-- The cheapest of the three block types for a plan whose symbol indices and frequencies are
known (`stored_ok` only when the span fits a stored block). -/
theorem block2_correct (data : Aeneas.Std.Slice U8) (start stop : Usize) (w : Gzip.solution.Writer)
    (plan : Plan) (lsym dsym : alloc.vec.Vec U8) (lfreq dfreq : alloc.vec.Vec Usize) (final : Bool)
    (stored_cost : Usize) (stored_ok : Bool) (smooth : Bool)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length) (hspan : stop.val - start.val ≤ 1048576)
    (hr : Runs data.val stop.val start.val stop.val plan.lengths.val plan.distances.val)
    (hsym : Symbolize.Symbolized plan.lengths.val plan.distances.val lsym.val dsym.val)
    (hlf : lfreq.val.length = 286) (hdf : dfreq.val.length = 30)
    (hsupp : Fused.Support data.val start.val plan.lengths.val plan.distances.val lsym.val dsym.val lfreq.val dfreq.val)
    (hok : stored_ok = true → stop.val - start.val ≤ 32768)
    (hb : Buffered w) (hbudget : (stream w).length + 16 * (stop.val - start.val) + 5000 ≤ 34359738360) :
    block2 w data start stop plan lsym dsym lfreq dfreq final stored_cost stored_ok smooth ⦃ r =>
      Buffered r ∧ ∃ bits, stream r = stream w ++ bits ∧
        bits.length ≤ 16 * (stop.val - start.val) + 5000 ∧ 3 ≤ bits.length ∧
        Fragment data.val start.val stop.val (stream w) bits final ⦄ := by
  have hll := runs_lengths hr
  unfold block2
  have hbt := fit_tables_spec data start plan.lengths plan.distances lsym dsym lfreq dfreq smooth stop.val hr hd
    hsym (by omega) hlf hdf hsupp
  step as ⟨tables, dynamic_cost, fixed_cost, ok1, hok1⟩
  have hfixed := fixed_correct data start stop w plan.lengths plan.distances final hs hd hr hb (by omega)
  have hfixed' : fixed w data start plan.lengths plan.distances final ⦃ r =>
      Buffered r ∧ ∃ bits, stream r = stream w ++ bits ∧
        bits.length ≤ 16 * (stop.val - start.val) + 5000 ∧ 3 ≤ bits.length ∧
        Fragment data.val start.val stop.val (stream w) bits final ⦄ := by
    refine WP.spec_mono hfixed ?_
    intro r ⟨hr', bits, he, hlen, hpos, hf⟩
    exact ⟨hr', bits, he, by omega, hpos, hf⟩
  have hfallback : (if stored_ok then
      (if stored_cost < fixed_cost then stored w data start stop final
        else fixed w data start plan.lengths plan.distances final)
      else fixed w data start plan.lengths plan.distances final) ⦃ r =>
      Buffered r ∧ ∃ bits, stream r = stream w ++ bits ∧
        bits.length ≤ 16 * (stop.val - start.val) + 5000 ∧ 3 ≤ bits.length ∧
        Fragment data.val start.val stop.val (stream w) bits final ⦄ := by
    split
    · rename_i hsp
      have hspan' : stop.val - start.val ≤ 32768 := hok hsp
      have hstored := stored_correct data start stop w final hs hd hspan' hb (by omega)
      split
      · refine WP.spec_mono hstored ?_
        intro r ⟨hr', bits, he, hlen, hpos, hf⟩
        exact ⟨hr', bits, he, by omega, hpos, hf⟩
      · exact hfixed'
    · exact hfixed'
  split
  · rename_i hok1t
    split
    · split
      · exact dynamic_correct data start stop w plan.lengths plan.distances lsym dsym tables final hs hd hspan hr
          hsym (hok1 hok1t) hb hbudget
      · exact hfallback
    · exact hfallback
  · exact hfallback

/-- A block from a parse: stored outright when nearly all literals, else the cheapest type
(with the symbols counted by the parse, or counted here). -/
theorem block1_correct (data : Aeneas.Std.Slice U8) (start stop : Usize) (w : Gzip.solution.Writer)
    (pr : Parsed) (final : Bool) (smooth : Bool)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length) (hspan : stop.val - start.val ≤ 1048576)
    (hpr : Counting.ParsedOk data.val start.val stop.val pr)
    (hb : Buffered w) (hbudget : (stream w).length + 16 * (stop.val - start.val) + 5000 ≤ 34359738360) :
    block1 w data start stop pr final smooth ⦃ r =>
      Buffered r ∧ ∃ bits, stream r = stream w ++ bits ∧
        bits.length ≤ 16 * (stop.val - start.val) + 5000 ∧ 3 ≤ bits.length ∧
        Fragment data.val start.val stop.val (stream w) bits final ⦄ := by
  have hr := hpr.1
  have hc := hb.1
  have hw := hb.2
  have hll := runs_lengths hr
  have hstored' (hsp : stop.val - start.val ≤ 32768) :
      stored w data start stop final ⦃ r =>
        Buffered r ∧ ∃ bits, stream r = stream w ++ bits ∧
          bits.length ≤ 16 * (stop.val - start.val) + 5000 ∧ 3 ≤ bits.length ∧
          Fragment data.val start.val stop.val (stream w) bits final ⦄ := by
    refine WP.spec_mono (stored_correct data start stop w final hs hd hsp hb (by omega)) ?_
    intro r ⟨hr', bits, he, hlen, hpos, hf⟩
    exact ⟨hr', bits, he, by omega, hpos, hf⟩
  have hslow (span : Usize) (hspanv : span.val = stop.val - start.val) :
      (do
      let i ← w.count + 3#u32
      let i1 ← lift (i &&& 7#u32)
      let i2 ← 8#u32 - i1
      let i3 ← lift (i2 &&& 7#u32)
      let i4 ← i3 + 35#u32
      let i5 ← lift (UScalar.cast .Usize i4)
      let i6 ← span * 8#usize
      let stored_cost ← i5 + i6
      if pr.fused
      then
        solution.block2 w data start stop pr.plan pr.lsym pr.dsym pr.lfreq pr.dfreq final stored_cost
          (span <= 32768#usize) smooth
      else
        let (lsym, dsym, lfreq, dfreq) ←
          solution.symbols_histogram data start pr.plan.lengths pr.plan.distances
        solution.block2 w data start stop pr.plan lsym dsym lfreq dfreq final stored_cost
          (span <= 32768#usize) smooth) ⦃ r =>
        Buffered r ∧ ∃ bits, stream r = stream w ++ bits ∧
          bits.length ≤ 16 * (stop.val - start.val) + 5000 ∧ 3 ≤ bits.length ∧
          Fragment data.val start.val stop.val (stream w) bits final ⦄ := by
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    have hi1b : i1.val ≤ 7 := by
      rw [hi1, UScalar.val_and]
      change i.val &&& 7 ≤ 7
      have he : i.val &&& 7 = i.val % 8 := Nat.and_two_pow_sub_one_eq_mod _ 3
      rw [he]; omega
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3⟩
    have hi3b : i3.val ≤ 7 := by
      rw [hi3, UScalar.val_and]
      change i2.val &&& 7 ≤ 7
      have he : i2.val &&& 7 = i2.val % 8 := Nat.and_two_pow_sub_one_eq_mod _ 3
      rw [he]; omega
    step as ⟨i4, hi4⟩
    step as ⟨i5, hi5⟩
    step as ⟨i6, hi6⟩
    step as ⟨stored_cost, hsc⟩
    have hok : decide (span ≤ 32768#usize) = true → stop.val - start.val ≤ 32768 := by
      intro h
      simp only [decide_eq_true_eq] at h
      scalar_tac
    split
    · rename_i hf
      obtain ⟨hsym, hlf, hdf, hsupp⟩ := hpr.2 hf
      exact block2_correct data start stop w pr.plan pr.lsym pr.dsym pr.lfreq pr.dfreq final stored_cost _ smooth
        hs hd hspan hr hsym hlf hdf hsupp hok hb hbudget
    · have hsymb := Fused.correct data start pr.plan.lengths pr.plan.distances stop.val hr hd (by omega)
      step as ⟨lsym, dsym, lfreq, dfreq, hsym, hlf, hdf, hsupp⟩
      exact block2_correct data start stop w pr.plan lsym dsym lfreq dfreq final stored_cost _ smooth
        hs hd hspan hr hsym hlf hdf hsupp hok hb hbudget
  unfold block1
  step as ⟨span, hspanv⟩
  split
  · rename_i hsp
    split
    · step as ⟨part, hpart⟩
      have hpartb : part.val ≤ span.val := by
        rw [hpart]
        exact Nat.div_le_self _ _
      step as ⟨threshold, hthreshold⟩
      split
      · exact hstored' (by scalar_tac)
      · exact hslow span hspanv
    · exact hslow span hspanv
  · exact hslow span hspanv

end Gzip.Proofs.DynBlock
