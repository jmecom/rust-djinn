import Gzip.Proofs.Huff
import Gzip.Proofs.Codes
import Gzip.Proofs.Tables

open Aeneas Std Result
open Gzip.solution Gzip.Proofs.Huffman Gzip.Proofs.Codes Gzip.Proofs.Writer

set_option maxHeartbeats 2000000

namespace Gzip.Proofs.Canon

theorem shift_ok (s : Usize) (h : s.val ≤ 16) : s.val < System.Platform.numBits := by
  rcases System.Platform.numBits_eq with h' | h' <;> rw [h'] <;> omega

theorem shift_val (s : Usize) (h : s.val ≤ 16) : (1 <<< s.val) % Usize.size = 2 ^ s.val := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  apply Nat.mod_eq_of_lt
  have h1 : 2 ^ s.val ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) h
  have h2 : 2 ^ 16 < Usize.size := by scalar_tac
  omega

theorem earlier_le (lens : List U8) (n k : ℕ) : earlier lens n k ≤ k := by
  induction k with
  | zero => simp [earlier]
  | succ k ih => simp only [earlier]; split <;> omega

theorem shorter_bound (lens : List U8) (l k : ℕ) : shorter lens l k ≤ k * 2 ^ l := by
  induction k with
  | zero => simp [shorter]
  | succ k ih =>
      simp only [shorter]
      split
      · have hp : 2 ^ (l - (lens[k]!).val) ≤ 2 ^ l :=
          Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
        calc
          shorter lens l k + 2 ^ (l - (lens[k]!).val) ≤ k * 2 ^ l + 2 ^ l := Nat.add_le_add ih hp
          _ = (k + 1) * 2 ^ l := by ring
      · simp only [Nat.add_zero]
        calc
          shorter lens l k ≤ k * 2 ^ l := ih
          _ ≤ (k + 1) * 2 ^ l := Nat.mul_le_mul_right _ (by omega)

theorem shorter_zero (lens : List U8) (k : ℕ) : shorter lens 0 k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [shorter, ih]; split <;> omega

theorem shorter_one (lens : List U8) (k : ℕ) : shorter lens 1 k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [shorter, ih]; split <;> omega

theorem shorter_succ (lens : List U8) (l k : ℕ) (hl : 1 ≤ l) :
    shorter lens (l + 1) k = 2 * (shorter lens l k + earlier lens l k) := by
  induction k with
  | zero => simp [shorter, earlier]
  | succ k ih =>
      simp only [shorter, earlier, ih]
      by_cases hpos : 1 ≤ (lens[k]!).val
      · by_cases hlt : (lens[k]!).val < l
        · have hlt' : (lens[k]!).val < l + 1 := by omega
          have hne : (lens[k]!).val ≠ l := by omega
          simp only [hpos, hlt, hlt', hne, and_self, ite_true, ite_false, Nat.add_zero]
          have he : l + 1 - (lens[k]!).val = l - (lens[k]!).val + 1 := by omega
          rw [he, Nat.pow_succ]
          omega
        · by_cases he : (lens[k]!).val = l
          · simp only [he, if_pos (by omega : 1 ≤ l ∧ l < l + 1), if_neg (by omega : ¬(1 ≤ l ∧ l < l)), ite_true]
            have hd : l + 1 - l = 1 := by omega
            rw [hd]
            omega
          · have hlt' : ¬(lens[k]!).val < l + 1 := by omega
            simp only [if_neg (by omega : ¬(1 ≤ (lens[k]!).val ∧ (lens[k]!).val < l)),
              if_neg (by omega : ¬(1 ≤ (lens[k]!).val ∧ (lens[k]!).val < l + 1)), if_neg he]
            omega
      · have hne : (lens[k]!).val ≠ l := by omega
        simp only [if_neg (by omega : ¬(1 ≤ (lens[k]!).val ∧ (lens[k]!).val < l)),
          if_neg (by omega : ¬(1 ≤ (lens[k]!).val ∧ (lens[k]!).val < l + 1)), if_neg hne]
        omega

theorem shorter_small (lens : List U8) (l k : ℕ) (hl : l ≤ 16) (hk : k ≤ 1024) :
    shorter lens l k ≤ 67108864 := by
  have hp : 2 ^ l ≤ 65536 := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hl
    simpa using this
  calc
    shorter lens l k ≤ k * 2 ^ l := shorter_bound lens l k
    _ ≤ 1024 * 65536 := Nat.mul_le_mul hk hp
    _ = 67108864 := by decide

/-! ### Count lengths once, then build the first codewords by recurrence. -/

def Hist (lens : List U8) (limit k : ℕ) (count : List Usize) : Prop :=
  count.length = limit + 2 ∧ (count[0]!).val = 0 ∧
  ∀ x, 1 ≤ x → x ≤ limit → (count[x]!).val = earlier lens x k

theorem hist_update (lens : List U8) (limit k x : ℕ) (count : List Usize) (value : Usize)
    (h : Hist lens limit k count) (hx : x = (lens[k]!).val)
    (hx1 : 1 ≤ x) (hx2 : x ≤ limit) (hv : value.val = (count[x]!).val + 1) :
    Hist lens limit (k + 1) (count.set x value) := by
  obtain ⟨hc, hz, hvals⟩ := h
  refine ⟨by simpa using hc, ?_, ?_⟩
  · rw [Djinn.Vocab.getElem!_set count x 0 value (by omega), if_neg (by omega)]
    exact hz
  · intro m hm1 hm2
    rw [Djinn.Vocab.getElem!_set count x m value (by omega)]
    simp only [earlier]
    by_cases he : m = x
    · subst m
      rw [if_pos rfl]
      rw [hv, hvals x hx1 hx2]
      rw [← hx]
      simp
    · have hxne : x ≠ m := Ne.symm he
      simp only [if_neg he]
      rw [hvals m hm1 hm2, ← hx, if_neg hxne, Nat.add_zero]

theorem hist_unchanged (lens : List U8) (limit k x : ℕ) (count : List Usize)
    (h : Hist lens limit k count) (hx : x = (lens[k]!).val)
    (hn : ¬ (1 ≤ x ∧ x ≤ limit)) :
    Hist lens limit (k + 1) count := by
  obtain ⟨hc, hz, hvals⟩ := h
  refine ⟨hc, hz, ?_⟩
  intro m hm1 hm2
  have hne : x ≠ m := by omega
  rw [hvals m hm1 hm2]
  simp only [earlier, ← hx, if_neg hne, Nat.add_zero]

theorem counts_body (lens : alloc.vec.Vec U8) (limit : Usize) (count : alloc.vec.Vec Usize)
    (ok1 : Bool) (k : Usize) (hsmall : lens.val.length ≤ 1024) (hlimit : limit.val ≤ 15)
    (hk : k.val ≤ lens.val.length) (hh : Hist lens.val limit.val k.val count.val)
    (hok : ok1 = true → ∀ j < k.val, (lens.val[j]!).val ≤ limit.val) :
    canonical_counts_loop.body lens limit count ok1 k ⦃ r =>
      match r with
      | .done (c, ok2) => Hist lens.val limit.val lens.val.length c.val ∧
          (ok2 = true → ∀ j < lens.val.length, (lens.val[j]!).val ≤ limit.val)
      | .cont (c, ok2, k2) => k2.val = k.val + 1 ∧ k2.val ≤ lens.val.length ∧
          Hist lens.val limit.val k2.val c.val ∧
          (ok2 = true → ∀ j < k2.val, (lens.val[j]!).val ≤ limit.val) ⦄ := by
  unfold canonical_counts_loop.body
  dsimp only
  split
  · have hkl : k.val < lens.val.length := by scalar_tac
    step as ⟨i, hi⟩
    step as ⟨x, hx⟩
    have hxv : x.val = (lens.val[k.val]!).val := by
      rw [hx, UScalar.cast_val_eq, hi, getElem!_pos lens.val k.val hkl]
      exact Nat.mod_eq_of_lt (by scalar_tac)
    have hselect : (if 1#usize <= x then if x <= limit then do
          let (old, back) ← alloc.vec.Vec.index_mut_usize count x
          let value ← old + 1#usize
          ok (back value)
        else ok count else ok count) ⦃ c => Hist lens.val limit.val (k.val + 1) c.val ⦄ := by
      split
      · split
        · have hx1 : 1 ≤ x.val := by scalar_tac
          have hx2 : x.val ≤ limit.val := by scalar_tac
          have hxb : x.val < count.val.length := by rw [hh.1]; omega
          step as ⟨old, back, hold, hback⟩
          have holdv : old.val = earlier lens.val x.val k.val := by
            rw [hold, ← getElem!_pos count.val x.val hxb]
            exact hh.2.2 x.val hx1 hx2
          have hbound := earlier_le lens.val x.val k.val
          step as ⟨value, hvalue⟩
          simp only [hback, WP.spec_ok, alloc.vec.Vec.set_val_eq]
          apply hist_update lens.val limit.val k.val x.val count.val value hh hxv hx1 hx2
          rw [hvalue, hold, ← getElem!_pos count.val x.val hxb]
        · simp only [WP.spec_ok]
          exact hist_unchanged lens.val limit.val k.val x.val count.val hh hxv (by scalar_tac)
      · simp only [WP.spec_ok]
        exact hist_unchanged lens.val limit.val k.val x.val count.val hh hxv (by scalar_tac)
    step as ⟨count1, hcount1⟩
    have hok2Spec : (if x > limit then ok false else ok ok1) ⦃ ok2 =>
        ok2 = true → ok1 = true ∧ x.val ≤ limit.val ⦄ := by
      split
      · simp
      · have hxle : x.val ≤ limit.val := by scalar_tac
        simp only [WP.spec_ok]
        exact fun h => ⟨h, hxle⟩
    step as ⟨ok2, hok2⟩
    step as ⟨k2, hk2⟩
    try simp only [WP.spec_ok]
    refine ⟨hk2, by scalar_tac, by rw [hk2]; exact hcount1, ?_⟩
    intro h2 j hj
    obtain ⟨h1, hxle⟩ := hok2 h2
    rw [hk2] at hj
    by_cases hjk : j < k.val
    · exact hok h1 j hjk
    · have he : j = k.val := by omega
      rw [he, ← hxv]
      exact hxle
  · have he : k.val = lens.val.length := by scalar_tac
    simp only [WP.spec_ok]
    rw [← he]
    exact ⟨hh, hok⟩

theorem counts_loop (lens : alloc.vec.Vec U8) (limit : Usize) (count : alloc.vec.Vec Usize)
    (ok1 : Bool) (k : Usize) (hsmall : lens.val.length ≤ 1024) (hlimit : limit.val ≤ 15)
    (hk : k.val ≤ lens.val.length) (hh : Hist lens.val limit.val k.val count.val)
    (hok : ok1 = true → ∀ j < k.val, (lens.val[j]!).val ≤ limit.val) :
    canonical_counts_loop lens limit count ok1 k ⦃ r =>
      Hist lens.val limit.val lens.val.length r.1.val ∧
      (r.2 = true → ∀ j < lens.val.length, (lens.val[j]!).val ≤ limit.val) ⦄ := by
  unfold canonical_counts_loop
  apply loop.spec_decr_nat (fun (_, _, k') => lens.val.length - k'.val)
    (fun (c, ok2, k2) => k2.val ≤ lens.val.length ∧ Hist lens.val limit.val k2.val c.val ∧
      (ok2 = true → ∀ j < k2.val, (lens.val[j]!).val ≤ limit.val))
  · rintro ⟨c, ok2, k2⟩ ⟨hk2, hh2, hok2⟩
    refine WP.spec_mono (counts_body lens limit c ok2 k2 hsmall hlimit hk2 hh2 hok2) ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨c', ok', k'⟩ := state
        obtain ⟨he, hk', hh', hok'⟩ := hr
        exact ⟨⟨hk', hh', hok'⟩, by change lens.val.length - k'.val < lens.val.length - k2.val; omega⟩
  · exact ⟨hk, hh, hok⟩

theorem counts_spec (lens : alloc.vec.Vec U8) (limit : Usize)
    (hsmall : lens.val.length ≤ 1024) (hlimit : limit.val ≤ 15) :
    canonical_counts lens limit ⦃ r =>
      Hist lens.val limit.val lens.val.length r.1.val ∧
      (r.2 = true → ∀ j < lens.val.length, (lens.val[j]!).val ≤ limit.val) ⦄ := by
  unfold canonical_counts
  step as ⟨n, hn⟩
  step as ⟨count, hcount⟩
  have hh : Hist lens.val limit.val 0 count.val := by
    rw [hcount]
    refine ⟨by simp [hn], ?_, ?_⟩
    · simp [hn]
    · intro x hx1 hx2
      simp [hn, earlier, List.getElem?_replicate, show x < limit.val + 2 by omega]
  exact counts_loop lens limit count true 0#usize hsmall hlimit (by simp) hh (by simp)

structure FirstState (lens : List U8) (limit n : ℕ) (base : alloc.vec.Vec Usize) (l : Usize) : Prop where
  range : 1 ≤ l.val ∧ l.val ≤ limit + 2
  baseLen : base.val.length = limit + 2
  zero : (base.val[0]!).val = 0
  values : ∀ l', 1 ≤ l' → l' < l.val → (base.val[l']!).val = shorter lens l' n

theorem base_body (lens : List U8) (limit n : Usize) (freq base : alloc.vec.Vec Usize) (l : Usize)
    (hsmall : n.val ≤ 1024) (hlimit : limit.val ≤ 15)
    (hh : Hist lens limit.val n.val freq.val)
    (h : FirstState lens limit.val n.val base l) :
    canonical_loop0.body limit freq base l ⦃ r =>
      match r with
      | .done base' => FirstState lens limit.val n.val base' l ∧ l.val = limit.val + 2
      | .cont (base', l') => FirstState lens limit.val n.val base' l' ∧ l'.val = l.val + 1 ⦄ := by
  obtain ⟨hr, hbl, hz, hv⟩ := h
  unfold canonical_loop0.body
  step as ⟨i, hi⟩
  split
  · have hle : l.val ≤ limit.val + 1 := by scalar_tac
    step as ⟨previous, hp⟩
    have hpb : previous.val < base.val.length := by rw [hbl]; omega
    have hpf : previous.val < freq.val.length := by rw [hh.1]; omega
    step as ⟨prev, hprev⟩
    step as ⟨freqval, hfreq⟩
    have hprevv : prev.val = shorter lens previous.val n.val := by
      rw [hprev, ← getElem!_pos base.val previous.val hpb]
      by_cases he : previous.val = 0
      · rw [he, hz, shorter_zero]
      · exact hv previous.val (by omega) (by omega)
    have hfreqb : freqval.val ≤ n.val := by
      rw [hfreq, ← getElem!_pos freq.val previous.val hpf]
      by_cases he : previous.val = 0
      · rw [he, hh.2.1]; omega
      · rw [hh.2.2 previous.val (by omega) (by omega)]
        exact earlier_le lens previous.val n.val
    have hprevb : prev.val ≤ 67108864 := by
      rw [hprevv]
      exact shorter_small lens previous.val n.val (by omega) hsmall
    step as ⟨sum, hsum⟩
    step as ⟨c, hc⟩
    have hcv : c.val = shorter lens l.val n.val := by
      rw [hc, hsum, hprevv, hfreq, ← getElem!_pos freq.val previous.val hpf]
      by_cases he : previous.val = 0
      · have hl1 : l.val = 1 := by omega
        rw [he, hh.2.1, shorter_zero, hl1, shorter_one]
      · rw [hh.2.2 previous.val (by omega) (by omega), ← shorter_succ lens previous.val n.val (by omega)]
        congr 2
        omega
    have hlb : l.val < base.val.length := by rw [hbl]; omega
    step as ⟨old, back, hold, hback⟩
    step as ⟨l1, hl1⟩
    simp only [hback, WP.spec_ok, alloc.vec.Vec.set_val_eq]
    refine ⟨⟨⟨by omega, by omega⟩, by simpa using hbl, ?_, ?_⟩, hl1⟩
    · simp only [alloc.vec.Vec.set_val_eq]
      rw [Djinn.Vocab.getElem!_set base.val l.val 0 c (by omega), if_neg (by omega)]
      exact hz
    · intro l' hl'1 hl'2
      simp only [alloc.vec.Vec.set_val_eq]
      rw [Djinn.Vocab.getElem!_set base.val l.val l' c (by omega)]
      split
      · rename_i he
        rw [he]
        exact hcv
      · exact hv l' hl'1 (by omega)
  · have he : l.val = limit.val + 2 := by scalar_tac
    simp only [WP.spec_ok]
    exact ⟨⟨hr, hbl, hz, hv⟩, he⟩

theorem base_loop (lens : List U8) (limit n : Usize) (freq base : alloc.vec.Vec Usize) (l : Usize)
    (hsmall : n.val ≤ 1024) (hlimit : limit.val ≤ 15)
    (hh : Hist lens limit.val n.val freq.val)
    (h : FirstState lens limit.val n.val base l) :
    canonical_loop0 limit freq base l ⦃ r =>
      r.val.length = limit.val + 2 ∧
      (∀ l', 1 ≤ l' → l' ≤ limit.val + 1 →
        (r.val[l']!).val = min (shorter lens l' n.val) 1073741824) ⦄ := by
  unfold canonical_loop0
  apply loop.spec_decr_nat (fun (_, l') => limit.val + 2 - l'.val)
    (fun (base', l') => FirstState lens limit.val n.val base' l')
  · rintro ⟨base', l'⟩ h'
    refine WP.spec_mono (base_body lens limit n freq base' l' hsmall hlimit hh h') ?_
    intro r hr
    cases r with
    | done state =>
        obtain ⟨hs, he⟩ := hr
        refine ⟨hs.baseLen, ?_⟩
        intro l'' h1 h2
        rw [hs.values l'' h1 (by omega), Nat.min_eq_left]
        exact (shorter_small lens l'' n.val (by omega) hsmall).trans (by decide)
    | cont state =>
        obtain ⟨base'', l''⟩ := state
        obtain ⟨hs, he⟩ := hr
        exact ⟨hs, by change limit.val + 2 - l''.val < limit.val + 2 - l'.val; have := hs.range; omega⟩
  · exact h

/-! ### The codewords: first codeword of the length plus the symbols before of the same length -/

structure WordState (lens : List U8) (limit n : ℕ) (base : List Usize) (okin ok : Bool)
    (count words : alloc.vec.Vec Usize) (sym : Usize) : Prop where
  index : sym.val ≤ n
  countLen : count.val.length = limit + 2
  wordsLen : words.val.length = n
  counts : ∀ x, 1 ≤ x → x ≤ limit → (count.val[x]!).val = earlier lens x sym.val
  values : ∀ s < sym.val, 1 ≤ (lens[s]!).val → (lens[s]!).val ≤ limit →
    (words.val[s]!).val = (base[(lens[s]!).val]!).val + earlier lens (lens[s]!).val s
  okay : ok = true → okin = true ∧ ∀ s < sym.val, 1 ≤ (lens[s]!).val → (lens[s]!).val ≤ limit →
    (words.val[s]!).val < 2 ^ (lens[s]!).val

theorem word_body (lens : alloc.vec.Vec U8) (limit n : Usize) (base : alloc.vec.Vec Usize) (ok1 : Bool)
    (count words : alloc.vec.Vec Usize) (sym : Usize) (okin : Bool)
    (hn : n.val = lens.val.length) (hsmall : n.val ≤ 1024) (hlimit : limit.val ≤ 15)
    (hbl : base.val.length = limit.val + 2)
    (hbb : ∀ l', 1 ≤ l' → l' ≤ limit.val + 1 → (base.val[l']!).val ≤ 1073741824)
    (h : WordState lens.val limit.val n.val base.val okin ok1 count words sym) :
    canonical_loop1.body lens limit n base ok1 count words sym ⦃ r =>
      match r with
      | .done (words', ok') => WordState lens.val limit.val n.val base.val okin ok' count words' sym ∧ sym.val = n.val
      | .cont (ok', count', words', sym') =>
          WordState lens.val limit.val n.val base.val okin ok' count' words' sym' ∧ sym'.val = sym.val + 1 ⦄ := by
  obtain ⟨hidx, hcl, hwl, hcounts, hvalues, hokay⟩ := h
  unfold canonical_loop1.body
  split
  · rename_i hlt
    have hlt' : sym.val < lens.val.length := by scalar_tac
    step as ⟨i, hi⟩
    step as ⟨x, hx⟩
    have hxv : x.val = (lens.val[sym.val]!).val := by
      rw [hx, UScalar.cast_val_eq, hi, getElem!_pos lens.val sym.val hlt']
      exact Nat.mod_eq_of_lt (by scalar_tac)
    have hestep : ∀ m, earlier lens.val m (sym.val + 1) = earlier lens.val m sym.val +
        if (lens.val[sym.val]!).val = m then 1 else 0 := by
      intro m
      simp only [earlier]
    have hSpec : (if 1#usize <= x then if x <= limit then do
          let i1 ← alloc.vec.Vec.index_usize base x
          let i2 ← alloc.vec.Vec.index_usize count x
          let w ← i1 + i2
          let (_, index_mut_back) ← alloc.vec.Vec.index_mut_usize words sym
          let e ← i2 + 1#usize
          let (_, index_mut_back1) ← alloc.vec.Vec.index_mut_usize count x
          let i3 ← 1#usize <<< x
          if w >= i3 then
            let count2 := index_mut_back1 e
            let words2 := index_mut_back w
            ok (false, count2, words2)
          else
            let count2 := index_mut_back1 e
            let words2 := index_mut_back w
            ok (ok1, count2, words2)
        else ok (ok1, count, words) else ok (ok1, count, words)) ⦃ r =>
        r.2.1.val.length = limit.val + 2 ∧ r.2.2.val.length = n.val ∧
        (∀ m, 1 ≤ m → m ≤ limit.val → (r.2.1.val[m]!).val = earlier lens.val m (sym.val + 1)) ∧
        (∀ s < sym.val + 1, 1 ≤ (lens.val[s]!).val → (lens.val[s]!).val ≤ limit.val →
          (r.2.2.val[s]!).val = (base.val[(lens.val[s]!).val]!).val + earlier lens.val (lens.val[s]!).val s) ∧
        (r.1 = true → okin = true ∧ ∀ s < sym.val + 1, 1 ≤ (lens.val[s]!).val → (lens.val[s]!).val ≤ limit.val →
          (r.2.2.val[s]!).val < 2 ^ (lens.val[s]!).val) ⦄ := by
      split
      · rename_i hx1
        split
        · rename_i hxle
          have hx1' : 1 ≤ x.val := by scalar_tac
          have hxle' : x.val ≤ limit.val := by scalar_tac
          have hxb : x.val < base.val.length := by rw [hbl]; omega
          step as ⟨i1, hi1⟩
          have hxc : x.val < count.val.length := by rw [hcl]; omega
          step as ⟨i2, hi2⟩
          have hi1v : i1.val = (base.val[x.val]!).val := by rw [hi1, getElem!_pos base.val x.val hxb]
          have hi2v : i2.val = (count.val[x.val]!).val := by rw [hi2, getElem!_pos count.val x.val hxc]
          have hi1b : i1.val ≤ 1073741824 := by rw [hi1v]; exact hbb x.val hx1' (by omega)
          have hi2b : i2.val ≤ sym.val := by rw [hi2v, hcounts x.val hx1' hxle']; exact earlier_le _ _ _
          step as ⟨w, hw⟩
          have hsw : sym.val < words.val.length := by rw [hwl]; scalar_tac
          step as ⟨x1, back, hxx1, hback⟩
          step as ⟨e, he⟩
          step as ⟨x2, back1, hx2, hback1⟩
          have hxs : x.val ≤ 16 := by omega
          step as ⟨i3, hi3⟩
          case hy => exact shift_ok x hxs
          have hi3v : i3.val = 2 ^ x.val := by rw [hi3, shift_val x hxs]
          have hcounts' : ∀ m, 1 ≤ m → m ≤ limit.val →
              ((count.val.set x.val e)[m]!).val = earlier lens.val m (sym.val + 1) := by
            intro m hm1 hm2
            rw [Djinn.Vocab.getElem!_set count.val x.val m e (by rw [hcl]; omega), hestep m]
            split
            · rename_i hmx
              rw [he, hi2v, hcounts x.val hx1' hxle', hmx, ← hxv, if_pos rfl]
            · rename_i hmx
              rw [hcounts m hm1 hm2, if_neg (by rw [← hxv]; exact Ne.symm hmx), Nat.add_zero]
          have hvalues' : ∀ s < sym.val + 1, 1 ≤ (lens.val[s]!).val → (lens.val[s]!).val ≤ limit.val →
              ((words.val.set sym.val w)[s]!).val =
                (base.val[(lens.val[s]!).val]!).val + earlier lens.val (lens.val[s]!).val s := by
            intro s hs hs1 hs2
            rw [Djinn.Vocab.getElem!_set words.val sym.val s w (by rw [hwl]; omega)]
            split
            · rename_i hss
              rw [hss, hw, hi1v, hi2v, hcounts x.val hx1' hxle', hxv]
            · exact hvalues s (by omega) hs1 hs2
          split
          · rename_i hge
            simp only [hback, hback1, alloc.vec.Vec.set_val_eq, WP.spec_ok]
            refine ⟨by simp only [List.length_set]; exact hcl, by simp only [List.length_set]; exact hwl,
              hcounts', hvalues', fun h => by simp at h⟩
          · rename_i hge
            have hlt3 : w.val < 2 ^ x.val := by rw [← hi3v]; scalar_tac
            simp only [hback, hback1, alloc.vec.Vec.set_val_eq, WP.spec_ok]
            refine ⟨by simp only [List.length_set]; exact hcl, by simp only [List.length_set]; exact hwl,
              hcounts', hvalues', ?_⟩
            intro hok
            obtain ⟨hin, hprev⟩ := hokay hok
            refine ⟨hin, ?_⟩
            intro s hs hs1 hs2
            rw [Djinn.Vocab.getElem!_set words.val sym.val s w (by rw [hwl]; omega)]
            split
            · rename_i hss
              rw [hss, ← hxv]
              exact hlt3
            · exact hprev s (by omega) hs1 hs2
        · rename_i hxgt
          have hxgt' : limit.val < x.val := by scalar_tac
          try simp only [WP.spec_ok]
          refine ⟨hcl, hwl, ?_, ?_, ?_⟩
          · intro m hm1 hm2
            rw [hcounts m hm1 hm2, hestep m, if_neg (by rw [← hxv]; omega), Nat.add_zero]
          · intro s hs hs1 hs2
            have hs' : s < sym.val := by
              by_contra hc
              have : s = sym.val := by omega
              rw [this, ← hxv] at hs2
              omega
            exact hvalues s hs' hs1 hs2
          · intro hok
            obtain ⟨hin, hprev⟩ := hokay hok
            refine ⟨hin, ?_⟩
            intro s hs hs1 hs2
            have hs' : s < sym.val := by
              by_contra hc
              have : s = sym.val := by omega
              rw [this, ← hxv] at hs2
              omega
            exact hprev s hs' hs1 hs2
      · rename_i hx0
        have hx0' : x.val = 0 := by scalar_tac
        try simp only [WP.spec_ok]
        refine ⟨hcl, hwl, ?_, ?_, ?_⟩
        · intro m hm1 hm2
          rw [hcounts m hm1 hm2, hestep m, if_neg (by rw [← hxv]; omega), Nat.add_zero]
        · intro s hs hs1 hs2
          have hs' : s < sym.val := by
            by_contra hc
            have : s = sym.val := by omega
            rw [this, ← hxv] at hs1
            omega
          exact hvalues s hs' hs1 hs2
        · intro hok
          obtain ⟨hin, hprev⟩ := hokay hok
          refine ⟨hin, ?_⟩
          intro s hs hs1 hs2
          have hs' : s < sym.val := by
            by_contra hc
            have : s = sym.val := by omega
            rw [this, ← hxv] at hs1
            omega
          exact hprev s hs' hs1 hs2
    step as ⟨ok2, count1, words1, hcl1, hwl1, hcounts1, hvalues1, hokay1⟩
    step as ⟨sym1, hsym1⟩
    try simp only [WP.spec_ok]
    refine ⟨⟨by scalar_tac, hcl1, hwl1, ?_, ?_, ?_⟩, hsym1⟩
    · rw [hsym1]; exact hcounts1
    · rw [hsym1]; exact hvalues1
    · rw [hsym1]; exact hokay1
  · rename_i hge
    have he : sym.val = n.val := by scalar_tac
    try simp only [WP.spec_ok]
    exact ⟨⟨hidx, hcl, hwl, hcounts, hvalues, hokay⟩, he⟩

@[step]
theorem word_loop (lens : alloc.vec.Vec U8) (limit n : Usize) (base : alloc.vec.Vec Usize) (ok1 : Bool)
    (count words : alloc.vec.Vec Usize) (sym : Usize) (okin : Bool)
    (hn : n.val = lens.val.length) (hsmall : n.val ≤ 1024) (hlimit : limit.val ≤ 15)
    (hbl : base.val.length = limit.val + 2)
    (hbb : ∀ l', 1 ≤ l' → l' ≤ limit.val + 1 → (base.val[l']!).val ≤ 1073741824)
    (h : WordState lens.val limit.val n.val base.val okin ok1 count words sym) :
    canonical_loop1 lens limit n ok1 base count words sym ⦃ r =>
        r.1.val.length = n.val ∧
        (∀ s < n.val, 1 ≤ (lens.val[s]!).val → (lens.val[s]!).val ≤ limit.val →
          (r.1.val[s]!).val = (base.val[(lens.val[s]!).val]!).val + earlier lens.val (lens.val[s]!).val s) ∧
        (r.2 = true → okin = true ∧ ∀ s < n.val, 1 ≤ (lens.val[s]!).val → (lens.val[s]!).val ≤ limit.val →
          (r.1.val[s]!).val < 2 ^ (lens.val[s]!).val) ⦄ := by
  unfold canonical_loop1
  apply loop.spec_decr_nat (fun (_, _, _, s) => n.val - s.val)
    (fun (ok', count', words', s) => WordState lens.val limit.val n.val base.val okin ok' count' words' s)
  · rintro ⟨ok', count', words', s⟩ h'
    refine WP.spec_mono (word_body lens limit n base ok' count' words' s okin hn hsmall hlimit hbl hbb h') ?_
    intro r hr
    cases r with
    | done state =>
        obtain ⟨words'', ok''⟩ := state
        obtain ⟨hs, he⟩ := hr
        refine ⟨hs.wordsLen, ?_, ?_⟩
        · intro s' hs' h1 h2
          exact hs.values s' (by omega) h1 h2
        · intro hok
          obtain ⟨hin, hv⟩ := hs.okay hok
          exact ⟨hin, fun s' hs' h1 h2 => hv s' (by omega) h1 h2⟩
    | cont state =>
        obtain ⟨ok'', count'', words'', s'⟩ := state
        obtain ⟨hs, he⟩ := hr
        exact ⟨hs, by change n.val - s'.val < n.val - s.val; have := hs.index; omega⟩
  · exact h

theorem canonical_spec (lens : alloc.vec.Vec U8) (limit : Usize) (hsmall : lens.val.length ≤ 1024)
    (hlimit : limit.val ≤ 15) :
    canonical lens limit ⦃ r => r.1.val.length = lens.val.length ∧
      (r.2 = true → TableOk lens.val r.1.val limit.val ∧ Kraft lens.val limit.val) ⦄ := by
  unfold solution.canonical
  dsimp only
  have hlen : (alloc.vec.Vec.len lens).val = lens.val.length := by
    simp [alloc.vec.Vec.len_val, alloc.vec.Vec.length]
  have hcs := counts_spec lens limit hsmall hlimit
  step as ⟨freq, ok1, hhist, hbok⟩
  step as ⟨i, hi⟩
  step as ⟨base, hbase⟩
  have hbl : base.val.length = limit.val + 2 := by rw [hbase, List.length_replicate, hi]
  have hfirst : FirstState lens.val limit.val (alloc.vec.Vec.len lens).val base 1#usize := by
    refine ⟨by simp, hbl, ?_, fun l' h1 h2 => by simp at h1 h2; omega⟩
    simp [hbase, hi]
  have hb := base_loop lens.val limit (alloc.vec.Vec.len lens) freq base 1#usize
    (by rw [hlen]; exact hsmall) hlimit (by rw [hlen]; exact hhist) hfirst
  step as ⟨base1, hbl1, hbv⟩
  step as ⟨i1, hi1⟩
  have hi1b : i1.val < base1.val.length := by rw [hbl1]; omega
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = min (shorter lens.val (limit.val + 1) (alloc.vec.Vec.len lens).val) 1073741824 := by
    rw [hi2, ← getElem!_pos base1.val i1.val hi1b, hbv i1.val (by omega) (by omega), hi1]
  have hi1s : i1.val ≤ 16 := by omega
  step as ⟨i3, hi3⟩
  case hy => exact shift_ok i1 hi1s
  have hi3v : i3.val = 2 ^ (limit.val + 1) := by rw [hi3, shift_val i1 hi1s, hi1]
  have hokSpec : (if i2 > i3 then ok false else ok ok1) ⦃ ok2 =>
      ok2 = true → ok1 = true ∧ i2.val ≤ i3.val ⦄ := by
    split
    · simp
    · rename_i hle
      have : i2.val ≤ i3.val := by scalar_tac
      simp only [WP.spec_ok]
      exact fun h => ⟨h, this⟩
  step as ⟨ok2, hok2⟩
  step as ⟨i4, hi4⟩
  step as ⟨count, hcount⟩
  step as ⟨words, hwords⟩
  have hcl : count.val.length = limit.val + 2 := by rw [hcount, List.length_replicate, hi4]
  have hwl : words.val.length = (alloc.vec.Vec.len lens).val := by rw [hwords, List.length_replicate]
  have hbb : ∀ l', 1 ≤ l' → l' ≤ limit.val + 1 → (base1.val[l']!).val ≤ 1073741824 := by
    intro l' h1 h2
    rw [hbv l' h1 h2]
    exact Nat.min_le_right _ _
  have hws : WordState lens.val limit.val (alloc.vec.Vec.len lens).val base1.val ok2 ok2 count words 0#usize := by
    refine ⟨by simp, hcl, hwl, ?_, fun s hs => by simp at hs, fun h => ⟨h, fun s hs => by simp at hs⟩⟩
    intro x hx1 hx2
    rw [hcount, List.getElem!_replicate]
    · simp [earlier]
    · rw [hi4]; omega
  have hw := word_loop lens limit (alloc.vec.Vec.len lens) base1 ok2 count words 0#usize ok2 hlen
    (by rw [hlen]; exact hsmall) hlimit hbl1 hbb hws
  refine WP.spec_mono hw ?_
  intro r hr
  obtain ⟨hrl, hrv, hrok⟩ := hr
  refine ⟨by rw [hrl, hlen], ?_⟩
  intro hok
  obtain ⟨hok2', hvals⟩ := hrok hok
  obtain ⟨hok1', hkraft⟩ := hok2 hok2'
  have hbounds : ∀ k < (alloc.vec.Vec.len lens).val, (lens.val[k]!).val ≤ limit.val := by
    rw [hlen]
    exact hbok hok1'
  have hkraft' : shorter lens.val (limit.val + 1) lens.val.length ≤ 2 ^ (limit.val + 1) := by
    rw [hi2v, hi3v, hlen] at hkraft
    have h16 : 2 ^ (limit.val + 1) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  refine ⟨⟨by rw [hrl, hlen], ?_⟩, ⟨fun s hs => hbounds s (by rw [hlen]; exact hs), hkraft'⟩⟩
  intro sym hsym hpos
  have hsym' : sym < (alloc.vec.Vec.len lens).val := by rw [hlen]; exact hsym
  have hle := hbounds sym hsym'
  have hv := hrv sym hsym' hpos hle
  have hlt := hvals sym hsym' hpos hle
  refine ⟨hle, ?_, hlt⟩
  rw [hv] at hlt ⊢
  rw [hbv (lens.val[sym]!).val hpos (by omega)] at hlt ⊢
  have h2 : 2 ^ (lens.val[sym]!).val ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) (by omega)
  have hmin : min (shorter lens.val (lens.val[sym]!).val (alloc.vec.Vec.len lens).val) 1073741824 =
      shorter lens.val (lens.val[sym]!).val (alloc.vec.Vec.len lens).val := by
    apply Nat.min_eq_left
    omega
  rw [hmin, Huffman.canonical, hlen]

/-! ### make_code -/

theorem trim_body (least : Usize) (full : alloc.vec.Vec U8) (n : Usize) (hn : n.val ≤ full.val.length)
    (hstart : least.val ≤ n.val ∨ n.val = full.val.length) :
    make_code_loop0.body least full n ⦃ r =>
      match r with
      | .done n' => n'.val ≤ full.val.length ∧ (least.val ≤ n'.val ∨ n'.val = full.val.length)
      | .cont n' => n'.val < n.val ∧ n'.val ≤ full.val.length ∧ (least.val ≤ n'.val ∨ n'.val = full.val.length) ⦄ := by
  unfold make_code_loop0.body
  split
  · rename_i hgt
    have hgt' : least.val < n.val := by scalar_tac
    step as ⟨i, hi⟩
    have hil : i.val < full.val.length := by omega
    step as ⟨i1, hi1⟩
    split
    · try simp only [WP.spec_ok]
      exact ⟨by omega, by omega, Or.inl (by omega)⟩
    · try simp only [WP.spec_ok]
      exact ⟨hn, hstart⟩
  · try simp only [WP.spec_ok]
    exact ⟨hn, hstart⟩

@[step]
theorem trim_loop (least : Usize) (full : alloc.vec.Vec U8) (n : Usize) (hn : n.val ≤ full.val.length)
    (hstart : least.val ≤ n.val ∨ n.val = full.val.length) :
    make_code_loop0 least full n ⦃ r =>
      r.val ≤ full.val.length ∧ (least.val ≤ r.val ∨ r.val = full.val.length) ⦄ := by
  unfold make_code_loop0
  apply loop.spec_decr_nat (fun n' => n'.val)
    (fun n' => n'.val ≤ full.val.length ∧ (least.val ≤ n'.val ∨ n'.val = full.val.length))
  · intro n' hn'
    refine WP.spec_mono (trim_body least full n' hn'.1 hn'.2) ?_
    intro r hr
    cases r with
    | done k => exact hr
    | cont k => exact ⟨⟨hr.2.1, hr.2.2⟩, hr.1⟩
  · exact ⟨hn, hstart⟩

theorem take_body (full : alloc.vec.Vec U8) (n : Usize) (lens : alloc.vec.Vec U8) (i : Usize)
    (limit : ℕ) (hfb : ∀ k < full.val.length, (full.val[k]!).val ≤ limit)
    (hn : n.val ≤ full.val.length) (hi : i.val ≤ n.val) (hl : lens.val.length = i.val)
    (hlb : ∀ k < lens.val.length, (lens.val[k]!).val ≤ limit) :
    make_code_loop1.body full n lens i ⦃ r =>
      match r with
      | .done lens' => lens'.val.length = n.val ∧ ∀ k < lens'.val.length, (lens'.val[k]!).val ≤ limit
      | .cont (lens', i') => i'.val = i.val + 1 ∧ i'.val ≤ n.val ∧ lens'.val.length = i'.val ∧
          ∀ k < lens'.val.length, (lens'.val[k]!).val ≤ limit ⦄ := by
  unfold make_code_loop1.body
  split
  · rename_i hlt
    dsimp only
    split
    · rename_i hlt2
      have hlt' : i.val < full.val.length := by scalar_tac
      step as ⟨i2, hi2⟩
      have hi2v : i2 = full.val[i.val]! := by rw [hi2, getElem!_pos full.val i.val hlt']
      have hspace : lens.val.length < Usize.max := by scalar_tac
      step as ⟨lens1, hlens1⟩
      step as ⟨i3, hi3⟩
      try simp only [WP.spec_ok]
      refine ⟨hi3, by scalar_tac, by rw [hlens1, List.length_append, List.length_singleton, hl, hi3], ?_⟩
      intro k hk
      rw [hlens1, List.length_append, List.length_singleton] at hk
      rw [hlens1]
      by_cases hkl : k < lens.val.length
      · rw [List.getElem!_append_left lens.val [i2] k hkl]
        exact hlb k hkl
      · have he : k = lens.val.length := by omega
        rw [List.getElem!_append_right lens.val [i2] k (by omega), he, Nat.sub_self,
          List.getElem!_cons_zero, hi2v]
        exact hfb i.val hlt'
    · rename_i hge
      have : full.val.length ≤ i.val := by scalar_tac
      try simp only [WP.spec_ok]
      exact ⟨by omega, hlb⟩
  · rename_i hge
    have : n.val ≤ i.val := by scalar_tac
    try simp only [WP.spec_ok]
    exact ⟨by omega, hlb⟩

@[step]
theorem take_loop (full : alloc.vec.Vec U8) (n : Usize) (lens : alloc.vec.Vec U8) (i : Usize)
    (limit : ℕ) (hfb : ∀ k < full.val.length, (full.val[k]!).val ≤ limit)
    (hn : n.val ≤ full.val.length) (hi : i.val ≤ n.val) (hl : lens.val.length = i.val)
    (hlb : ∀ k < lens.val.length, (lens.val[k]!).val ≤ limit) :
    make_code_loop1 full n lens i ⦃ r => r.val.length = n.val ∧
      ∀ k < r.val.length, (r.val[k]!).val ≤ limit ⦄ := by
  unfold make_code_loop1
  apply loop.spec_decr_nat (fun (_, i') => n.val - i'.val)
    (fun (lens', i') => i'.val ≤ n.val ∧ lens'.val.length = i'.val ∧
      ∀ k < lens'.val.length, (lens'.val[k]!).val ≤ limit)
  · rintro ⟨lens', i'⟩ ⟨hi', hl', hlb'⟩
    refine WP.spec_mono (take_body full n lens' i' limit hfb hn hi' hl' hlb') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨lens'', i''⟩ := state
        exact ⟨⟨hr.2.1, hr.2.2.1, hr.2.2.2⟩, by change n.val - i''.val < n.val - i'.val; omega⟩
  · exact ⟨hi, hl, hlb⟩

def RevPrefix (lens : List U8) (words : List Usize) (rev : List U32) (i : ℕ) : Prop :=
  rev.length = i ∧ ∀ i' < i, 1 ≤ (lens[i']!).val → (lens[i']!).val ≤ 16 → (words[i']!).val < 65536 →
    (rev[i']!).val = reverse16 (words[i']!).val / 2 ^ (16 - (lens[i']!).val)

theorem rev_body (n : Usize) (lens : alloc.vec.Vec U8) (words : alloc.vec.Vec Usize) (i : Usize)
    (rev : alloc.vec.Vec U32) (hl : lens.val.length = n.val) (hw : words.val.length = n.val)
    (hsmall : n.val ≤ 1024) (hi : i.val ≤ n.val) (hr : RevPrefix lens.val words.val rev.val i.val) :
    make_code_loop2.body n lens words i rev ⦃ r =>
      match r with
      | .done rev' => RevPrefix lens.val words.val rev'.val n.val
      | .cont (i', rev') => i'.val = i.val + 1 ∧ i'.val ≤ n.val ∧ RevPrefix lens.val words.val rev'.val i'.val ⦄ := by
  obtain ⟨hrl, hrv⟩ := hr
  unfold make_code_loop2.body
  split
  · rename_i hlt
    dsimp only
    split
    · rename_i hlt2
      have hlt' : i.val < lens.val.length := by rw [hl]; scalar_tac
      have hlw : i.val < words.val.length := by rw [hw]; scalar_tac
      step as ⟨i2, hi2⟩
      step as ⟨x, hx⟩
      have hxv : x.val = (lens.val[i.val]!).val := by
        rw [hx, UScalar.cast_val_eq, hi2, getElem!_pos lens.val i.val hlt']
        exact Nat.mod_eq_of_lt (by scalar_tac)
      step as ⟨w, hwv⟩
      have hwv' : w = words.val[i.val]! := by rw [getElem!_pos words.val i.val hlw]; exact hwv
      have hspace : rev.val.length < Usize.max := by scalar_tac
      have hext : ∀ (v : U32), (v.val = reverse16 w.val / 2 ^ (16 - x.val) ∨ ¬ (x.val ≤ 16 ∧ w.val < 65536)) →
          RevPrefix lens.val words.val (rev.val ++ [v]) (i.val + 1) := by
        intro v hv
        refine ⟨by rw [List.length_append, List.length_singleton, hrl], ?_⟩
        intro i' hi' h1 h2 h3
        by_cases hii : i' < i.val
        · rw [List.getElem!_append_left rev.val [v] i' (by omega)]
          exact hrv i' hii h1 h2 h3
        · have he : i' = i.val := by omega
          rw [he]
          rw [List.getElem!_append_right rev.val [v] i.val (by omega), hrl, Nat.sub_self,
            List.getElem!_cons_zero]
          rcases hv with hv | hv
          · rw [hv, hxv, ← hwv']
          · exfalso
            apply hv
            rw [he] at h2 h3
            rw [hxv, hwv']
            exact ⟨h2, h3⟩
      split
      · rename_i hx16
        split
        · rename_i hw16
          have hx16' : x.val ≤ 16 := by scalar_tac
          have hw16' : w.val < 65536 := by scalar_tac
          step as ⟨i3, hi3⟩
          have hi3v : i3.val = w.val := by
            rw [hi3, UScalar.cast_val_eq]
            exact Nat.mod_eq_of_lt (by scalar_tac)
          have hrc := Tables.reverse_code_spec i3 x hx16'
          step as ⟨i4, hi4⟩
          step as ⟨rev1, hrev1⟩
          step as ⟨i5, hi5⟩
          try simp only [WP.spec_ok]
          refine ⟨hi5, by scalar_tac, ?_⟩
          rw [hrev1, hi5]
          apply hext
          left
          rw [hi4, hi3v]
        · rename_i hw16
          have hw16' : ¬ w.val < 65536 := by scalar_tac
          step as ⟨rev1, hrev1⟩
          step as ⟨i3, hi3⟩
          try simp only [WP.spec_ok]
          refine ⟨hi3, by scalar_tac, ?_⟩
          rw [hrev1, hi3]
          apply hext
          right
          omega
      · rename_i hx16
        have hx16' : ¬ x.val ≤ 16 := by scalar_tac
        step as ⟨rev1, hrev1⟩
        step as ⟨i3, hi3⟩
        try simp only [WP.spec_ok]
        refine ⟨hi3, by scalar_tac, ?_⟩
        rw [hrev1, hi3]
        apply hext
        right
        omega
    · rename_i hge
      have : words.val.length ≤ i.val := by scalar_tac
      have he : i.val = n.val := by omega
      try simp only [WP.spec_ok]
      rw [← he]
      exact ⟨hrl, hrv⟩
  · rename_i hge
    have he : i.val = n.val := by scalar_tac
    try simp only [WP.spec_ok]
    rw [← he]
    exact ⟨hrl, hrv⟩

@[step]
theorem rev_loop (n : Usize) (lens : alloc.vec.Vec U8) (words : alloc.vec.Vec Usize) (i : Usize)
    (rev : alloc.vec.Vec U32) (hl : lens.val.length = n.val) (hw : words.val.length = n.val)
    (hsmall : n.val ≤ 1024) (hi : i.val ≤ n.val) (hr : RevPrefix lens.val words.val rev.val i.val) :
    make_code_loop2 n lens i words rev ⦃ r => RevPrefix lens.val words.val r.val n.val ⦄ := by
  unfold make_code_loop2
  apply loop.spec_decr_nat (fun (i', _) => n.val - i'.val)
    (fun (i', rev') => i'.val ≤ n.val ∧ RevPrefix lens.val words.val rev'.val i'.val)
  · rintro ⟨i', rev'⟩ ⟨hi', hr'⟩
    refine WP.spec_mono (rev_body n lens words i' rev' hl hw hsmall hi' hr') ?_
    intro r hr
    cases r with
    | done state => exact hr
    | cont state =>
        obtain ⟨i'', rev''⟩ := state
        exact ⟨⟨hr.2.1, hr.2.2⟩, by change n.val - i''.val < n.val - i'.val; omega⟩
  · exact ⟨hi, hr⟩

/-- Everything `make_code` guarantees when it reports success. -/
structure CodeOk (c : Code) (limit : ℕ) : Prop where
  words : c.words.val.length = c.lens.val.length
  rev : c.rev.val.length = c.lens.val.length
  table : TableOk c.lens.val c.words.val limit
  kraft : Kraft c.lens.val limit
  reversed : RevOk c.lens.val c.words.val c.rev.val

theorem make_code_spec (freq : alloc.vec.Vec Usize) (limit least : Usize)
    (hsmall : freq.val.length ≤ 1024) (hlimit : limit.val ≤ 15) :
    make_code freq limit least ⦃ r =>
      r.1.lens.val.length ≤ freq.val.length ∧
      (least.val ≤ freq.val.length → least.val ≤ r.1.lens.val.length) ∧
      r.1.words.val.length = r.1.lens.val.length ∧ r.1.rev.val.length = r.1.lens.val.length ∧
      (∀ k < r.1.lens.val.length, (r.1.lens.val[k]!).val ≤ limit.val) ∧
      (r.2 = true → CodeOk r.1 limit.val) ⦄ := by
  unfold make_code
  dsimp only
  have hcl := Huff.code_lengths_spec freq limit hsmall hlimit
  step as ⟨full, hfull, hfb⟩
  have hflen : (alloc.vec.Vec.len full).val = full.val.length := by
    simp [alloc.vec.Vec.len_val, alloc.vec.Vec.length]
  have ht := trim_loop least full (alloc.vec.Vec.len full) (by rw [hflen]) (Or.inr hflen)
  step as ⟨n1, hn1, hn1'⟩
  have htk := take_loop full n1 (alloc.vec.Vec.with_capacity U8 n1) 0#usize limit.val hfb hn1 (by simp)
    (by simp [alloc.vec.Vec.with_capacity]) (by simp [alloc.vec.Vec.with_capacity])
  step with htk as ⟨lens, hlens, hlb⟩
  have hc := canonical_spec lens limit (by rw [hlens]; omega) hlimit
  step as ⟨words, ok1, hwl, hok⟩
  have hrv := rev_loop n1 lens words 0#usize (alloc.vec.Vec.with_capacity U32 n1) hlens (by rw [hwl, hlens]) (by omega)
    (by simp) ⟨by simp [alloc.vec.Vec.with_capacity], fun i' hi' => by simp [alloc.vec.Vec.with_capacity] at hi'⟩
  step with hrv as ⟨rev, hrev⟩
  obtain ⟨hrl, hrvals⟩ := hrev
  try simp only [WP.spec_ok]
  try dsimp only
  refine ⟨by rw [hlens]; omega, ?_, by rw [hwl], by rw [hrl, hlens], hlb, ?_⟩
  · intro hle
    rw [hlens]
    rcases hn1' with h | h
    · exact h
    · rw [h, hfull]; exact hle
  · intro hok1
    obtain ⟨htable, hkraft⟩ := hok hok1
    refine ⟨by rw [hwl], by rw [hrl, hlens], htable, hkraft, by rw [hrl, hlens], ?_⟩
    intro sym hsym hpos hle16
    obtain ⟨hle, hcan, hlt⟩ := htable.2 sym hsym hpos
    have hw16 : (words.val[sym]!).val < 65536 := by
      have h2 : 2 ^ (lens.val[sym]!).val ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    exact hrvals sym (by rw [← hlens]; exact hsym) hpos hle16 hw16

end Gzip.Proofs.Canon
