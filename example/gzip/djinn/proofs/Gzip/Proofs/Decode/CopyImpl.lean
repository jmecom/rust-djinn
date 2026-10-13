import Gzip.Proofs.Decode.ReaderImpl
import Gzip.Proofs.Decode.WideFacts
import Gzip.Proofs.Decode.SubsliceImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.WideFacts Gzip.Proofs.Decode.SubsliceImpl

namespace Gzip.Proofs.Decode.CopyImpl

theorem copy_length (prev out : List U8) (d len : ℤ) (h : copy_spec prev d len out) :
    prev.length ≤ out.length := by
  have hp := congrArg List.length h.2.2.2.1
  simp only [List.drop_zero, Int.toNat_natCast, List.length_take] at hp
  omega

/-! ## eight bytes at a time

`load8_correct`, `store8_correct` and `Stored` are in `SubsliceImpl`. -/

/-- The bytes of a little-endian number of eight bytes. -/
theorem le8_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256)
    (h3 : b3 < 256) (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256) :
    let w := le [b0, b1, b2, b3, b4, b5, b6, b7]
    w % 256 = b0 ∧ w / 256 % 256 = b1 ∧ w / 65536 % 256 = b2 ∧ w / 16777216 % 256 = b3 ∧
      w / 4294967296 % 256 = b4 ∧ w / 1099511627776 % 256 = b5 ∧
      w / 281474976710656 % 256 = b6 ∧ w / 72057594037927936 % 256 = b7 := by
  simp only [le]
  omega

/-- A byte repeated eight times. -/
theorem rep8_bytes (b : Nat) (hb : b < 256) :
    let w := b * 72340172838076673
    w % 256 = b ∧ w / 256 % 256 = b ∧ w / 65536 % 256 = b ∧ w / 16777216 % 256 = b ∧
      w / 4294967296 % 256 = b ∧ w / 1099511627776 % 256 = b ∧
      w / 281474976710656 % 256 = b ∧ w / 72057594037927936 % 256 = b := by
  have hw : b * 72340172838076673 = le [b, b, b, b, b, b, b, b] := by
    simp only [le]; ring
  simp only [hw]
  exact le8_bytes b b b b b b b b hb hb hb hb hb hb hb hb

theorem getElem!_set' (l : List U8) (i k : Nat) (x : U8) (hk : k < l.length) :
    (l.set i x)[k]! = if k = i then x else l[k]! := Djinn.Vocab.getElem!_set l i k x hk

/-! ## the copy, position by position -/

/-- The first `m` bytes of a copy of distance `d` are in place at `n` and the bytes before `n`
are untouched. -/
def Copied (v0 v : List U8) (n d m : Nat) : Prop :=
  v.length = v0.length ∧ (∀ k, k < n → v[k]! = v0[k]!) ∧
  (∀ k, n ≤ k → k < n + m → v[k]! = v[k - d]!)

theorem copied_zero (v0 : List U8) (n d : Nat) : Copied v0 v0 n d 0 :=
  ⟨rfl, fun _ _ => rfl, fun _ _ _ => by omega⟩

theorem copied_mono (v0 v : List U8) (n d m m' : Nat) (h : Copied v0 v n d m) (hm : m' ≤ m) :
    Copied v0 v n d m' :=
  ⟨h.1, h.2.1, fun k hk hk' => h.2.2 k hk (by omega)⟩

/-- A chunk of eight bytes from `d ≥ 8` back extends the copy by eight. -/
theorem copied_chunk (v0 v v' : List U8) (n d m : Nat) (w : Nat) (hd : 8 ≤ d) (hdn : d ≤ n)
    (hb : n + m + 8 ≤ v.length) (hc : Copied v0 v n d m)
    (hw : w = le [(v[n + m - d]!).val, (v[n + m - d + 1]!).val, (v[n + m - d + 2]!).val,
      (v[n + m - d + 3]!).val, (v[n + m - d + 4]!).val, (v[n + m - d + 5]!).val,
      (v[n + m - d + 6]!).val, (v[n + m - d + 7]!).val])
    (hs : Stored v v' (n + m) w) : Copied v0 v' n d (m + 8) := by
  obtain ⟨hl, hpre, hcp⟩ := hc
  obtain ⟨hl', hkeep, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ := hs
  have hbytes := le8_bytes (v[n + m - d]!).val (v[n + m - d + 1]!).val (v[n + m - d + 2]!).val
    (v[n + m - d + 3]!).val (v[n + m - d + 4]!).val (v[n + m - d + 5]!).val
    (v[n + m - d + 6]!).val (v[n + m - d + 7]!).val (by scalar_tac) (by scalar_tac)
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
  simp only at hbytes
  rw [← hw] at hbytes
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hbytes
  refine ⟨hl'.trans hl, ?_, ?_⟩
  · intro k hk
    rw [hkeep k (by omega) (by omega)]
    exact hpre k hk
  · intro k hk hk'
    by_cases hold : k < n + m
    · rw [hkeep k (by omega) (by omega), hkeep (k - d) (by omega) (by omega)]
      exact hcp k hk hold
    · have hsrc : v'[k - d]! = v[k - d]! := hkeep (k - d) (by omega) (by omega)
      rw [hsrc]
      apply UScalar.eq_of_val_eq
      have hcases : k = n + m ∨ k = n + m + 1 ∨ k = n + m + 2 ∨ k = n + m + 3 ∨ k = n + m + 4 ∨
          k = n + m + 5 ∨ k = n + m + 6 ∨ k = n + m + 7 := by omega
      rcases hcases with hc | hc | hc | hc | hc | hc | hc | hc <;> subst hc
      · rw [hw0, hb0]
      · rw [hw1, hb1]; congr 2; omega
      · rw [hw2, hb2]; congr 2; omega
      · rw [hw3, hb3]; congr 2; omega
      · rw [hw4, hb4]; congr 2; omega
      · rw [hw5, hb5]; congr 2; omega
      · rw [hw6, hb6]; congr 2; omega
      · rw [hw7, hb7]; congr 2; omega

/-- One byte from `d ≥ 1` back extends the copy by one. -/
theorem copied_byte (v0 v : List U8) (n d m : Nat) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hb : n + m < v.length) (hc : Copied v0 v n d m) :
    Copied v0 (v.set (n + m) (v[n + m - d]!)) n d (m + 1) := by
  obtain ⟨hl, hpre, hcp⟩ := hc
  refine ⟨by simp only [List.length_set]; exact hl, ?_, ?_⟩
  · intro k hk
    rw [getElem!_set' v (n + m) k _ (by omega), if_neg (by omega)]
    exact hpre k hk
  · intro k hk hk'
    rw [getElem!_set' v (n + m) k _ (by omega), getElem!_set' v (n + m) (k - d) _ (by omega)]
    rw [if_neg (show ¬ (k - d = n + m) by omega)]
    by_cases he : k = n + m
    · rw [if_pos he, he]
    · rw [if_neg he]
      exact hcp k hk (by omega)

/-- Bytes `n` to `n + m` all hold `b`, the byte before `n`, and the bytes before `n` are untouched. -/
def Filled (v0 v : List U8) (n m : Nat) (b : U8) : Prop :=
  v.length = v0.length ∧ (∀ k, k < n → v[k]! = v0[k]!) ∧
  (∀ k, n ≤ k → k < n + m → v[k]! = b)

theorem filled_zero (v0 : List U8) (n : Nat) (b : U8) : Filled v0 v0 n 0 b :=
  ⟨rfl, fun _ _ => rfl, fun _ _ _ => by omega⟩

theorem filled_chunk (v0 v v' : List U8) (n m : Nat) (b : U8) (hb : n + m + 8 ≤ v.length)
    (hf : Filled v0 v n m b) (hs : Stored v v' (n + m) (b.val * 72340172838076673)) :
    Filled v0 v' n (m + 8) b := by
  obtain ⟨hl, hpre, hfl⟩ := hf
  obtain ⟨hl', hkeep, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ := hs
  have hbytes := rep8_bytes b.val (by scalar_tac)
  simp only at hbytes
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hbytes
  refine ⟨hl'.trans hl, ?_, ?_⟩
  · intro k hk
    rw [hkeep k (by omega) (by omega)]
    exact hpre k hk
  · intro k hk hk'
    by_cases hold : k < n + m
    · rw [hkeep k (by omega) (by omega)]
      exact hfl k hk hold
    · apply UScalar.eq_of_val_eq
      have hcases : k = n + m ∨ k = n + m + 1 ∨ k = n + m + 2 ∨ k = n + m + 3 ∨ k = n + m + 4 ∨
          k = n + m + 5 ∨ k = n + m + 6 ∨ k = n + m + 7 := by omega
      rcases hcases with hc | hc | hc | hc | hc | hc | hc | hc <;> subst hc
      · rw [hw0, hb0]
      · rw [hw1, hb1]
      · rw [hw2, hb2]
      · rw [hw3, hb3]
      · rw [hw4, hb4]
      · rw [hw5, hb5]
      · rw [hw6, hb6]
      · rw [hw7, hb7]

theorem filled_copied (v0 v : List U8) (n m : Nat) (hn : 1 ≤ n) (hf : Filled v0 v n m (v0[n - 1]!)) :
    Copied v0 v n 1 m := by
  obtain ⟨hl, hpre, hfl⟩ := hf
  refine ⟨hl, hpre, ?_⟩
  intro k hk hk'
  rw [hfl k hk hk']
  by_cases he : k = n
  · rw [he, hpre (n - 1) (by omega)]
  · rw [hfl (k - 1) (by omega) (by omega)]

/-- A finished copy is the specification's copy on the prefixes. -/
theorem copied_spec (v0 v : List U8) (n d len : Nat) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hb : n + len ≤ v0.length) (hc : Copied v0 v n d len) :
    copy_spec (v0.take n) d len (v.take (n + len)) := by
  obtain ⟨hl, hpre, hcp⟩ := hc
  have hln : (v0.take n).length = n := List.length_take_of_le (by omega)
  have hlv : (v.take (n + len)).length = n + len := List.length_take_of_le (by omega)
  refine ⟨trivial, ⟨by omega, by omega⟩, ?_, ?_, ?_⟩
  · rw [hlv, hln]; push_cast; ring
  · simp only [List.drop_zero, Int.toNat_natCast, hln, List.take_take, Nat.min_eq_left (by omega : n ≤ n + len)]
    apply list_eq _ _ (by rw [List.length_take_of_le (by omega), hln])
    intro k hk
    rw [List.length_take_of_le (by omega)] at hk
    rw [RoundTrip.take_get _ _ _ hk, RoundTrip.take_get _ _ _ hk]
    exact hpre k hk
  · intro k hk hk'
    rw [hln] at hk
    rw [hlv] at hk'
    have hkn : k.toNat < n + len := by omega
    have hkd : (k - d).toNat < n + len := by omega
    rw [RoundTrip.take_get _ _ _ hkn, RoundTrip.take_get _ _ _ hkd]
    have he : (k - d).toNat = k.toNat - d := by omega
    rw [he]
    exact hcp k.toNat (by omega) (by omega)

/-! ## the copy within its window

For distances of eight or more, `copy_at` works in the window of the buffer that starts `d`
bytes before the destination: source chunk `k` is at `k` of the window, its destination at
`d + k`. -/

/-- Within the window: the first `m` bytes of the copy are in place at `d` and the `d` bytes
before them are untouched. -/
def SCopied (o0 o : List U8) (d m : Nat) : Prop :=
  o.length = o0.length ∧ (∀ k, k < d → o[k]! = o0[k]!) ∧ (∀ k, k < m → o[d + k]! = o[k]!)

theorem scopied_zero (o0 : List U8) (d : Nat) : SCopied o0 o0 d 0 :=
  ⟨rfl, fun _ _ => rfl, fun _ h => by omega⟩

theorem scopied_mono (o0 o : List U8) (d m m' : Nat) (h : SCopied o0 o d m) (hm : m' ≤ m) :
    SCopied o0 o d m' :=
  ⟨h.1, h.2.1, fun k hk => h.2.2 k (by omega)⟩

/-- A chunk of eight bytes from `d ≥ 8` back extends the copy by eight. -/
theorem scopied_chunk (o0 o o' : List U8) (d m : Nat) (w : Nat) (hd : 8 ≤ d)
    (hb : d + m + 8 ≤ o.length) (hc : SCopied o0 o d m)
    (hw : w = le [(o[m]!).val, (o[m + 1]!).val, (o[m + 2]!).val, (o[m + 3]!).val,
      (o[m + 4]!).val, (o[m + 5]!).val, (o[m + 6]!).val, (o[m + 7]!).val])
    (hs : Stored o o' (d + m) w) : SCopied o0 o' d (m + 8) := by
  obtain ⟨hl, hpre, hcp⟩ := hc
  obtain ⟨hl', hkeep, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ := hs
  have hbytes := le8_bytes (o[m]!).val (o[m + 1]!).val (o[m + 2]!).val (o[m + 3]!).val
    (o[m + 4]!).val (o[m + 5]!).val (o[m + 6]!).val (o[m + 7]!).val (by scalar_tac) (by scalar_tac)
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
  simp only at hbytes
  rw [← hw] at hbytes
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hbytes
  refine ⟨hl'.trans hl, ?_, ?_⟩
  · intro k hk
    rw [hkeep k (by omega) (by omega)]
    exact hpre k hk
  · intro k hk
    by_cases hold : k < m
    · rw [hkeep (d + k) (by omega) (by omega), hkeep k (by omega) (by omega)]
      exact hcp k hold
    · have hsrc : o'[k]! = o[k]! := hkeep k (by omega) (by omega)
      rw [hsrc]
      apply UScalar.eq_of_val_eq
      have hcases : k = m ∨ k = m + 1 ∨ k = m + 2 ∨ k = m + 3 ∨ k = m + 4 ∨
          k = m + 5 ∨ k = m + 6 ∨ k = m + 7 := by omega
      rcases hcases with hc | hc | hc | hc | hc | hc | hc | hc <;> subst hc
      · rw [hw0, hb0]
      · rw [show d + (m + 1) = d + m + 1 by omega, hw1, hb1]
      · rw [show d + (m + 2) = d + m + 2 by omega, hw2, hb2]
      · rw [show d + (m + 3) = d + m + 3 by omega, hw3, hb3]
      · rw [show d + (m + 4) = d + m + 4 by omega, hw4, hb4]
      · rw [show d + (m + 5) = d + m + 5 by omega, hw5, hb5]
      · rw [show d + (m + 6) = d + m + 6 by omega, hw6, hb6]
      · rw [show d + (m + 7) = d + m + 7 by omega, hw7, hb7]

/-- The window written back into the buffer `d` bytes before `n` is the copy on the buffer. -/
theorem scopied_copied (v0 o0 o' : List U8) (n d len : Nat) (hd : d ≤ n)
    (hb : n + len + 24 ≤ v0.length) (hlen : o0.length = d + len + 24)
    (hel : ∀ k, k < d + len + 24 → o0[k]! = v0[n - d + k]!)
    (hc : SCopied o0 o' d len) : Copied v0 (v0.setSlice! (n - d) o') n d len := by
  obtain ⟨hl, hpre, hcp⟩ := hc
  have hl' : o'.length = d + len + 24 := hl.trans hlen
  refine ⟨List.length_setSlice! _ _ _, ?_, ?_⟩
  · intro k hk
    by_cases hlt : k < n - d
    · exact List.getElem!_setSlice!_prefix _ _ _ _ hlt
    · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by omega, by omega⟩]
      rw [hpre (k - (n - d)) (by omega), hel (k - (n - d)) (by omega)]
      congr 1
      omega
  · intro k hk hk'
    rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by omega, by omega⟩,
      List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by omega, by omega⟩]
    have h1 : k - (n - d) = d + (k - n) := by omega
    have h2 : k - d - (n - d) = k - n := by omega
    rw [h1, h2]
    exact hcp (k - n) (by omega)

/-! ## the loops -/

def ChunkInv (v0 : List U8) (n d : Usize) (out : alloc.vec.Vec U8) (k : Usize) : Prop :=
  Copied v0 out.val n.val d.val k.val

def SChunkInv (o0 : List U8) (d : Usize) (o : Aeneas.Std.Slice U8) (k : Usize) : Prop :=
  SCopied o0 o.val d.val k.val

theorem schunk_body (o0 : List U8) (d len : Usize) (o : Aeneas.Std.Slice U8) (k : Usize)
    (hd : 8 ≤ d.val) (hb : d.val + len.val + 24 ≤ o0.length) (h : SChunkInv o0 d o k) :
    copy_tail_loop.body d len o k ⦃ z => match z with
      | .done v => SCopied o0 v.val d.val len.val
      | .cont (v, j) => SChunkInv o0 d v j ∧ len.val - j.val < len.val - k.val ⦄ := by
  have hl := h.1
  unfold copy_tail_loop.body
  step*
  all_goals try scalar_tac
  · have hc : SCopied o0 o1.val d.val (k.val + 8) := by
      apply scopied_chunk o0 o.val o1.val d.val k.val i1.val hd (by scalar_tac) h i1_post
      have hi : i.val = d.val + k.val := by scalar_tac
      rw [← hi]
      exact o1_post
    refine ⟨?_, by scalar_tac⟩
    unfold SChunkInv
    rw [k1_post]
    exact hc
  · exact scopied_mono _ _ _ _ _ h (by scalar_tac)

theorem schunk_loop (o0 : List U8) (d len : Usize) (o : Aeneas.Std.Slice U8) (k : Usize)
    (hd : 8 ≤ d.val) (hb : d.val + len.val + 24 ≤ o0.length) (h : SChunkInv o0 d o k) :
    copy_tail_loop o d len k ⦃ v => SCopied o0 v.val d.val len.val ⦄ := by
  unfold copy_tail_loop
  apply loop.spec_decr_nat (fun (_, j) => len.val - j.val) (fun (v, j) => SChunkInv o0 d v j)
  · rintro ⟨v, j⟩ hinv
    apply WP.spec_mono (schunk_body o0 d len v j hd hb hinv)
    intro z hz
    cases z <;> exact hz
  · exact h

def FillInv (v0 : List U8) (n : Usize) (b : U8) (out : alloc.vec.Vec U8) (k : Usize) : Prop :=
  Filled v0 out.val n.val k.val b

theorem fill_body (v0 : List U8) (n len : Usize) (b : U8) (w : U64) (out : alloc.vec.Vec U8) (k : Usize)
    (hw : w.val = b.val * 72340172838076673) (hb : n.val + len.val + 24 ≤ v0.length)
    (h : FillInv v0 n b out k) :
    copy_at_loop0.body n len w out k ⦃ z => match z with
      | .done v => Filled v0 v.val n.val len.val b
      | .cont (v, j) => FillInv v0 n b v j ∧ len.val - j.val < len.val - k.val ⦄ := by
  have hl := h.1
  unfold copy_at_loop0.body
  step*
  all_goals try scalar_tac
  · have hf : Filled v0 out1.val n.val (k.val + 8) b := by
      apply filled_chunk v0 out.val out1.val n.val k.val b (by scalar_tac) h
      have hi : i.val = n.val + k.val := by scalar_tac
      rw [← hi, ← hw]
      exact out1_post
    refine ⟨?_, by scalar_tac⟩
    unfold FillInv
    rw [k1_post]
    exact hf
  · exact ⟨h.1, h.2.1, fun j hj hj' => h.2.2 j hj (by scalar_tac)⟩

theorem fill_loop (v0 : List U8) (n len : Usize) (b : U8) (w : U64) (out : alloc.vec.Vec U8) (k : Usize)
    (hw : w.val = b.val * 72340172838076673) (hb : n.val + len.val + 24 ≤ v0.length)
    (h : FillInv v0 n b out k) :
    copy_at_loop0 out n len w k ⦃ v => Filled v0 v.val n.val len.val b ⦄ := by
  unfold copy_at_loop0
  apply loop.spec_decr_nat (fun (_, j) => len.val - j.val) (fun (v, j) => FillInv v0 n b v j)
  · rintro ⟨v, j⟩ hinv
    apply WP.spec_mono (fill_body v0 n len b w v j hw hb hinv)
    intro z hz
    cases z <;> exact hz
  · exact h

theorem byte_body (v0 : List U8) (n d len : Usize) (out : alloc.vec.Vec U8) (k : Usize)
    (hd : 1 ≤ d.val) (hdn : d.val ≤ n.val) (hb : n.val + len.val + 24 ≤ v0.length)
    (h : ChunkInv v0 n d out k) :
    copy_at_loop1.body n d len out k ⦃ z => match z with
      | .done v => Copied v0 v.val n.val d.val len.val
      | .cont (v, j) => ChunkInv v0 n d v j ∧ len.val - j.val < len.val - k.val ⦄ := by
  have hl := h.1
  unfold copy_at_loop1.body
  step*
  all_goals try scalar_tac
  · have hi : i.val = n.val + k.val := by scalar_tac
    have h1 : i1.val = n.val + k.val - d.val := by scalar_tac
    have he : i2 = out.val[n.val + k.val - d.val]! := by
      rw [← h1, getElem!_pos _ _ (by scalar_tac)]; exact i2_post
    have hc := copied_byte v0 out.val n.val d.val k.val hd hdn (by scalar_tac) h
    refine ⟨?_, by scalar_tac⟩
    unfold ChunkInv
    rw [k1_post, index_mut_back_post]
    simp only [alloc.vec.Vec.set_val_eq]
    rw [hi, he]
    exact hc
  · exact copied_mono _ _ _ _ _ _ h (by scalar_tac)

theorem byte_loop (v0 : List U8) (n d len : Usize) (out : alloc.vec.Vec U8) (k : Usize)
    (hd : 1 ≤ d.val) (hdn : d.val ≤ n.val) (hb : n.val + len.val + 24 ≤ v0.length)
    (h : ChunkInv v0 n d out k) :
    copy_at_loop1 out n d len k ⦃ v => Copied v0 v.val n.val d.val len.val ⦄ := by
  unfold copy_at_loop1
  apply loop.spec_decr_nat (fun (_, j) => len.val - j.val) (fun (v, j) => ChunkInv v0 n d v j)
  · rintro ⟨v, j⟩ hinv
    apply WP.spec_mono (byte_body v0 n d len v j hd hdn hb hinv)
    intro z hz
    cases z <;> exact hz
  · exact h

/-- The suffix of a vector from `i`, borrowed mutably: writing a slice back replaces the suffix. -/
theorem vec_range_from_mut (v : alloc.vec.Vec U8) (i : Usize) (h : i.val ≤ v.val.length) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeFromUsizeSlice U8) v { start := i }
      ⦃ s back => s.val = v.val.drop i.val ∧ ∀ s', (back s').val = v.val.setSlice! i.val s'.val ⦄ := by
  have hv : v.slice.val.length = v.val.length := rfl
  unfold alloc.vec.Vec.index_mut
  simp only [core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut]
  split
  · step*
    first
    | (show Result.ok _ ⦃ _ ⦄
       rw [WP.spec_ok])
    | (rw [WP.spec_equiv_exists]
       refine ⟨_, rfl, ?_⟩)
    simp only [WP.uncurry', Slice.from_val, Slice.drop]
    all_goals try (refine ⟨rfl, ?_⟩; intro s'; simp only [alloc.vec.Vec.val, Slice.from_val])
  · exfalso
    rename_i hc
    apply hc
    simp only [Slice.length]; omega

/-- The prefix of a slice up to `j`, borrowed mutably: writing a slice back replaces the prefix. -/
theorem slice_range_to_mut (s : Aeneas.Std.Slice U8) (j : Usize) (h : j.val ≤ s.val.length) :
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut { «end» := j } s
      ⦃ o back => o.val = s.val.slice 0 j.val ∧ ∀ o', (back o').val = s.val.setSlice! 0 o'.val ⦄ := by
  simp only [core.slice.index.SliceIndexRangeToUsizeSlice.index_mut]
  split
  · first
    | (show Result.ok _ ⦃ _ ⦄
       rw [WP.spec_ok])
    | (rw [WP.spec_equiv_exists]
       refine ⟨_, rfl, ?_⟩)
    simp only [WP.uncurry', Slice.from_val]
    all_goals try exact ⟨rfl, fun _ => rfl⟩
    all_goals try exact ⟨trivial, fun _ => trivial⟩
  · exfalso
    rename_i hc
    apply hc
    simp only [Slice.length]; omega

/-- The window written back through both borrows: the suffix of the buffer from `start` with
its prefix replaced, then the suffix written back. -/
theorem window_back (v o' : List U8) (start : Nat) (hs : start ≤ v.length)
    (ho : start + o'.length ≤ v.length) :
    (v.setSlice! start ((v.drop start).setSlice! 0 o')).length = v.length ∧
    (∀ j, j < start → (v.setSlice! start ((v.drop start).setSlice! 0 o'))[j]! = v[j]!) ∧
    (∀ j, start ≤ j → j < start + o'.length →
      (v.setSlice! start ((v.drop start).setSlice! 0 o'))[j]! = o'[j - start]!) := by
  have hl1 : ((v.drop start).setSlice! 0 o').length = v.length - start := by
    rw [List.length_setSlice!, List.length_drop]
  refine ⟨List.length_setSlice! _ _ _, ?_, ?_⟩
  · intro j hj
    exact List.getElem!_setSlice!_prefix _ _ _ _ hj
  · intro j hj1 hj2
    have hld : (v.drop start).length = v.length - start := List.length_drop
    rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨hj1, by rw [hl1]; omega, by omega⟩,
      List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by omega, by rw [hld]; omega⟩, Nat.sub_zero]

/-- A buffer whose window from `d` before `n` holds a finished copy, and which agrees with the
old buffer before the window, is the copy on the buffer. -/
theorem scopied_copied' (v0 o0 o' v' : List U8) (n d len : Nat) (hd : d ≤ n)
    (hb : n + len + 24 ≤ v0.length) (hlen : o0.length = d + len + 24)
    (hel : ∀ k, k < d + len + 24 → o0[k]! = v0[n - d + k]!)
    (hc : SCopied o0 o' d len)
    (hvl : v'.length = v0.length) (hpre : ∀ j, j < n - d → v'[j]! = v0[j]!)
    (hmid : ∀ j, n - d ≤ j → j < n - d + o'.length → v'[j]! = o'[j - (n - d)]!) :
    Copied v0 v' n d len := by
  obtain ⟨hl, hpre', hcp⟩ := hc
  have hl' : o'.length = d + len + 24 := hl.trans hlen
  refine ⟨hvl, ?_, ?_⟩
  · intro k hk
    by_cases hlt : k < n - d
    · exact hpre k hlt
    · rw [hmid k (by omega) (by omega), hpre' (k - (n - d)) (by omega), hel (k - (n - d)) (by omega)]
      congr 1
      omega
  · intro k hk hk'
    rw [hmid k (by omega) (by omega), hmid (k - d) (by omega) (by omega)]
    have h1 : k - (n - d) = d + (k - n) := by omega
    have h2 : k - d - (n - d) = k - n := by omega
    rw [h1, h2]
    exact hcp (k - n) (by omega)

/-! ## the second chunk from registers

For `8 ≤ d < 16` the second chunk's source overlaps the first chunk's destination, so `copy_at`
assembles it from the two words loaded before the first store: the low `d - 8` bytes of the
word from 8 and, above them, the low bytes of the first chunk. -/

/-- The bytes a store left, uniformly. -/
theorem stored_bytes (v v' : List U8) (i w : Nat) (hs : Stored v v' i w) :
    ∀ r, r < 8 → (v'[i + r]!).val = w / 256 ^ r % 256 := by
  obtain ⟨_, _, h0, h1, h2, h3, h4, h5, h6, h7⟩ := hs
  intro r hr
  have hc : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc <;> subst hc <;>
    simp only [Nat.add_zero, Nat.pow_zero, Nat.div_one, Nat.pow_one, Nat.reducePow] <;> assumption

-- For a distance `8 ≤ d < 16`: the eight bytes from 8 of the window after the first chunk `w0`
-- was stored at `d`, as a number: the low `d - 8` bytes of `w1`, the window's bytes from 8, and
-- above them the low bytes of `w0`.
set_option maxHeartbeats 8000000 in
theorem mix_stored (o o1 : List U8) (d w0 w1 : Nat) (hd8 : 8 ≤ d) (hd16 : d < 16) (hl : 16 ≤ o.length)
    (hw0 : w0 = le [(o[0]!).val, (o[1]!).val, (o[2]!).val, (o[3]!).val, (o[4]!).val, (o[5]!).val,
      (o[6]!).val, (o[7]!).val])
    (hw1 : w1 = le [(o[8]!).val, (o[9]!).val, (o[10]!).val, (o[11]!).val, (o[12]!).val, (o[13]!).val,
      (o[14]!).val, (o[15]!).val])
    (hs : Stored o o1 d w0) :
    w1 % 2 ^ (8 * (d - 8)) + (w0 * 2 ^ (8 * (d - 8))) % 2 ^ 64 =
      le [(o1[8]!).val, (o1[9]!).val, (o1[10]!).val, (o1[11]!).val, (o1[12]!).val, (o1[13]!).val,
        (o1[14]!).val, (o1[15]!).val] := by
  have hkeep := hs.2.1
  have hb := stored_bytes o o1 d w0 hs
  have f : ∀ j, 8 ≤ j → j < 16 →
      (o1[j]!).val = if j < d then (o[j]!).val else w0 / 256 ^ (j - d) % 256 := by
    intro j hj8 hj16
    by_cases hjd : j < d
    · rw [if_pos hjd, hkeep j (by omega) (Or.inl hjd)]
    · rw [if_neg hjd, ← hb (j - d) (by omega)]
      congr 3
      omega
  have f8 := f 8 (by omega) (by omega)
  have f9 := f 9 (by omega) (by omega)
  have f10 := f 10 (by omega) (by omega)
  have f11 := f 11 (by omega) (by omega)
  have f12 := f 12 (by omega) (by omega)
  have f13 := f 13 (by omega) (by omega)
  have f14 := f 14 (by omega) (by omega)
  have f15 := f 15 (by omega) (by omega)
  clear f hb hkeep hs
  have c0 : (o[0]!).val < 256 := by scalar_tac
  have c1 : (o[1]!).val < 256 := by scalar_tac
  have c2 : (o[2]!).val < 256 := by scalar_tac
  have c3 : (o[3]!).val < 256 := by scalar_tac
  have c4 : (o[4]!).val < 256 := by scalar_tac
  have c5 : (o[5]!).val < 256 := by scalar_tac
  have c6 : (o[6]!).val < 256 := by scalar_tac
  have c7 : (o[7]!).val < 256 := by scalar_tac
  have c8 : (o[8]!).val < 256 := by scalar_tac
  have c9 : (o[9]!).val < 256 := by scalar_tac
  have c10 : (o[10]!).val < 256 := by scalar_tac
  have c11 : (o[11]!).val < 256 := by scalar_tac
  have c12 : (o[12]!).val < 256 := by scalar_tac
  have c13 : (o[13]!).val < 256 := by scalar_tac
  have c14 : (o[14]!).val < 256 := by scalar_tac
  have c15 : (o[15]!).val < 256 := by scalar_tac
  simp only [le] at hw0 hw1 ⊢
  have hcases : d = 8 ∨ d = 9 ∨ d = 10 ∨ d = 11 ∨ d = 12 ∨ d = 13 ∨ d = 14 ∨ d = 15 := by omega
  rcases hcases with hd | hd | hd | hd | hd | hd | hd | hd <;> subst hd <;>
    simp only [Nat.reduceLT, if_true, if_false, Nat.reduceSub, Nat.reduceMul, Nat.reducePow,
      Nat.pow_zero, Nat.div_one] at f8 f9 f10 f11 f12 f13 f14 f15 ⊢ <;> omega

theorem u64_size' : U64.size = 2 ^ 64 := by scalar_tac

/-- The mixed word fits in 64 bits. -/
theorem mix_lt (w0 w1 d : Nat) (hd8 : 8 ≤ d) (hd16 : d < 16) :
    w1 % 2 ^ (8 * (d - 8)) + (w0 * 2 ^ (8 * (d - 8))) % 2 ^ 64 < 2 ^ 64 := by
  have hcases : d = 8 ∨ d = 9 ∨ d = 10 ∨ d = 11 ∨ d = 12 ∨ d = 13 ∨ d = 14 ∨ d = 15 := by omega
  rcases hcases with hd | hd | hd | hd | hd | hd | hd | hd <;> subst hd <;>
    simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.mul_one, Nat.mod_one] <;> omega

/-- For a distance of sixteen or more the first store leaves the bytes from 8 alone. -/
theorem keep_bytes_16 (o o1 : List U8) (d w0 : Nat) (hd : 16 ≤ d) (hl : 16 ≤ o.length)
    (hs : Stored o o1 d w0) :
    le [(o1[8]!).val, (o1[9]!).val, (o1[10]!).val, (o1[11]!).val, (o1[12]!).val, (o1[13]!).val,
        (o1[14]!).val, (o1[15]!).val] =
      le [(o[8]!).val, (o[9]!).val, (o[10]!).val, (o[11]!).val, (o[12]!).val, (o[13]!).val,
        (o[14]!).val, (o[15]!).val] := by
  obtain ⟨_, hkeep, _⟩ := hs
  rw [hkeep 8 (by omega) (Or.inl (by omega)), hkeep 9 (by omega) (Or.inl (by omega)),
    hkeep 10 (by omega) (Or.inl (by omega)), hkeep 11 (by omega) (Or.inl (by omega)),
    hkeep 12 (by omega) (Or.inl (by omega)), hkeep 13 (by omega) (Or.inl (by omega)),
    hkeep 14 (by omega) (Or.inl (by omega)), hkeep 15 (by omega) (Or.inl (by omega))]

-- The two source words were loaded before either store. If len ≤ d, none of
-- the source bytes required for this copy can be changed by the first store.
theorem scopied_short_nonoverlap (o o1 o2 : List U8) (d len w0 w1 : Nat)
    (hd8 : 8 ≤ d) (hlen16 : len ≤ 16) (hlen_d : len ≤ d)
    (hb : d + 16 ≤ o.length)
    (hw0 : w0 = le [(o[0]!).val, (o[1]!).val, (o[2]!).val, (o[3]!).val,
      (o[4]!).val, (o[5]!).val, (o[6]!).val, (o[7]!).val])
    (hw1 : w1 = le [(o[8]!).val, (o[9]!).val, (o[10]!).val, (o[11]!).val,
      (o[12]!).val, (o[13]!).val, (o[14]!).val, (o[15]!).val])
    (hs1 : Stored o o1 d w0) (hs2 : Stored o1 o2 (d + 8) w1) :
    SCopied o o2 d len := by
  have hbytes0 := le8_bytes (o[0]!).val (o[1]!).val (o[2]!).val (o[3]!).val
    (o[4]!).val (o[5]!).val (o[6]!).val (o[7]!).val (by scalar_tac) (by scalar_tac)
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
  have hbytes1 := le8_bytes (o[8]!).val (o[9]!).val (o[10]!).val (o[11]!).val
    (o[12]!).val (o[13]!).val (o[14]!).val (o[15]!).val (by scalar_tac) (by scalar_tac)
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
  simp only at hbytes0 hbytes1
  rw [← hw0] at hbytes0
  rw [← hw1] at hbytes1
  obtain ⟨hb00, hb01, hb02, hb03, hb04, hb05, hb06, hb07⟩ := hbytes0
  obtain ⟨hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17⟩ := hbytes1
  have bytes0 : ∀ r, r < 8 → w0 / 256 ^ r % 256 = (o[r]!).val := by
    intro r hr
    have hc : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
    rcases hc with hc | hc | hc | hc | hc | hc | hc | hc <;> subst hc <;>
      simp only [Nat.pow_zero, Nat.div_one, Nat.pow_one, Nat.reducePow] <;> assumption
  have bytes1 : ∀ r, r < 8 → w1 / 256 ^ r % 256 = (o[8 + r]!).val := by
    intro r hr
    have hc : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
    rcases hc with hc | hc | hc | hc | hc | hc | hc | hc <;> subst hc <;>
      simp only [Nat.add_zero, Nat.reduceAdd, Nat.pow_zero, Nat.div_one, Nat.pow_one, Nat.reducePow] <;> assumption
  have hl1 := hs1.1
  have hl2 := hs2.1
  refine ⟨hl2.trans hl1, ?_, ?_⟩
  · intro k hk
    rw [hs2.2.1 k (by omega) (Or.inl (by omega)), hs1.2.1 k (by omega) (Or.inl hk)]
  · intro k hk
    rw [hs2.2.1 k (by omega) (Or.inl (by omega)), hs1.2.1 k (by omega) (Or.inl (by omega))]
    apply UScalar.eq_of_val_eq
    by_cases hk8 : k < 8
    · rw [hs2.2.1 (d + k) (by omega) (Or.inl (by omega)), stored_bytes o o1 d w0 hs1 k hk8, bytes0 k hk8]
    · have hk16 : k < 16 := by omega
      rw [show d + k = d + 8 + (k - 8) by omega,
        stored_bytes o1 o2 (d + 8) w1 hs2 (k - 8) (by omega), bytes1 (k - 8) (by omega)]
      congr 2
      omega


/-- The start of a copy's source, computed by the caller as a wrapping subtraction before its
check that the distance reaches no further back than the content, is the difference. -/
theorem usize_wrapping_sub_of_le (n d : Usize) (h : d.val ≤ n.val) :
    (core.num.Usize.wrapping_sub n d).val = n.val - d.val := by
  rw [core.num.Usize.wrapping_sub_val_eq]
  have hn := n.hBounds
  have hd := d.hBounds
  simp only [UScalar.size, UScalarTy.numBits] at *
  rcases System.Platform.numBits_eq with hb | hb <;> simp only [hb] at * <;> omega

-- `copy_at` performs the specification's copy on the prefix of the buffer and keeps its
-- length; `start` is where the source begins, `d` before `n`.
set_option maxHeartbeats 8000000 in
@[step]
theorem copy_at_correct (out : alloc.vec.Vec U8) (start n d len : Usize)
    (hstart : start.val = n.val - d.val)
    (hd : 1 ≤ d.val) (hdn : d.val ≤ n.val) (hb : n.val + len.val + 24 ≤ out.val.length) :
    copy_at out start n d len ⦃ v => v.val.length = out.val.length ∧
      copy_spec (out.val.take n.val) d.val len.val (v.val.take (n.val + len.val)) ⦄ := by
  have hfinish (v : alloc.vec.Vec U8) (hc : Copied out.val v.val n.val d.val len.val) :
      v.val.length = out.val.length ∧
      copy_spec (out.val.take n.val) d.val len.val (v.val.take (n.val + len.val)) :=
    ⟨hc.1, copied_spec out.val v.val n.val d.val len.val hd hdn (by omega) hc⟩
  unfold copy_at
  split
  · -- the window of the buffer from d before n to n + len + 24, with the two unconditional
    -- chunks and the loop on it
    have hd8 : 8 ≤ d.val := by scalar_tac
    step with (vec_range_from_mut out start (by scalar_tac)) as ⟨s, back, hs, hback⟩
    step as ⟨i, hi⟩
    all_goals try scalar_tac
    step as ⟨i1, hi1⟩
    all_goals try scalar_tac
    have hsl : s.val.length = out.val.length - start.val := by rw [hs, List.length_drop]
    step with (slice_range_to_mut s i1 (by scalar_tac)) as ⟨o, back1, ho, hback1⟩
    have holen' : o.val.length = d.val + len.val + 24 := by
      rw [ho, List.slice_length]
      scalar_tac
    have hoel' : ∀ k, k < d.val + len.val + 24 → o.val[k]! = out.val[n.val - d.val + k]! := by
      intro k hk
      rw [ho, List.getElem!_slice _ _ _ _ ⟨by scalar_tac, by scalar_tac⟩, Nat.zero_add, hs,
        List.getElem!_drop, hstart]
    -- the two words of the first sixteen bytes
    step with (load8a_correct o 0#usize (by scalar_tac)) as ⟨w0, hw0⟩
    step with (load8a_correct o 8#usize (by scalar_tac)) as ⟨w1, hw1⟩
    have hw0' : w0.val = le [(o.val[0]!).val, (o.val[1]!).val, (o.val[2]!).val, (o.val[3]!).val,
        (o.val[4]!).val, (o.val[5]!).val, (o.val[6]!).val, (o.val[7]!).val] := by simpa using hw0
    have hw1' : w1.val = le [(o.val[8]!).val, (o.val[9]!).val, (o.val[10]!).val, (o.val[11]!).val,
        (o.val[12]!).val, (o.val[13]!).val, (o.val[14]!).val, (o.val[15]!).val] := by simpa using hw1
    clear hw0 hw1
    -- the finish from the first stored chunk, given the second chunk's word
    have htail (w2 : U64) (o1 : Aeneas.Std.Slice U8) (ho1 : Stored o.val o1.val d.val w0.val)
        (hw2' : w2.val = le [(o1.val[8]!).val, (o1.val[9]!).val, (o1.val[10]!).val, (o1.val[11]!).val,
          (o1.val[12]!).val, (o1.val[13]!).val, (o1.val[14]!).val, (o1.val[15]!).val] ∨
          (len.val ≤ d.val ∧ len.val ≤ 16 ∧ w2 = w1)) :
        (do
          let i2 ← d + 8#usize
          let o2 ← store8w o1 i2 w2
          if len > 16#usize
          then
            let o3 ← copy_tail o2 d len
            let s1 := back1 o3
            ok (back s1)
          else let s1 := back1 o2
               ok (back s1)) ⦃ v => v.val.length = out.val.length ∧
            copy_spec (out.val.take n.val) d.val len.val (v.val.take (n.val + len.val)) ⦄ := by
      have hl1 := ho1.1
      have hc8 : SCopied o.val o1.val d.val 8 := by
        apply scopied_chunk o.val o.val o1.val d.val 0 w0.val hd8 (by omega) (scopied_zero _ _)
        · simpa using hw0'
        · simpa using ho1
      step as ⟨i4, hi4⟩
      all_goals try scalar_tac
      step with (store8w_correct o1 i4 w2 (by omega)) as ⟨o2, ho2⟩
      have ho2' : Stored o1.val o2.val (d.val + 8) w2.val := by
        rw [hi4] at ho2
        exact ho2
      have hcmin : SCopied o.val o2.val d.val (min len.val 16) := by
        rcases hw2' with hw2' | ⟨hlen_d, hlen16, hw2eq⟩
        · have hc16 : SCopied o.val o2.val d.val 16 := by
            apply scopied_chunk o.val o1.val o2.val d.val 8 w2.val hd8 (by omega) hc8
            · simpa using hw2'
            · exact ho2'
          exact scopied_mono _ _ _ _ _ hc16 (Nat.min_le_right _ _)
        · rw [Nat.min_eq_left hlen16]
          rw [hw2eq] at ho2'
          exact scopied_short_nonoverlap o.val o1.val o2.val d.val len.val w0.val w1.val
            hd8 hlen16 hlen_d (by omega) hw0' hw1' ho1 ho2'
      clear ho2 ho2'
      -- the finish from the window with the whole copy done
      have hfin (o3 : Aeneas.Std.Slice U8) (ho3 : SCopied o.val o3.val d.val len.val) :
          (back (back1 o3)).val.length = out.val.length ∧
            copy_spec (out.val.take n.val) d.val len.val
              ((back (back1 o3)).val.take (n.val + len.val)) := by
        apply hfinish
        have hol3 : o3.val.length = d.val + len.val + 24 := ho3.1.trans holen'
        have hw := window_back out.val o3.val start.val (by scalar_tac) (by rw [hol3]; scalar_tac)
        rw [hback, hback1, hs, hstart]
        rw [hstart] at hw
        exact scopied_copied' out.val o.val o3.val _ n.val d.val len.val hdn hb holen' hoel' ho3
          hw.1 hw.2.1 hw.2.2
      split
      · -- longer than sixteen: the remaining chunks by copy_tail
        have hlen16 : 16 ≤ len.val := by scalar_tac
        unfold copy_tail
        step with (schunk_loop o.val d len o2 16#usize hd8 (by omega)
          (by unfold SChunkInv; simpa [Nat.min_eq_right hlen16] using hcmin)) as ⟨o3, ho3⟩
        exact hfin o3 ho3
      · -- at most sixteen: the two chunks already cover the copy
        rename_i hlen
        have hlen' : len.val ≤ 16 := by
          by_contra hc
          apply hlen
          scalar_tac
        show (ok (back (back1 o2)) : Result (alloc.vec.Vec U8)) ⦃ v => v.val.length = out.val.length ∧
          copy_spec (out.val.take n.val) d.val len.val (v.val.take (n.val + len.val)) ⦄
        rw [WP.spec_ok]
        exact hfin o2 (by simpa only [Nat.min_eq_left hlen'] using hcmin)
    split
    · -- The copy reaches the first store, so distances below sixteen need repair.
      rename_i hlen_d
      split
      · -- below sixteen: the second chunk mixed from the two words
        rename_i hd16
        have hd16' : d.val < 16 := by scalar_tac
        step as ⟨i2, hi2⟩
        all_goals try scalar_tac
        step as ⟨s1, hs1⟩
        all_goals try scalar_tac
        have hs1' : s1.val = 8 * (d.val - 8) := by rw [hs1, hi2]
        step as ⟨i3, hi3⟩
        all_goals try scalar_tac
        have hi3' : i3.val = 2 ^ (8 * (d.val - 8)) := by
          rw [hi3, Nat.shiftLeft_eq, u64_size', hs1']
          simp only [Nat.one_mul]
          apply Nat.mod_eq_of_lt
          exact Nat.pow_lt_pow_right (by norm_num) (by omega)
        step as ⟨i4, hi4⟩
        all_goals try (rw [hi3']; positivity)
        step as ⟨i5, hi5⟩
        all_goals try scalar_tac
        have hi5' : i5.val = (w0.val * 2 ^ (8 * (d.val - 8))) % 2 ^ 64 := by
          rw [hi5, Nat.shiftLeft_eq, u64_size', hs1']
        have hlt : i4.val + i5.val < 2 ^ 64 := by
          rw [hi4, hi5', hi3']
          exact mix_lt w0.val w1.val d.val hd8 hd16'
        step as ⟨w2, hw2⟩
        all_goals try scalar_tac
        step with (store8w_correct o d w0 (by omega)) as ⟨o1, ho1⟩
        apply htail w2 o1 ho1
        apply Or.inl
        rw [hw2, hi4, hi3', hi5']
        exact mix_stored o.val o1.val d.val w0.val w1.val hd8 hd16' (by omega) hw0' hw1' ho1
      · -- sixteen or more: the second chunk is the word from 8
        rename_i hd16
        have hd16' : 16 ≤ d.val := by scalar_tac
        step with (store8w_correct o d w0 (by omega)) as ⟨o1, ho1⟩
        apply htail w1 o1 ho1
        apply Or.inl
        rw [hw1']
        exact (keep_bytes_16 o.val o1.val d.val w0.val hd16' (by omega) ho1).symm
    · -- Source bytes required by this copy precede the first store.
      rename_i hlen_d
      have hlen_d' : len.val ≤ d.val := by scalar_tac
      step with (store8w_correct o d w0 (by omega)) as ⟨o1, ho1⟩
      apply htail w1 o1 ho1
      by_cases hd16 : 16 ≤ d.val
      · apply Or.inl
        rw [hw1']
        exact (keep_bytes_16 o.val o1.val d.val w0.val hd16 (by omega) ho1).symm
      · exact Or.inr ⟨hlen_d', by omega, rfl⟩
  · split
    · -- a run of one byte
      step*
      all_goals try scalar_tac
      have hn : 1 ≤ n.val := by scalar_tac
      have hi : i.val = n.val - 1 := by scalar_tac
      have he : i1 = out.val[n.val - 1]! := by
        rw [← hi, getElem!_pos _ _ (by scalar_tac)]; exact i1_post
      have hw' : w.val = i1.val * 72340172838076673 := by
        rw [w_post, i2_post, cast_byte64]
      apply WP.spec_mono (fill_loop out.val n len i1 w out 0#usize hw' hb
        (by unfold FillInv; simpa using filled_zero out.val n.val i1))
      intro v hv
      apply hfinish
      have hd1 : d.val = 1 := by scalar_tac
      rw [hd1]
      apply filled_copied out.val v.val n.val len.val hn
      rw [← he]
      exact hv
    · -- short distances, byte by byte
      apply WP.spec_mono (byte_loop out.val n d len out 0#usize hd hdn hb
        (by unfold ChunkInv; simpa using copied_zero out.val n.val d.val))
      intro v hv
      exact hfinish v hv

end Gzip.Proofs.Decode.CopyImpl
