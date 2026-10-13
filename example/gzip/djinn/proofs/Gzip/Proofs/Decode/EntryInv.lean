import Gzip.Proofs.Decode.WindowImpl

/-! # The table entry the decoding loop carries

The loop keeps the literal/length table's entry at the window's position, looked up from the
window before it is refilled. A refilled window holds all 64 of its bits from the stream, so the
entry is right as long as at most 53 bits were taken since; when no refill was possible the
entry may be stale, but then the window is too short for the fast path. -/

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.WindowFacts Gzip.Proofs.Decode.WindowImpl

namespace Gzip.Proofs.Decode.EntryInv

/-- Two numbers whose first eleven bits are the stream's bits at the same position agree on
their low eleven bits. -/
theorem low_bits_eq (s : List U8) (q w nq : Nat) (P : ℤ) (hq : Window s q nq P) (h11 : 11 ≤ nq)
    (hw : ∀ k : Nat, k < 64 → bit_spec s (P + k) ((w / 2 ^ k % 2 : Nat) : ℤ)) :
    q % 2048 = w % 2048 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [show (2048 : Nat) = 2 ^ 11 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hk : k < 11
  · have hqb := window_bits s q nq P hq k (by omega) (by omega)
    have hwb := hw k (by omega)
    have heq := Decoding.bit_unique _ _ _ _ hqb hwb
    have heq' : q / 2 ^ k % 2 = w / 2 ^ k % 2 := by exact_mod_cast heq
    rw [bit_eq_toNat, bit_eq_toNat] at heq'
    have hb : q.testBit k = w.testBit k := by
      cases hq' : q.testBit k <;> cases hw' : w.testBit k <;> simp_all
    simp [hk, hb]
  · simp [hk]

/-- The loop's knowledge about its entry `e`: some `nv ≥ nbits` bits of the window are the
stream's (all 64 when the last refill was possible), and `e` is the entry at the window's
position whenever eleven of them are. -/
def EInv (s : Aeneas.Std.Slice U8) (table : Array U32 2048#usize) (buf : U64) (nbits : U32)
    (cpos : Usize) (e : U32) : Prop :=
  ∃ nv : Nat, nbits.val ≤ nv ∧ nv ≤ 64 ∧ Window s.val buf.val nv (wpos cpos nbits) ∧
    (cpos.val + 8 ≤ s.val.length → nv = 64) ∧ (11 ≤ nv → e = table.val[buf.val % 2048]!)

theorem einv_entry (s : Aeneas.Std.Slice U8) (table : Array U32 2048#usize) (buf : U64) (nbits : U32)
    (cpos : Usize) (e : U32) (h : EInv s table buf nbits cpos e) (lo : U32) (hlo : 11 ≤ lo.val) :
    lo.val ≤ nbits.val → e = table.val[buf.val % 2048]! := by
  intro hle
  obtain ⟨nv, hn, _, _, _, he⟩ := h
  exact he (by omega)

/-- The window after `c` of the `nv` stream bits of a window were taken. -/
theorem einv_skip (s : Aeneas.Std.Slice U8) (table : Array U32 2048#usize) (buf : U64) (nbits : U32)
    (cpos : Usize) (e : U32) (h : EInv s table buf nbits cpos e) (q : U64) (c : Nat)
    (hq : q.val = buf.val >>> c) (hc : c ≤ nbits.val) :
    ∃ nv : Nat, nbits.val - c ≤ nv ∧ nv ≤ 64 ∧ Window s.val q.val nv (wpos cpos nbits + c) ∧
      (cpos.val + 8 ≤ s.val.length → nv = 64 - c) := by
  obtain ⟨nv, hn, h64, hw, hfull, _⟩ := h
  refine ⟨nv - c, by omega, by omega, ?_, fun hle => by rw [hfull hle]⟩
  rw [hq]
  exact window_skip s.val buf.val nv c (wpos cpos nbits) hw (by scalar_tac) h64 (by omega)

/-- The entry invariant after a refill of a window `q` of which `nvq` bits are the stream's,
with the entry looked up from `q` before the refill. -/
theorem einv_of_refill (s : Aeneas.Std.Slice U8) (table : Array U32 2048#usize) (q : U64) (nq : U32)
    (cpos : Usize) (w : U64) (nb : U32) (c : Usize) (e : U32) (nvq : Nat)
    (hwin : WInv s w nb c) (hpos : wpos c nb = wpos cpos nq)
    (hno : s.val.length < cpos.val + 8 → w = q ∧ nb = nq ∧ c = cpos)
    (hall : cpos.val + 8 ≤ s.val.length →
      ∀ k : Nat, k < 64 → bit_spec s.val (wpos cpos nq + k) ((w.val / 2 ^ k % 2 : Nat) : ℤ))
    (hq : Window s.val q.val nvq (wpos cpos nq)) (hnq : nq.val ≤ nvq) (h64 : nvq ≤ 64)
    (h11 : cpos.val + 8 ≤ s.val.length → 11 ≤ nvq) (he : e = table.val[q.val % 2048]!) :
    EInv s table w nb c e := by
  by_cases hle : cpos.val + 8 ≤ s.val.length
  · have hall' := hall hle
    refine ⟨64, by have := hwin.2.1; omega, Nat.le_refl _, ?_, fun _ => rfl, fun _ => ?_⟩
    · rw [hpos]
      intro k hk
      exact Or.inl (hall' k hk)
    · rw [he, low_bits_eq s.val q.val w.val nvq (wpos cpos nq) hq (h11 hle) hall']
  · obtain ⟨hwq, hnb, hc⟩ := hno (by omega)
    refine ⟨nvq, by rw [hnb]; exact hnq, h64, ?_, fun h => by rw [hc] at h; exact absurd h hle,
      fun _ => by rw [hwq]; exact he⟩
    rw [hwq, hpos]
    exact hq

/-- The entry invariant with the entry looked up from the refilled window itself. -/
theorem einv_of_lookup (s : Aeneas.Std.Slice U8) (table : Array U32 2048#usize) (q : U64) (nq : U32)
    (cpos : Usize) (w : U64) (nb : U32) (c : Usize) (e : U32)
    (hwin : WInv s w nb c) (hpos : wpos c nb = wpos cpos nq)
    (hno : s.val.length < cpos.val + 8 → w = q ∧ nb = nq ∧ c = cpos)
    (hall : cpos.val + 8 ≤ s.val.length →
      ∀ k : Nat, k < 64 → bit_spec s.val (wpos cpos nq + k) ((w.val / 2 ^ k % 2 : Nat) : ℤ))
    (he : e = table.val[w.val % 2048]!) :
    EInv s table w nb c e := by
  by_cases hle : cpos.val + 8 ≤ s.val.length
  · have hall' := hall hle
    refine ⟨64, by have := hwin.2.1; omega, Nat.le_refl _, ?_, fun _ => rfl, fun _ => he⟩
    rw [hpos]
    intro k hk
    exact Or.inl (hall' k hk)
  · obtain ⟨_, _, hc⟩ := hno (by omega)
    refine ⟨nb.val, Nat.le_refl _, by have := hwin.2.1; omega, hwin.2.2.2,
      fun h => by rw [hc] at h; exact absurd h hle, fun _ => he⟩

/-- `advance`: the entry at the window `rest` (of which `nvq` bits are the stream's) and the
refilled window, with the entry invariant. -/
theorem advance_correct (s : Aeneas.Std.Slice U8) (table : Array U32 2048#usize) (rest : U64)
    (nrest : U32) (cpos : Usize) (nvq : Nat)
    (hwin : WInv s rest nrest cpos) (hq : Window s.val rest.val nvq (wpos cpos nrest))
    (hnq : nrest.val ≤ nvq) (h64 : nvq ≤ 64) (h11 : cpos.val + 8 ≤ s.val.length → 11 ≤ nvq) :
    advance s table rest nrest cpos ⦃ z => WInv s z.2.1 z.2.2.1 z.2.2.2 ∧
      wpos z.2.2.2 z.2.2.1 = wpos cpos nrest ∧ EInv s table z.2.1 z.2.2.1 z.2.2.2 z.1 ⦄ := by
  unfold advance
  step as ⟨i, i_post⟩
  step as ⟨i1, i1_post⟩
  have hi1 : i1.val = rest.val % 2048 := by
    rw [i1_post, UScalar.cast_val_eq, i_post]
    apply Nat.mod_eq_of_lt
    scalar_tac
  clear i1_post
  step as ⟨e, e_post⟩
  have he : e = table.val[rest.val % 2048]! := by
    rw [← hi1, getElem!_pos table.val i1.val (by scalar_tac)]
    exact e_post
  step with (refill_correct s rest nrest cpos hwin) as ⟨w, nb, c, hwin1, hpos1, _, _, hno, hall⟩
  exact ⟨hwin1, hpos1, einv_of_refill s table rest nrest cpos w nb c e nvq hwin1 hpos1 hno hall hq hnq h64 h11 he⟩

end Gzip.Proofs.Decode.EntryInv
