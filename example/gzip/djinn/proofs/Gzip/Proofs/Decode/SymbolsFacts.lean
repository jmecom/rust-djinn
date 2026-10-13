import Gzip.Proofs.Decode.MatchImpl

open Aeneas Std Result
open Gzip.Spec Gzip.Proofs.Decode.MatchImpl Gzip.Proofs.Decode.ReaderImpl
open Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.CopyImpl

namespace Gzip.Proofs.Decode.SymbolsFacts

theorem symbols_unfold (s lit dist prev out : List U8) (i j : ℤ) :
    symbols_spec s i lit dist prev out j ↔ ∃ sym a,
      symbol_spec s i lit sym ∧ a = i + (lit[sym.toNat]!).val ∧ (i < a ∧ a ≤ 8 * s.length) ∧
      (if sym = 256 then out = prev ∧ j = a
       else if sym < 256 then ∃ p, append_spec prev sym p ∧ symbols_spec s a lit dist p out j
       else ∃ len d c, MatchSpec s a dist (sym - 257) len d c ∧ (a < c ∧ c ≤ 8 * s.length) ∧
         ∃ p, copy_spec prev d len p ∧ symbols_spec s c lit dist p out j) := by
  rw [symbols_spec]
  simp only [symbols_pre, true_and, true_implies, guard_and]
  constructor
  · rintro ⟨sym, a, hs, ha, hab, hrest⟩
    refine ⟨sym, a, hs, ha, hab, ?_⟩
    split_ifs with he hl
    · exact hrest.1 he
    · exact (hrest.2 he).1 hl
    · obtain ⟨len, b, dc, d, c, hlen, hb, hdc, hd, hc, hcb, p, hp, hrec⟩ := (hrest.2 he).2 hl
      exact ⟨len, d, c, ⟨b, dc, hlen, hb, hdc, hd, hc⟩, hcb, p, hp, hrec⟩
  · rintro ⟨sym, a, hs, ha, hab, hrest⟩
    refine ⟨sym, a, hs, ha, hab, ?_⟩
    by_cases he : sym = 256
    · simp only [he, if_true] at hrest
      exact ⟨fun _ => hrest, fun hn => (hn he).elim⟩
    refine ⟨fun hy => (he hy).elim, fun _ => ?_⟩
    by_cases hl : sym < 256
    · simp only [if_neg he, if_pos hl] at hrest
      exact ⟨fun _ => hrest, fun hn => (hn hl).elim⟩
    refine ⟨fun hy => (hl hy).elim, fun _ => ?_⟩
    simp only [if_neg he, if_neg hl] at hrest
    obtain ⟨len, d, c, ⟨b, dc, hlen, hb, hdc, hd, hc⟩, hcb, p, hp, hrec⟩ := hrest
    exact ⟨len, b, dc, d, c, hlen, hb, hdc, hd, hc, hcb, p, hp, hrec⟩

theorem symbols_length (s lit dist prev out : List U8) (i j : ℤ)
    (h : symbols_spec s i lit dist prev out j) : prev.length ≤ out.length := by
  generalize hm : (8 * (s.length : ℤ) - i).toNat = m
  induction m using Nat.strong_induction_on generalizing i prev with
  | h m ih =>
    obtain ⟨sym, a, hs, ha, hab, hr⟩ := (symbols_unfold _ _ _ _ _ _ _).mp h
    by_cases he : sym = 256
    · simp only [if_pos he] at hr
      rw [hr.1]
    by_cases hl : sym < 256
    · simp only [if_neg he, if_pos hl] at hr
      obtain ⟨p, hp, hrec⟩ := hr
      have hv := ih _ (hm ▸ bit_measure_decreases s i a hab.1 hab.2) p a hrec rfl
      have hlen := hp.2.1
      omega
    · simp only [if_neg he, if_neg hl] at hr
      obtain ⟨len, d, c, _, hcb, p, hp, hrec⟩ := hr
      have hv := ih _ (hm ▸ bit_measure_decreases s i c (_root_.lt_trans hab.1 hcb.1) hcb.2) p c hrec rfl
      have hlen := copy_length prev p d len hp
      omega

theorem append_byte (prev : List U8) (ch : U8) : append_spec prev ch.val (prev ++ [ch]) := by
  refine ⟨trivial, by simp, by simp, ?_⟩
  simp only [Int.toNat_natCast, List.getElem!_append_right prev _ prev.length (Nat.le_refl _),
    Nat.sub_self, List.getElem!_cons_zero]

theorem match_unique (s dist : List U8) (i lc len d j len' d' j' : ℤ)
    (h : MatchSpec s i dist lc len d j) (h' : MatchSpec s i dist lc len' d' j') :
    len = len' ∧ d = d' ∧ j = j' := by
  obtain ⟨b, dc, ⟨lb, hlb, le, hle, v, hv, hlen⟩, ⟨le1, hle1, hb⟩, hdc,
    ⟨db, hdb, de, hde, w, hw, hd⟩, ⟨de1, hde1, hj⟩⟩ := h
  obtain ⟨b', dc', ⟨lb', hlb', le', hle', v', hv', hlen'⟩, ⟨le1', hle1', hb'⟩, hdc',
    ⟨db', hdb', de', hde', w', hw', hd'⟩, ⟨de1', hde1', hj'⟩⟩ := h'
  have helb := lbase_unique _ _ _ hlb hlb'
  have hele := lextra_unique _ _ _ hle hle'
  rw [← hele] at hv'
  have hev := Decoding.field_unique _ _ _ _ _ hv hv'
  have hele1 := lextra_unique _ _ _ hle1 hle1'
  have heb : b = b' := by omega
  rw [← heb] at hdc' hw' hj'
  have hedc := Huffman.symbol_unique _ _ _ _ _ hdc hdc'
  rw [← hedc] at hdb' hde' hw' hde1' hj'
  have hedb := dbase_unique _ _ _ hdb hdb'
  have hede := dextra_unique _ _ _ hde hde'
  rw [← hede] at hw'
  have hew := Decoding.field_unique _ _ _ _ _ hw hw'
  have hede1 := dextra_unique _ _ _ hde1 hde1'
  omega

theorem symbols_at (s lit dist prev out : List U8) (i j sym a : ℤ)
    (hs : symbol_spec s i lit sym) (ha : a = i + (lit[sym.toNat]!).val) :
    symbols_spec s i lit dist prev out j ↔
      (if sym = 256 then out = prev ∧ j = a
       else if sym < 256 then ∃ p, append_spec prev sym p ∧ symbols_spec s a lit dist p out j
       else ∃ len d c, MatchSpec s a dist (sym - 257) len d c ∧ (a < c ∧ c ≤ 8 * s.length) ∧
         ∃ p, copy_spec prev d len p ∧ symbols_spec s c lit dist p out j) := by
  rw [symbols_unfold]
  constructor
  · rintro ⟨sym', a', hs', ha', _, hrest⟩
    have he := Huffman.symbol_unique _ _ _ _ _ hs hs'
    rw [← he] at ha' hrest
    have he' : a' = a := ha'.trans ha.symm
    rwa [he'] at hrest
  · intro hrest
    refine ⟨sym, a, hs, ha, ?_, hrest⟩
    rw [ha]
    exact RoundTrip.symbol_bounds _ _ _ _ hs

theorem symbols_literal_iff (s lit dist prev mid out : List U8) (i a j sym : ℤ)
    (hs : symbol_spec s i lit sym) (ha : a = i + (lit[sym.toNat]!).val)
    (he : sym ≠ 256) (hl : sym < 256) (hp : append_spec prev sym mid) :
    symbols_spec s i lit dist prev out j ↔ symbols_spec s a lit dist mid out j := by
  rw [symbols_at s lit dist prev out i j sym a hs ha, if_neg he, if_pos hl]
  constructor
  · rintro ⟨p, hp', hrec⟩
    have heq := append_unique _ _ _ _ hp hp'
    rwa [← heq] at hrec
  · intro hrec; exact ⟨mid, hp, hrec⟩

theorem symbols_match_iff (s lit dist prev mid out : List U8) (i a c j sym len d : ℤ)
    (hs : symbol_spec s i lit sym) (ha : a = i + (lit[sym.toNat]!).val)
    (he : sym ≠ 256) (hl : ¬ sym < 256) (hm : MatchSpec s a dist (sym - 257) len d c)
    (hcb : a < c ∧ c ≤ 8 * s.length) (hp : copy_spec prev d len mid) :
    symbols_spec s i lit dist prev out j ↔ symbols_spec s c lit dist mid out j := by
  rw [symbols_at s lit dist prev out i j sym a hs ha, if_neg he, if_neg hl]
  constructor
  · rintro ⟨len', d', c', hm', _, p, hp', hrec⟩
    obtain ⟨hlen, hd, hc⟩ := match_unique _ _ _ _ _ _ _ _ _ _ hm hm'
    rw [← hlen, ← hd] at hp'
    have heq := copy_unique _ _ _ _ _ hp hp'
    rwa [← heq, ← hc] at hrec
  · intro hrec; exact ⟨len, d, c, hm, hcb, mid, hp, hrec⟩

end Gzip.Proofs.Decode.SymbolsFacts
