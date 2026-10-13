import Gzip.Proofs.Decode.Parsing

open Aeneas Std
open Gzip.Spec Gzip.Proofs.Decode.Decoding Gzip.Proofs.Decode.Huffman Gzip.Proofs.Decode.Parsing

namespace Gzip.Proofs.Decode.RoundTrip

theorem byte_bound (ch : U8) : (ch.val : ℤ) < 256 := by scalar_tac

theorem code_bounds (s : List U8) (i n v : ℤ) (hn : 0 < n)
    (h : code_spec s i n v) : 0 ≤ i ∧ i + n ≤ 8 * (s.length : ℤ) := by
  generalize hm : n.toNat = m
  induction m using Nat.strong_induction_on generalizing n v with
  | h m ih =>
    rw [code_spec] at h
    obtain ⟨v', hv, b, hb, _⟩ := (h.2 (by omega)).2 (by omega)
    have hbb := hb.2.1
    by_cases h1 : n = 1
    · omega
    · have hi := ih (n - 1).toNat (hm ▸ int_step_decreases n (by omega) (by omega))
        (n - 1) v' (by omega) hv rfl
      omega

theorem symbol_bounds (s lit : List U8) (i sym : ℤ) (h : symbol_spec s i lit sym) :
    i < i + (lit[sym.toNat]!).val ∧ i + (lit[sym.toNat]!).val ≤ 8 * (s.length : ℤ) := by
  obtain ⟨_, _, hl, c, _, hc⟩ := h
  have hb := code_bounds s i _ c (by omega) hc
  omega

theorem field_end_bound (s : List U8) (i n v : ℤ) (hi : i ≤ 8 * (s.length : ℤ))
    (h : field_spec s i n v) : i + n ≤ 8 * (s.length : ℤ) := by
  generalize hm : n.toNat = m
  induction m using Nat.strong_induction_on generalizing i n v with
  | h m ih =>
    rw [field_spec] at h
    have hp := h.1
    by_cases hz : n = 0
    · simpa [hz] using hi
    · obtain ⟨b, hb, hrest⟩ := (h.2 hp).2 hz
      obtain ⟨v', hv', _⟩ := hrest hb
      have hb := hb.2.1
      have := ih (n - 1).toNat (hm ▸ int_step_decreases n hp hz) (i + 1) (n - 1) v'
        (by omega) hv' rfl
      omega

theorem fixedlit_end_length (lit : List U8) (h : fixedlit_spec lit) :
    (lit[256]!).val = 7 := by
  obtain ⟨n, hn, he⟩ := h.2.2 256 (by omega) (by omega)
  have hn' : n = 7 := by simpa [fixedlen_spec, fixedlen_pre] using hn
  have he' : (7 : ℤ) = (lit[256]!).val := by simpa [hn'] using he
  omega

theorem fixeddist_exists : fixeddist_spec (List.replicate 32 5#u8) := by
  norm_num [fixeddist_spec, fixeddist_pre]

theorem take_get (s : List U8) (n k : Nat) (h : k < n) : (s.take n)[k]! = s[k]! := by
  simp [getElem!_def, List.getElem?_take, h]

theorem append_take (data : List U8) (p : ℤ) (hp : 0 ≤ p) (hb : p < data.length) :
    append_spec (data.take p.toNat) (data[p.toNat]!).val (data.take (p + 1).toNat) := by
  have hpn : p.toNat ≤ data.length := by omega
  have hpn' : (p + 1).toNat ≤ data.length := by omega
  have hlen : (data.take p.toNat).length = p.toNat := List.length_take_of_le hpn
  refine ⟨trivial, ?_, ?_, ?_⟩
  · rw [hlen, List.length_take_of_le hpn']; omega
  · simp only [List.drop_zero, Int.toNat_natCast, hlen, List.take_take]
    rw [Nat.min_eq_left (by omega)]
  · simp only [Int.toNat_natCast, hlen]
    rw [take_get data (p + 1).toNat p.toNat (by omega)]

end Gzip.Proofs.Decode.RoundTrip
