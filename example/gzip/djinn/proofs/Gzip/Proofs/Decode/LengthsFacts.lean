import Gzip.Proofs.Decode.RunImpl

open Aeneas Std Result
open Gzip.Spec Gzip.Proofs.Decode.RunImpl Gzip.Proofs.Decode.ReaderImpl
open Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.RoundTrip

namespace Gzip.Proofs.Decode.LengthsFacts

theorem run_unique (s cl prev : List U8) (i : ℤ) (v v' : U8) (n j n' j' : ℤ)
    (h : RunSpec s cl prev i v n j) (h' : RunSpec s cl prev i v' n' j') :
    v = v' ∧ n = n' ∧ j = j' := by
  obtain ⟨sym, a, hs, ha, hr⟩ := h
  obtain ⟨sym', a', hs', ha', hr'⟩ := h'
  have he := Huffman.symbol_unique _ _ _ _ _ hs hs'
  rw [← he] at ha' hr'
  have he' : a' = a := ha'.trans ha.symm
  rw [he'] at hr'
  unfold RunKind at hr hr'
  split_ifs at hr hr' with h16 hrep h17
  · exact ⟨by apply UScalar.eq_of_val_eq; omega, by omega, by omega⟩
  · obtain ⟨_, hv, w, hw, hn, hj⟩ := hr
    obtain ⟨_, hv', w', hw', hn', hj'⟩ := hr'
    have hew := Decoding.field_unique _ _ _ _ _ hw hw'
    exact ⟨hv.trans hv'.symm, by omega, by omega⟩
  · obtain ⟨hv, w, hw, hn, hj⟩ := hr
    obtain ⟨hv', w', hw', hn', hj'⟩ := hr'
    have hew := Decoding.field_unique _ _ _ _ _ hw hw'
    exact ⟨by apply UScalar.eq_of_val_eq; omega, by omega, by omega⟩
  · obtain ⟨_, hv, w, hw, hn, hj⟩ := hr
    obtain ⟨_, hv', w', hw', hn', hj'⟩ := hr'
    have hew := Decoding.field_unique _ _ _ _ _ hw hw'
    exact ⟨by apply UScalar.eq_of_val_eq; omega, by omega, by omega⟩

theorem prefix_get (all prev : List U8) (h : all.take prev.length = prev) (k : Nat)
    (hk : k < prev.length) : all[k]! = prev[k]! := by
  have he := congrArg (fun l : List U8 => l[k]!) h
  rwa [take_get all prev.length k hk] at he

theorem prefix_replicate (all prev : List U8) (value : U8) (n : Nat)
    (hpre : all.take prev.length = prev) (hbound : prev.length + n ≤ all.length)
    (hvals : ∀ k, prev.length ≤ k → k < prev.length + n → all[k]! = value) :
    all.take (prev.length + n) = prev ++ List.replicate n value := by
  apply list_eq
  · simp only [List.length_take, Nat.min_eq_left hbound, List.length_append, List.length_replicate]
  · intro k hk
    have hk' : k < prev.length + n := by simp only [List.length_take, Nat.min_eq_left hbound] at hk; exact hk
    rw [take_get all (prev.length + n) k hk']
    by_cases hp : k < prev.length
    · rw [List.getElem!_append_left prev _ k hp]
      exact prefix_get all prev hpre k hp
    · rw [List.getElem!_append_right prev _ k (by omega), List.getElem!_replicate value (by omega)]
      exact hvals k (by omega) hk'

theorem lengths_unfold (s cl prev all : List U8) (i j : ℤ)
    (hlt : prev.length < all.length) (hpre : all.take prev.length = prev) :
    lengths_spec s i cl prev.length all j ↔ ∃ value n a,
      RunSpec s cl prev i value n a ∧ 0 < n ∧ (prev.length : ℤ) + n ≤ all.length ∧
      (∀ k : ℤ, prev.length ≤ k → k < (prev.length : ℤ) + n → all[k.toNat]! = value) ∧
      lengths_spec s a cl ((prev.length : ℤ) + n) all j := by
  have hp : lengths_pre s i cl prev.length all := ⟨by omega, by omega⟩
  have hnend : (prev.length : ℤ) ≠ all.length := by omega
  constructor
  · intro h
    rw [lengths_spec] at h
    have hr := (h.2 hp).2 hnend
    simp only [guard_and] at hr
    obtain ⟨sym, a, n, hs, ha, hr⟩ := hr
    by_cases h16 : sym < 16
    · obtain ⟨hn, hvals, hrec⟩ := hr.1 h16
      have hval : ((all[prev.length]!).val : ℤ) = sym := by
        simpa only [Int.toNat_natCast] using hvals prev.length (by omega) (by omega)
      refine ⟨all[prev.length]!, n, a, ⟨sym, a, hs, ha, ?_⟩, by omega, by omega, ?_, hrec⟩
      · simp only [RunKind, if_pos h16]
        exact ⟨hval, hn, trivial⟩
      · intro k hk hk'
        apply UScalar.eq_of_val_eq
        have hv := hvals k hk hk'
        omega
    have hr := hr.2 h16
    by_cases hrep : sym = 16
    · obtain ⟨hp1, ⟨v, hv, hn⟩, hnb, hvals, hrec⟩ := hr.1 hrep
      have hlast : all[((prev.length : ℤ) - 1).toNat]! = prev[prev.length - 1]! := by
        have he : ((prev.length : ℤ) - 1).toNat = prev.length - 1 := by omega
        rw [he]
        exact prefix_get all prev hpre _ (by omega)
      refine ⟨prev[prev.length - 1]!, n, a + 2, ⟨sym, a, hs, ha, ?_⟩, by omega, hnb.2, ?_, hrec⟩
      · simp only [RunKind, if_neg h16, if_pos hrep]
        exact ⟨by omega, trivial, v, hv, hn, trivial⟩
      · intro k hk hk'
        exact (hvals k hk hk').trans hlast
    have hr := hr.2 hrep
    by_cases h17 : sym = 17
    · obtain ⟨⟨v, hv, hn⟩, hnb, hvals, hrec⟩ := hr.1 h17
      refine ⟨0#u8, n, a + 3, ⟨sym, a, hs, ha, ?_⟩, by omega, hnb.2, ?_, hrec⟩
      · simp only [RunKind, if_neg h16, if_neg hrep, if_pos h17]
        exact ⟨rfl, v, hv, hn, trivial⟩
      · intro k hk hk'
        apply UScalar.eq_of_val_eq
        have hv := hvals k hk hk'
        change (all[k.toNat]!).val = 0
        omega
    · obtain ⟨h18, ⟨v, hv, hn⟩, hnb, hvals, hrec⟩ := hr.2 h17
      refine ⟨0#u8, n, a + 7, ⟨sym, a, hs, ha, ?_⟩, by omega, hnb.2, ?_, hrec⟩
      · simp only [RunKind, if_neg h16, if_neg hrep, if_neg h17]
        exact ⟨h18, rfl, v, hv, hn, trivial⟩
      · intro k hk hk'
        apply UScalar.eq_of_val_eq
        have hv := hvals k hk hk'
        change (all[k.toNat]!).val = 0
        omega
  · rintro ⟨value, n, a', ⟨sym, a, hs, ha, hr⟩, hn0, hn, hvals, hrec⟩
    rw [lengths_spec]
    refine ⟨hp, fun _ => ⟨fun he => (hnend he).elim, fun _ => ?_⟩⟩
    simp only [guard_and]
    refine ⟨sym, a, n, hs, ha, ?_⟩
    unfold RunKind at hr
    by_cases h16 : sym < 16
    · simp only [if_pos h16] at hr
      obtain ⟨hval, hn1, ha'⟩ := hr
      rw [ha'] at hrec
      refine ⟨fun _ => ⟨hn1, ?_, hrec⟩, fun hn => (hn h16).elim⟩
      intro k hk hk'
      rw [hvals k hk hk']
      exact hval
    refine ⟨fun hy => (h16 hy).elim, fun _ => ?_⟩
    simp only [if_neg h16] at hr
    by_cases hrep : sym = 16
    · simp only [if_pos hrep] at hr
      obtain ⟨hp1, hval, v, hv, hnv, ha'⟩ := hr
      rw [ha'] at hrec
      refine ⟨fun _ => ⟨by omega, ⟨v, hv, hnv⟩, ⟨by omega, hn⟩, ?_, hrec⟩, fun hy => (hy hrep).elim⟩
      intro k hk hk'
      rw [hvals k hk hk', hval]
      have hlast := prefix_get all prev hpre (prev.length - 1) (by omega)
      have he : ((prev.length : ℤ) - 1).toNat = prev.length - 1 := by omega
      rw [he]
      exact hlast.symm
    refine ⟨fun hy => (hrep hy).elim, fun _ => ?_⟩
    simp only [if_neg hrep] at hr
    by_cases h17 : sym = 17
    · simp only [if_pos h17] at hr
      obtain ⟨hval, v, hv, hnv, ha'⟩ := hr
      rw [ha'] at hrec
      refine ⟨fun _ => ⟨⟨v, hv, hnv⟩, ⟨by omega, hn⟩, ?_, hrec⟩, fun hy => (hy h17).elim⟩
      intro k hk hk'
      rw [hvals k hk hk', hval]
      rfl
    · simp only [if_neg h17] at hr
      obtain ⟨h18, hval, v, hv, hnv, ha'⟩ := hr
      rw [ha'] at hrec
      refine ⟨fun hy => (h17 hy).elim, fun _ => ⟨h18, ⟨v, hv, hnv⟩, ⟨by omega, hn⟩, ?_, hrec⟩⟩
      intro k hk hk'
      rw [hvals k hk hk', hval]
      rfl

theorem lengths_step_iff (s cl prev all : List U8) (i a j : ℤ) (value : U8) (n : Nat)
    (hlt : prev.length < all.length) (hpre : all.take prev.length = prev)
    (hn : 0 < n) (hr : RunSpec s cl prev i value n a) :
    lengths_spec s i cl prev.length all j ↔
      prev.length + n ≤ all.length ∧ all.take (prev.length + n) = prev ++ List.replicate n value ∧
      lengths_spec s a cl (prev.length + n : Nat) all j := by
  rw [lengths_unfold s cl prev all i j hlt hpre]
  constructor
  · rintro ⟨v', n', a', hr', _, hb, hv, hrec⟩
    obtain ⟨he, hn', ha'⟩ := run_unique _ _ _ _ _ _ _ _ _ _ hr hr'
    simp only [← he, ← hn', ← ha'] at hv hrec hb
    refine ⟨by omega, ?_, ?_⟩
    · apply prefix_replicate all prev value n hpre (by omega)
      intro k hk hk'
      simpa only [Int.toNat_natCast] using hv k (by omega) (by omega)
    · simpa only [Nat.cast_add] using hrec
  · rintro ⟨hb, hp, hrec⟩
    refine ⟨value, n, a, hr, by omega, by omega, ?_, ?_⟩
    · intro k hk hk'
      have hp' : all.take (prev ++ List.replicate n value).length = prev ++ List.replicate n value := by
        simpa only [List.length_append, List.length_replicate] using hp
      rw [prefix_get all (prev ++ List.replicate n value) hp' k.toNat (by
        simp only [List.length_append, List.length_replicate]; omega)]
      rw [List.getElem!_append_right prev _ k.toNat (by omega), List.getElem!_replicate value (by omega)]
    · simpa only [Nat.cast_add] using hrec

end Gzip.Proofs.Decode.LengthsFacts
