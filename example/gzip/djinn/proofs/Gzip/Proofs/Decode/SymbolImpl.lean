import Gzip.Proofs.Decode.CodewordTable
import Gzip.Proofs.Decode.DecodeTable
import Gzip.Proofs.Decode.PeekImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.BaseImpl Gzip.Proofs.Decode.CodewordImpl
open Gzip.Proofs.Decode.Decoding Gzip.Proofs.Decode.Encoding Gzip.Proofs.Decode.CodewordTable

namespace Gzip.Proofs.Decode.SymbolImpl

def CodePost (s : Aeneas.Std.Slice U8) (r : Reader) (n : U32) (z : Option U32 × Reader) : Prop :=
  Inv s z.2 ∧ match z.1 with
  | none => ∀ v, ¬ code_spec s.val (pos r) n.val v
  | some v => code_spec s.val (pos r) n.val v.val ∧ pos z.2 = pos r + n.val ∧ v.val < 2 ^ n.val

theorem code_bit_at (s : List U8) (i n v k : ℤ) (h : code_spec s i n v)
    (hk : 0 ≤ k) (hkn : k < n) : ∃ b, bit_spec s (i + k) b := by
  generalize hm : n.toNat = m
  induction m using Nat.strong_induction_on generalizing n v with
  | h m ih =>
    rw [code_spec] at h
    obtain ⟨w, hw, b, hb, _⟩ := (h.2 h.1).2 (by omega)
    by_cases he : k = n - 1
    · exact ⟨b, by convert hb using 1 <;> omega⟩
    · apply ih (n - 1).toNat (by omega) (n - 1) w hw (by omega) rfl

def CodeInv (s : Aeneas.Std.Slice U8) (start : Reader) (count : U32)
    (r : Reader) (pfx n : U32) : Prop :=
  Inv s r ∧ n.val ≤ count.val ∧ code_spec s.val (pos start) n.val pfx.val ∧
    pos r = pos start + n.val ∧ pfx.val < 2 ^ n.val

theorem code_body (s : Aeneas.Std.Slice U8) (start : Reader) (count : U32)
    (r : Reader) (pfx n : U32) (hc : count.val ≤ 31)
    (h : CodeInv s start count r pfx n) :
    read_code_loop.body s count r pfx n ⦃ z => match z with
      | .done v => CodePost s start count v
      | .cont (r1, p1, n1) => CodeInv s start count r1 p1 n1 ∧
          count.val - n1.val < count.val - n.val ⦄ := by
  obtain ⟨hr, hn, hp, hpos, hbound⟩ := h
  unfold read_code_loop.body
  step*
  · simp only [BitPost, show o = none by assumption] at o_post
    refine ⟨o_post.1, ?_⟩
    intro v hv
    obtain ⟨b, hb⟩ := code_bit_at s.val (pos start) count.val v n.val hv (by omega) (by scalar_tac)
    apply o_post.2 b
    rwa [hpos]
  · have hpow : 2 ^ n.val ≤ 1073741824 := calc
      _ ≤ 2 ^ 30 := Nat.pow_le_pow_right (by omega) (by scalar_tac)
      _ = _ := by norm_num
    scalar_tac
  · simp only [BitPost, show o = some value by assumption] at o_post
    have hv := bit_range _ _ _ o_post.2.1
    have hpow : 2 ^ n.val ≤ 1073741824 := calc
      _ ≤ 2 ^ 30 := Nat.pow_le_pow_right (by omega) (by scalar_tac)
      _ = _ := by norm_num
    scalar_tac
  · simp only [BitPost, show o = some value by assumption] at o_post
    refine ⟨⟨o_post.1, by scalar_tac, ?_, by scalar_tac, ?_⟩, by scalar_tac⟩
    · rw [code_spec]
      refine ⟨show 0 ≤ (n1.val : ℤ) from by omega, fun _ => ⟨?_, ?_⟩⟩
      · intro hz
        have hnpos : 0 < n1.val := by omega
        omega
      · intro _
        refine ⟨pfx.val, ?_, value.val, ?_, ?_⟩
        · convert hp using 1 <;> omega
        · convert o_post.2.1 using 1 <;> push_cast <;> omega
        · push_cast; omega
    · have hv := bit_range _ _ _ o_post.2.1
      rw [n1_post, pow_succ]
      omega
  · have he : n.val = count.val := by scalar_tac
    exact ⟨hr, by simpa only [he] using hp, by simpa only [he] using hpos,
      by simpa only [he] using hbound⟩

@[step]
theorem read_code_correct (s : Aeneas.Std.Slice U8) (r : Reader) (n : U32)
    (h : Inv s r) (hn : n.val ≤ 31) : read_code s r n ⦃ z => CodePost s r n z ⦄ := by
  unfold read_code read_code_loop
  apply loop.spec_decr_nat (fun (_, _, k) => n.val - k.val)
    (fun (r1, p, k) => CodeInv s r n r1 p k)
  · rintro ⟨r1, p, k⟩ hinv
    apply WP.spec_mono (code_body s r n r1 p k hn hinv)
    intro z hz
    cases z <;> exact hz
  · refine ⟨h, by simp, ?_, by simp, by decide⟩
    change code_spec s.val (pos r) 0 0
    rw [code_spec]
    simp [code_pre]

@[step]
theorem read_code_fast_correct (s : Aeneas.Std.Slice U8) (r : Reader) (n : U32)
    (h : Inv s r) (hn : n.val ≤ 31) : read_code_fast s r n ⦃ z => CodePost s r n z ⦄ := by
  unfold read_code_fast
  step*
  all_goals simp only [PeekImpl.PeekPost, show o = some p by assumption] at o_post
  all_goals try scalar_tac
  simp only [CodePost]
  refine ⟨PeekImpl.skip_inv s r r1 o_post.1 (by assumption) (by assumption), ?_, by assumption, ?_⟩
  · rw [code_post]
    exact PeekFacts.code_of_bits s.val (pos r) p.val n.val (fun k hk => o_post.2.2 k (by scalar_tac))
  · rw [code_post]
    exact PeekFacts.rev_lt p.val n.val

def SymbolPost (s : Aeneas.Std.Slice U8) (r : Reader) (lens : Aeneas.Std.Slice U8)
    (k : Nat) (z : Option U32 × Reader) : Prop :=
  Inv s z.2 ∧ match z.1 with
  | none => ∀ v : ℤ, k ≤ v → ¬ symbol_spec s.val (pos r) lens.val v
  | some v => k ≤ v.val ∧ symbol_spec s.val (pos r) lens.val v.val ∧
      pos z.2 = pos r + (lens.val[v.val]!).val

theorem symbol_advance (s : Aeneas.Std.Slice U8) (r : Reader) (lens : Aeneas.Std.Slice U8)
    (k : Nat) (z : Option U32 × Reader) (hn : ¬ symbol_spec s.val (pos r) lens.val k)
    (h : SymbolPost s r lens (k + 1) z) : SymbolPost s r lens k z := by
  obtain ⟨hinv, hp⟩ := h
  refine ⟨hinv, ?_⟩
  cases hz : z.1 with
  | none =>
    simp only [hz] at hp
    intro v hv hs
    by_cases he : v = k
    · exact hn (he ▸ hs)
    · exact hp v (by omega) hs
  | some v =>
    simp only [hz] at hp
    exact ⟨by omega, hp.2⟩

@[step]
theorem read_symbol_at_correct (s : Aeneas.Std.Slice U8) (r : Reader) (lens : Aeneas.Std.Slice U8)
    (codes : Aeneas.Std.Slice U32) (hlen : codes.val.length = lens.val.length) (htable : Entries lens.val codes.val)
    (k : Usize) (h : Inv s r) (hl : lens.val.length ≤ 320)
    (hb : ∀ j, j < lens.val.length → (lens.val[j]!).val ≤ 15) (hk : k.val ≤ lens.val.length) :
    read_symbol_at s r lens codes k ⦃ z => SymbolPost s r lens k.val z ⦄ := by
  generalize hm : lens.val.length - k.val = m
  induction m using Nat.strong_induction_on generalizing k with
  | h m ih =>
    have ih' (j : Usize) (hj : k.val < j.val) (hjl : j.val ≤ lens.val.length) :
        read_symbol_at s r lens codes j ⦃ z => SymbolPost s r lens j.val z ⦄ :=
      ih (lens.val.length - j.val) (by omega) j hjl rfl
    clear ih
    unfold read_symbol_at
    step*
    · refine ⟨h, ?_⟩
      intro v hv hs
      have hvs := hs.2.1
      scalar_tac
    all_goals
      have hkl : k.val < lens.val.length := by scalar_tac
      have hn' : n.val = (lens.val[k.val]!).val := by
        rw [n_post, cast_byte, i1_post, getElem!_pos lens.val k.val hkl]
    · have hbound := hb k.val hkl
      omega
    · simp only [CodePost, Prod.fst, Prod.snd, show o = none by assumption] at o_post
      apply symbol_advance s r lens k.val z ?_ (by simpa only [i2_post] using z_post)
      intro hs
      obtain ⟨_, _, _, w, _, hw⟩ := hs
      apply o_post.2 w
      simpa only [Int.toNat_natCast, ← hn'] using hw
    · simp only [CodePost, Prod.fst, Prod.snd, show o = some code by assumption] at o_post
      rw [show i2 = code by assumption] at i2_post
      have hc : i3.val = k.val := by
        rw [i3_post, UScalar.cast_val_eq]
        apply Nat.mod_eq_of_lt
        scalar_tac
      refine ⟨o_post.1, by omega, ?_, ?_⟩
      · rw [hc]
        refine ⟨trivial, ⟨by omega, by omega⟩, ?_, code.val, i2_post, ?_⟩
        · simp only [Int.toNat_natCast]
          scalar_tac
        · simpa only [Int.toNat_natCast, ← hn'] using o_post.2.1
      · simp only [Prod.snd]
        rw [hc]
        omega
    · simp only [CodePost, Prod.fst, Prod.snd, show o = some code by assumption] at o_post
      apply symbol_advance s r lens k.val z ?_ (by simpa only [i3_post] using z_post)
      intro hs
      obtain ⟨_, _, _, w, hw, hcode⟩ := hs
      have hw' := codeword_unique _ _ _ _ i2_post hw
      have hcode' : code_spec s.val (pos r) n.val w := by
        simpa only [Int.toNat_natCast, ← hn'] using hcode
      have hc := code_unique _ _ _ _ _ o_post.2.1 hcode'
      have he : i2 = code := by apply UScalar.eq_of_val_eq; omega
      contradiction
    · apply symbol_advance s r lens k.val z ?_ (by simpa only [i2_post] using z_post)
      intro hs
      have hpos := hs.2.2.1
      simp only [Int.toNat_natCast] at hpos
      scalar_tac

end Gzip.Proofs.Decode.SymbolImpl
