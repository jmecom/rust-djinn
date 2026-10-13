/-  Proofs.lean — the implementer's file. Written once by `cargo djinn
    translate`, never overwritten. Replace every `sorry`; add any helper
    lemmas you need (loop invariants, bridging lemmas) in this file. -/
import Aeneas
import Gzip.Spec
import Gzip.Code.Funs
import Gzip.Vocab
import Gzip.Proofs.CrcImpl
import Gzip.Proofs.Encoder
import Gzip.Proofs.Writer
import Gzip.Proofs.Bits
import Gzip.Proofs.Matches
import Gzip.Proofs.Chains
import Gzip.Proofs.Costs
import Gzip.Proofs.Huffman
import Gzip.Proofs.Plans
import Gzip.Proofs.Reverse
import Gzip.Proofs.Dp
import Gzip.Proofs.Passes
import Gzip.Proofs.Greedy
import Gzip.Proofs.Symbols
import Gzip.Proofs.Indices
import Gzip.Proofs.Copies
import Gzip.Proofs.Encoding
import Gzip.Proofs.Tokens
import Gzip.Proofs.Codes
import Gzip.Proofs.Dyn
import Gzip.Proofs.Header
import Gzip.Proofs.Tables
import Gzip.Proofs.Symbolize
import Gzip.Proofs.Huff
import Gzip.Proofs.Canon
import Gzip.Proofs.Histogram
import Gzip.Proofs.Rle
import Gzip.Proofs.Body
import Gzip.Proofs.Build
import Gzip.Proofs.DynBlock
import Gzip.Proofs.Member
import Gzip.Proofs.Decode.SpecCounterexample
import Gzip.Proofs.Decode.Decoding
import Gzip.Proofs.Decode.Parsing
import Gzip.Proofs.Decode.RoundTrip
import Gzip.Proofs.Decode.Encoding
import Gzip.Proofs.Decode.CrcImpl
import Gzip.Proofs.Decode.ReaderImpl
import Gzip.Proofs.Decode.HeaderImpl
import Gzip.Proofs.Decode.TablesImpl
import Gzip.Proofs.Decode.CodewordImpl
import Gzip.Proofs.Decode.SymbolImpl
import Gzip.Proofs.Decode.CopyImpl
import Gzip.Proofs.Decode.SymbolsImpl
import Gzip.Proofs.Decode.LengthsImpl
import Gzip.Proofs.Decode.DynamicImpl
import Gzip.Proofs.Decode.DecompressImpl
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 2000000

open Aeneas Std Result
open Gzip.Spec
open Djinn.Vocab

namespace Gzip.Proofs

/-! ## bit -/

theorem bit.wf :
    ∀ (s : List U8) (i : ℤ) (b : ℤ),
      bit_spec s i b →
      (8 ≠ 0) ∧ (0 ≤ (i / 8) ∧ (i / 8) < (s.length : ℤ)) ∧ (8 ≠ 0) ∧ (0 ≤ (i % 8)) ∧ ((2 ^ ((i % 8)).toNat) ≠ 0) ∧ (2 ≠ 0) := by
  intro s i b h
  obtain ⟨_, hi, _⟩ := h
  have hp : (2 : ℕ) ^ (i % 8).toNat ≠ 0 := pow_ne_zero _ (by norm_num)
  exact ⟨by norm_num, by omega, by norm_num, by omega, hp, by norm_num⟩

/-! ## field -/

theorem field.wf :
    ∀ (s : List U8) (i : ℤ) (n : ℤ) (v : ℤ),
      field_spec s i n v →
      ¬(n = 0) → ∀ v_call0 : ℤ, bit_spec s i v_call0 → (field_pre s (i + 1) (n - 1)) := by
  intro s i n v h hn x hx
  rw [field_spec] at h
  simp only [field_pre] at *
  omega

/-! ## code -/

theorem code.wf :
    ∀ (s : List U8) (i : ℤ) (n : ℤ) (v : ℤ),
      code_spec s i n v →
      ¬(n = 0) → (code_pre s i (n - 1)) := by
  intro s i n v h hn
  rw [code_spec] at h
  simp only [code_pre] at *
  omega

/-! ## u16le -/

theorem u16le.wf :
    ∀ (s : List U8) (i : ℤ) (v : ℤ),
      u16le_spec s i v →
      (0 ≤ i ∧ i < (s.length : ℤ)) ∧ (0 ≤ (i + 1) ∧ (i + 1) < (s.length : ℤ)) := by
  intro s i v h
  obtain ⟨_, hi, _⟩ := h
  omega

/-! ## u32le -/

/-! ## shorter -/

theorem shorter.wf :
    ∀ (lens : List U8) (k : ℤ) (n : ℤ) (c : ℤ),
      shorter_spec lens k n c →
      (¬(k = 0) → (0 ≤ (k - 1) ∧ (k - 1) < (lens.length : ℤ))) ∧
      (¬(k = 0) → 1 ≤ ((lens[(k - 1).toNat]!).val : ℤ) → (0 ≤ (k - 1) ∧ (k - 1) < (lens.length : ℤ))) ∧
      (¬(k = 0) → (1 ≤ ((lens[(k - 1).toNat]!).val : ℤ) ∧ ((lens[(k - 1).toNat]!).val : ℤ) < n) → (shorter_pre lens (k - 1) n)) ∧
      (¬(k = 0) → (1 ≤ ((lens[(k - 1).toNat]!).val : ℤ) ∧ ((lens[(k - 1).toNat]!).val : ℤ) < n) → ∀ v_call0 : ℤ, shorter_spec lens (k - 1) n v_call0 → (0 ≤ (k - 1) ∧ (k - 1) < (lens.length : ℤ)) ∧ (0 ≤ (n - ((lens[(k - 1).toNat]!).val : ℤ)))) ∧
      (¬(k = 0) → ¬((1 ≤ ((lens[(k - 1).toNat]!).val : ℤ) ∧ ((lens[(k - 1).toNat]!).val : ℤ) < n)) → (shorter_pre lens (k - 1) n)) := by
  intro lens k n c h
  rw [shorter_spec] at h
  simp only [shorter_pre] at *
  split_conjs <;> intros <;> omega

/-! ## earlier -/

theorem earlier.wf :
    ∀ (lens : List U8) (k : ℤ) (n : ℤ) (c : ℤ),
      earlier_spec lens k n c →
      (¬(k = 0) → (0 ≤ (k - 1) ∧ (k - 1) < (lens.length : ℤ))) ∧
      (¬(k = 0) → ((lens[(k - 1).toNat]!).val : ℤ) = n → (earlier_pre lens (k - 1) n)) ∧
      (¬(k = 0) → ¬(((lens[(k - 1).toNat]!).val : ℤ) = n) → (earlier_pre lens (k - 1) n)) := by
  intro lens k n c h
  rw [earlier_spec] at h
  simp only [earlier_pre] at *
  split_conjs <;> intros <;> omega

/-! ## codeword -/

theorem codeword.wf :
    ∀ (lens : List U8) (sym : ℤ) (c : ℤ),
      codeword_spec lens sym c →
      ((0 ≤ sym ∧ sym < (lens.length : ℤ)) ∧ (shorter_pre lens (lens.length : ℤ) ((lens[sym.toNat]!).val : ℤ))) ∧
      (∀ v_call0 : ℤ, shorter_spec lens (lens.length : ℤ) ((lens[sym.toNat]!).val : ℤ) v_call0 → (0 ≤ sym ∧ sym < (lens.length : ℤ)) ∧ (earlier_pre lens sym ((lens[sym.toNat]!).val : ℤ))) := by
  intro lens sym c h
  obtain ⟨_, hs, _⟩ := h
  simp only [shorter_pre, earlier_pre]
  split_conjs <;> intros <;> omega

/-! ## valid -/

theorem valid.wf :
    ∀ (lens : List U8) (n : ℤ) (b : Bool),
      valid_spec lens n b →
      ((∀ l, l ∈ lens → (l.val : ℤ) ≤ n) → (shorter_pre lens (lens.length : ℤ) (n + 1))) ∧
      ((∀ l, l ∈ lens → (l.val : ℤ) ≤ n) → ∀ v_call0 : ℤ, shorter_spec lens (lens.length : ℤ) (n + 1) v_call0 → (0 ≤ (n + 1))) := by
  intro lens n b h
  obtain ⟨hn, _⟩ := h
  simp only [valid_pre] at hn
  simp only [shorter_pre]
  split_conjs <;> intros <;> omega

/-! ## symbol -/

theorem symbol.wf :
    ∀ (s : List U8) (i : ℤ) (lens : List U8) (sym : ℤ),
      symbol_spec s i lens sym →
      ((0 ≤ sym ∧ sym < (lens.length : ℤ))) ∧
      (∀ v_call0 : ℤ, codeword_spec lens sym v_call0 → (0 ≤ sym ∧ sym < (lens.length : ℤ)) ∧ (code_pre s i ((lens[sym.toNat]!).val : ℤ))) := by
  intro s i lens sym h
  obtain ⟨_, hs, hl, _⟩ := h
  simp only [code_pre]
  exact ⟨hs, fun _ _ => ⟨hs, by omega⟩⟩

/-! ## fixedlen -/

/-! ## fixedlit -/

theorem fixedlit.wf :
    ∀  (lens : List U8),
      fixedlit_spec  lens →
      ∀ k : ℤ, 0 ≤ k → k < 288 → (0 ≤ k ∧ k < (lens.length : ℤ)) ∧ (0 ≤ k ∧ k < (lens.length : ℤ)) := by
  intro lens h k hk hk'
  obtain ⟨_, hn, _⟩ := h
  omega

/-! ## fixeddist -/

/-! ## lextra -/

theorem lextra.ens_0 :
    ∀ (k : ℤ) (e : ℤ),
      lextra_spec k e → 0 ≤ e := by
  intro k e h
  obtain ⟨_, hk, he⟩ := h
  by_cases hc : k < 8 ∨ k = 28
  · have := he.1 hc
    omega
  · have := he.2 hc
    omega

theorem lextra.wf :
    ∀ (k : ℤ) (e : ℤ),
      lextra_spec k e →
      ¬((k < 8 ∨ k = 28)) → (4 ≠ 0) := by
  intros
  norm_num

/-! ## lbase -/

theorem lbase.wf :
    ∀ (k : ℤ) (b : ℤ),
      lbase_spec k b →
      (¬(k = 0) → ¬(k = 28) → (lbase_pre (k - 1))) ∧
      (¬(k = 0) → ¬(k = 28) → ∀ v_call0 : ℤ, lbase_spec (k - 1) v_call0 → ∀ v_call1 : ℤ, lextra_spec (k - 1) v_call1 → (0 ≤ v_call1)) := by
  intro k b h
  rw [lbase_spec] at h
  simp only [lbase_pre] at h ⊢
  exact ⟨by intros; omega, fun _ _ _ _ _ he => lextra.ens_0 _ _ he⟩

/-! ## dextra -/

theorem dextra.ens_0 :
    ∀ (k : ℤ) (e : ℤ),
      dextra_spec k e → 0 ≤ e := by
  intro k e h
  obtain ⟨_, hk, he⟩ := h
  by_cases hc : k < 4
  · have := he.1 hc
    omega
  · have := he.2 hc
    omega

theorem dextra.wf :
    ∀ (k : ℤ) (e : ℤ),
      dextra_spec k e →
      ¬(k < 4) → (2 ≠ 0) := by
  intros
  norm_num

/-! ## dbase -/

theorem dbase.wf :
    ∀ (k : ℤ) (b : ℤ),
      dbase_spec k b →
      (¬(k = 0) → (dbase_pre (k - 1))) ∧
      (¬(k = 0) → ∀ v_call0 : ℤ, dbase_spec (k - 1) v_call0 → ∀ v_call1 : ℤ, dextra_spec (k - 1) v_call1 → (0 ≤ v_call1)) := by
  intro k b h
  rw [dbase_spec] at h
  simp only [dbase_pre] at h ⊢
  exact ⟨by intros; omega, fun _ _ _ _ he => dextra.ens_0 _ _ he⟩

/-! ## append -/

theorem append.wf :
    ∀ (prev : List U8) (x : ℤ) (out : List U8),
      append_spec prev x out →
      ((0 ≤ 0 ∧ 0 ≤ (prev.length : ℤ) ∧ (prev.length : ℤ) ≤ (out.length : ℤ))) ∧
      ((0 ≤ (prev.length : ℤ) ∧ (prev.length : ℤ) < (out.length : ℤ))) := by
  intro prev x out h
  obtain ⟨_, hn, _⟩ := h
  omega

/-! ## copy -/

theorem copy.wf :
    ∀ (prev : List U8) (d : ℤ) (len : ℤ) (out : List U8),
      copy_spec prev d len out →
      ((0 ≤ 0 ∧ 0 ≤ (prev.length : ℤ) ∧ (prev.length : ℤ) ≤ (out.length : ℤ))) ∧
      (∀ k : ℤ, (prev.length : ℤ) ≤ k → k < (out.length : ℤ) → (0 ≤ k ∧ k < (out.length : ℤ)) ∧ (0 ≤ (k - d) ∧ (k - d) < (out.length : ℤ))) := by
  intro prev d len out h
  obtain ⟨_, hd, hn, hp, _⟩ := h
  have ht := congrArg List.length hp
  simp only [List.drop_zero, List.length_take, Int.toNat_natCast] at ht
  constructor
  · omega
  · intro k hk hk'
    omega

/-! ## symbols -/


@[aesop safe forward]
theorem symbol_bounds (s : List U8) (i : ℤ) (lens : List U8) (sym : ℤ)
    (h : symbol_spec s i lens sym) : 0 ≤ sym ∧ sym < (lens.length : ℤ) := h.2.1

@[aesop safe forward]
theorem lbase_bounds (k b : ℤ) (h : lbase_spec k b) : 0 ≤ k := by
  rw [lbase_spec] at h
  exact h.1

@[aesop safe forward]
theorem dbase_bounds (k b : ℤ) (h : dbase_spec k b) : 0 ≤ k := by
  rw [dbase_spec] at h
  exact h.1

@[aesop safe forward]
theorem lengths_bounds (s : List U8) (i : ℤ) (cl : List U8) (p : ℤ) (all : List U8) (j : ℤ)
    (h : lengths_spec s i cl p all j) : 0 ≤ p ∧ p ≤ (all.length : ℤ) := by
  rw [lengths_spec] at h
  exact h.1

@[aesop safe forward]
theorem field_bounds (s : List U8) (i n v : ℤ) (h : field_spec s i n v) : 0 ≤ n := by
  rw [field_spec] at h
  exact h.1

@[aesop safe forward]
theorem u16le_bounds (s : List U8) (i v : ℤ) (h : u16le_spec s i v) : 0 ≤ i ∧ 0 ≤ v := by
  obtain ⟨_, hi, he⟩ := h
  constructor
  · omega
  · rw [he]
    positivity

@[aesop safe forward]
theorem prefix_length (a b : List U8) (h : b.take a.length = a) : a.length ≤ b.length := by
  have := congrArg List.length h
  simp only [List.length_take] at this
  omega

theorem cl_order_bounds (k : ℤ) (hk : 0 ≤ k) (hk' : k < 19) :
    (([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val : ℤ) < 19 := by
  interval_cases k <;> decide

theorem symbols.wf :
    ∀ (s : List U8) (i : ℤ) (lit : List U8) (dist : List U8) (prev : List U8) (out : List U8) (j : ℤ),
      symbols_spec s i lit dist prev out j →
      (∀ sym : ℤ, ∀ a : ℤ, (symbol_spec s i lit sym ∧ (symbol_spec s i lit sym → (a = (i + ((lit[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((lit[sym.toNat]!).val : ℤ)) → ((i < a ∧ a ≤ (8 * (s.length : ℤ))) ∧ ((i < a ∧ a ≤ (8 * (s.length : ℤ))) → ((sym = 256 → (out = prev ∧ j = a)) ∧ (¬(sym = 256) → ((sym < 256 → (∃ v_call0 : List U8, append_spec prev sym v_call0 ∧ (append_spec prev sym v_call0 → symbols_spec s a lit dist v_call0 out j))) ∧ (¬(sym < 256) → (∃ (len : ℤ) (b : ℤ) (dc : ℤ) (d : ℤ) (c : ℤ), ((∃ v_call10 : ℤ, lbase_spec (sym - 257) v_call10 ∧ (∃ v_call11 : ℤ, lextra_spec (sym - 257) v_call11 ∧ (∃ v_call12 : ℤ, field_spec s a v_call11 v_call12 ∧ len = (v_call10 + v_call12)))) ∧ ((∃ v_call10 : ℤ, lbase_spec (sym - 257) v_call10 ∧ (∃ v_call11 : ℤ, lextra_spec (sym - 257) v_call11 ∧ (∃ v_call12 : ℤ, field_spec s a v_call11 v_call12 ∧ len = (v_call10 + v_call12)))) → ((∃ v_call13 : ℤ, lextra_spec (sym - 257) v_call13 ∧ b = (a + v_call13)) ∧ ((∃ v_call13 : ℤ, lextra_spec (sym - 257) v_call13 ∧ b = (a + v_call13)) → (symbol_spec s b dist dc ∧ (symbol_spec s b dist dc → ((∃ v_call14 : ℤ, dbase_spec dc v_call14 ∧ (∃ v_call15 : ℤ, dextra_spec dc v_call15 ∧ (∃ v_call16 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call15 v_call16 ∧ d = (v_call14 + v_call16)))) ∧ ((∃ v_call14 : ℤ, dbase_spec dc v_call14 ∧ (∃ v_call15 : ℤ, dextra_spec dc v_call15 ∧ (∃ v_call16 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call15 v_call16 ∧ d = (v_call14 + v_call16)))) → ((∃ v_call17 : ℤ, dextra_spec dc v_call17 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call17)) ∧ ((∃ v_call17 : ℤ, dextra_spec dc v_call17 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call17)) → ((a < c ∧ c ≤ (8 * (s.length : ℤ))) ∧ ((a < c ∧ c ≤ (8 * (s.length : ℤ))) → (∃ v_call18 : List U8, copy_spec prev d len v_call18 ∧ (copy_spec prev d len v_call18 → symbols_spec s c lit dist v_call18 out j))))))))))))))))))))))))) → (0 ≤ sym ∧ sym < (lit.length : ℤ))) ∧
      (∀ sym : ℤ, ∀ a : ℤ, (symbol_spec s i lit sym ∧ (symbol_spec s i lit sym → (a = (i + ((lit[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((lit[sym.toNat]!).val : ℤ)) → ((i < a ∧ a ≤ (8 * (s.length : ℤ))) ∧ ((i < a ∧ a ≤ (8 * (s.length : ℤ))) → ((sym = 256 → (out = prev ∧ j = a)) ∧ (¬(sym = 256) → ((sym < 256 → (∃ v_call0 : List U8, append_spec prev sym v_call0 ∧ (append_spec prev sym v_call0 → symbols_spec s a lit dist v_call0 out j))) ∧ (¬(sym < 256) → (∃ (len : ℤ) (b : ℤ) (dc : ℤ) (d : ℤ) (c : ℤ), ((∃ v_call10 : ℤ, lbase_spec (sym - 257) v_call10 ∧ (∃ v_call11 : ℤ, lextra_spec (sym - 257) v_call11 ∧ (∃ v_call12 : ℤ, field_spec s a v_call11 v_call12 ∧ len = (v_call10 + v_call12)))) ∧ ((∃ v_call10 : ℤ, lbase_spec (sym - 257) v_call10 ∧ (∃ v_call11 : ℤ, lextra_spec (sym - 257) v_call11 ∧ (∃ v_call12 : ℤ, field_spec s a v_call11 v_call12 ∧ len = (v_call10 + v_call12)))) → ((∃ v_call13 : ℤ, lextra_spec (sym - 257) v_call13 ∧ b = (a + v_call13)) ∧ ((∃ v_call13 : ℤ, lextra_spec (sym - 257) v_call13 ∧ b = (a + v_call13)) → (symbol_spec s b dist dc ∧ (symbol_spec s b dist dc → ((∃ v_call14 : ℤ, dbase_spec dc v_call14 ∧ (∃ v_call15 : ℤ, dextra_spec dc v_call15 ∧ (∃ v_call16 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call15 v_call16 ∧ d = (v_call14 + v_call16)))) ∧ ((∃ v_call14 : ℤ, dbase_spec dc v_call14 ∧ (∃ v_call15 : ℤ, dextra_spec dc v_call15 ∧ (∃ v_call16 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call15 v_call16 ∧ d = (v_call14 + v_call16)))) → ((∃ v_call17 : ℤ, dextra_spec dc v_call17 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call17)) ∧ ((∃ v_call17 : ℤ, dextra_spec dc v_call17 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call17)) → ((a < c ∧ c ≤ (8 * (s.length : ℤ))) ∧ ((a < c ∧ c ≤ (8 * (s.length : ℤ))) → (∃ v_call18 : List U8, copy_spec prev d len v_call18 ∧ (copy_spec prev d len v_call18 → symbols_spec s c lit dist v_call18 out j))))))))))))))))))))))))) → ¬(sym = 256) → ¬(sym < 256) → ∀ len : ℤ, ∀ b : ℤ, ∀ dc : ℤ, ∀ d : ℤ, ∀ c : ℤ, ((∃ v_call20 : ℤ, lbase_spec (sym - 257) v_call20 ∧ (∃ v_call21 : ℤ, lextra_spec (sym - 257) v_call21 ∧ (∃ v_call22 : ℤ, field_spec s a v_call21 v_call22 ∧ len = (v_call20 + v_call22)))) ∧ ((∃ v_call20 : ℤ, lbase_spec (sym - 257) v_call20 ∧ (∃ v_call21 : ℤ, lextra_spec (sym - 257) v_call21 ∧ (∃ v_call22 : ℤ, field_spec s a v_call21 v_call22 ∧ len = (v_call20 + v_call22)))) → ((∃ v_call23 : ℤ, lextra_spec (sym - 257) v_call23 ∧ b = (a + v_call23)) ∧ ((∃ v_call23 : ℤ, lextra_spec (sym - 257) v_call23 ∧ b = (a + v_call23)) → (symbol_spec s b dist dc ∧ (symbol_spec s b dist dc → ((∃ v_call24 : ℤ, dbase_spec dc v_call24 ∧ (∃ v_call25 : ℤ, dextra_spec dc v_call25 ∧ (∃ v_call26 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call25 v_call26 ∧ d = (v_call24 + v_call26)))) ∧ ((∃ v_call24 : ℤ, dbase_spec dc v_call24 ∧ (∃ v_call25 : ℤ, dextra_spec dc v_call25 ∧ (∃ v_call26 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call25 v_call26 ∧ d = (v_call24 + v_call26)))) → ((∃ v_call27 : ℤ, dextra_spec dc v_call27 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call27)) ∧ ((∃ v_call27 : ℤ, dextra_spec dc v_call27 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call27)) → ((a < c ∧ c ≤ (8 * (s.length : ℤ))) ∧ ((a < c ∧ c ≤ (8 * (s.length : ℤ))) → (∃ v_call28 : List U8, copy_spec prev d len v_call28 ∧ (copy_spec prev d len v_call28 → symbols_spec s c lit dist v_call28 out j)))))))))))))) → (lbase_pre (sym - 257))) ∧
      (∀ sym : ℤ, ∀ a : ℤ, (symbol_spec s i lit sym ∧ (symbol_spec s i lit sym → (a = (i + ((lit[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((lit[sym.toNat]!).val : ℤ)) → ((i < a ∧ a ≤ (8 * (s.length : ℤ))) ∧ ((i < a ∧ a ≤ (8 * (s.length : ℤ))) → ((sym = 256 → (out = prev ∧ j = a)) ∧ (¬(sym = 256) → ((sym < 256 → (∃ v_call0 : List U8, append_spec prev sym v_call0 ∧ (append_spec prev sym v_call0 → symbols_spec s a lit dist v_call0 out j))) ∧ (¬(sym < 256) → (∃ (len : ℤ) (b : ℤ) (dc : ℤ) (d : ℤ) (c : ℤ), ((∃ v_call10 : ℤ, lbase_spec (sym - 257) v_call10 ∧ (∃ v_call11 : ℤ, lextra_spec (sym - 257) v_call11 ∧ (∃ v_call12 : ℤ, field_spec s a v_call11 v_call12 ∧ len = (v_call10 + v_call12)))) ∧ ((∃ v_call10 : ℤ, lbase_spec (sym - 257) v_call10 ∧ (∃ v_call11 : ℤ, lextra_spec (sym - 257) v_call11 ∧ (∃ v_call12 : ℤ, field_spec s a v_call11 v_call12 ∧ len = (v_call10 + v_call12)))) → ((∃ v_call13 : ℤ, lextra_spec (sym - 257) v_call13 ∧ b = (a + v_call13)) ∧ ((∃ v_call13 : ℤ, lextra_spec (sym - 257) v_call13 ∧ b = (a + v_call13)) → (symbol_spec s b dist dc ∧ (symbol_spec s b dist dc → ((∃ v_call14 : ℤ, dbase_spec dc v_call14 ∧ (∃ v_call15 : ℤ, dextra_spec dc v_call15 ∧ (∃ v_call16 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call15 v_call16 ∧ d = (v_call14 + v_call16)))) ∧ ((∃ v_call14 : ℤ, dbase_spec dc v_call14 ∧ (∃ v_call15 : ℤ, dextra_spec dc v_call15 ∧ (∃ v_call16 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call15 v_call16 ∧ d = (v_call14 + v_call16)))) → ((∃ v_call17 : ℤ, dextra_spec dc v_call17 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call17)) ∧ ((∃ v_call17 : ℤ, dextra_spec dc v_call17 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call17)) → ((a < c ∧ c ≤ (8 * (s.length : ℤ))) ∧ ((a < c ∧ c ≤ (8 * (s.length : ℤ))) → (∃ v_call18 : List U8, copy_spec prev d len v_call18 ∧ (copy_spec prev d len v_call18 → symbols_spec s c lit dist v_call18 out j))))))))))))))))))))))))) → ¬(sym = 256) → ¬(sym < 256) → ∀ len : ℤ, ∀ b : ℤ, ∀ dc : ℤ, ∀ d : ℤ, ∀ c : ℤ, ((∃ v_call20 : ℤ, lbase_spec (sym - 257) v_call20 ∧ (∃ v_call21 : ℤ, lextra_spec (sym - 257) v_call21 ∧ (∃ v_call22 : ℤ, field_spec s a v_call21 v_call22 ∧ len = (v_call20 + v_call22)))) ∧ ((∃ v_call20 : ℤ, lbase_spec (sym - 257) v_call20 ∧ (∃ v_call21 : ℤ, lextra_spec (sym - 257) v_call21 ∧ (∃ v_call22 : ℤ, field_spec s a v_call21 v_call22 ∧ len = (v_call20 + v_call22)))) → ((∃ v_call23 : ℤ, lextra_spec (sym - 257) v_call23 ∧ b = (a + v_call23)) ∧ ((∃ v_call23 : ℤ, lextra_spec (sym - 257) v_call23 ∧ b = (a + v_call23)) → (symbol_spec s b dist dc ∧ (symbol_spec s b dist dc → ((∃ v_call24 : ℤ, dbase_spec dc v_call24 ∧ (∃ v_call25 : ℤ, dextra_spec dc v_call25 ∧ (∃ v_call26 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call25 v_call26 ∧ d = (v_call24 + v_call26)))) ∧ ((∃ v_call24 : ℤ, dbase_spec dc v_call24 ∧ (∃ v_call25 : ℤ, dextra_spec dc v_call25 ∧ (∃ v_call26 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call25 v_call26 ∧ d = (v_call24 + v_call26)))) → ((∃ v_call27 : ℤ, dextra_spec dc v_call27 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call27)) ∧ ((∃ v_call27 : ℤ, dextra_spec dc v_call27 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call27)) → ((a < c ∧ c ≤ (8 * (s.length : ℤ))) ∧ ((a < c ∧ c ≤ (8 * (s.length : ℤ))) → (∃ v_call28 : List U8, copy_spec prev d len v_call28 ∧ (copy_spec prev d len v_call28 → symbols_spec s c lit dist v_call28 out j)))))))))))))) → ∀ v_call29 : ℤ, lbase_spec (sym - 257) v_call29 → ∀ v_call30 : ℤ, lextra_spec (sym - 257) v_call30 → (field_pre s a v_call30)) ∧
      (∀ sym : ℤ, ∀ a : ℤ, (symbol_spec s i lit sym ∧ (symbol_spec s i lit sym → (a = (i + ((lit[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((lit[sym.toNat]!).val : ℤ)) → ((i < a ∧ a ≤ (8 * (s.length : ℤ))) ∧ ((i < a ∧ a ≤ (8 * (s.length : ℤ))) → ((sym = 256 → (out = prev ∧ j = a)) ∧ (¬(sym = 256) → ((sym < 256 → (∃ v_call0 : List U8, append_spec prev sym v_call0 ∧ (append_spec prev sym v_call0 → symbols_spec s a lit dist v_call0 out j))) ∧ (¬(sym < 256) → (∃ (len : ℤ) (b : ℤ) (dc : ℤ) (d : ℤ) (c : ℤ), ((∃ v_call10 : ℤ, lbase_spec (sym - 257) v_call10 ∧ (∃ v_call11 : ℤ, lextra_spec (sym - 257) v_call11 ∧ (∃ v_call12 : ℤ, field_spec s a v_call11 v_call12 ∧ len = (v_call10 + v_call12)))) ∧ ((∃ v_call10 : ℤ, lbase_spec (sym - 257) v_call10 ∧ (∃ v_call11 : ℤ, lextra_spec (sym - 257) v_call11 ∧ (∃ v_call12 : ℤ, field_spec s a v_call11 v_call12 ∧ len = (v_call10 + v_call12)))) → ((∃ v_call13 : ℤ, lextra_spec (sym - 257) v_call13 ∧ b = (a + v_call13)) ∧ ((∃ v_call13 : ℤ, lextra_spec (sym - 257) v_call13 ∧ b = (a + v_call13)) → (symbol_spec s b dist dc ∧ (symbol_spec s b dist dc → ((∃ v_call14 : ℤ, dbase_spec dc v_call14 ∧ (∃ v_call15 : ℤ, dextra_spec dc v_call15 ∧ (∃ v_call16 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call15 v_call16 ∧ d = (v_call14 + v_call16)))) ∧ ((∃ v_call14 : ℤ, dbase_spec dc v_call14 ∧ (∃ v_call15 : ℤ, dextra_spec dc v_call15 ∧ (∃ v_call16 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call15 v_call16 ∧ d = (v_call14 + v_call16)))) → ((∃ v_call17 : ℤ, dextra_spec dc v_call17 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call17)) ∧ ((∃ v_call17 : ℤ, dextra_spec dc v_call17 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call17)) → ((a < c ∧ c ≤ (8 * (s.length : ℤ))) ∧ ((a < c ∧ c ≤ (8 * (s.length : ℤ))) → (∃ v_call18 : List U8, copy_spec prev d len v_call18 ∧ (copy_spec prev d len v_call18 → symbols_spec s c lit dist v_call18 out j))))))))))))))))))))))))) → ¬(sym = 256) → ¬(sym < 256) → ∀ len : ℤ, ∀ b : ℤ, ∀ dc : ℤ, ∀ d : ℤ, ∀ c : ℤ, ((∃ v_call20 : ℤ, lbase_spec (sym - 257) v_call20 ∧ (∃ v_call21 : ℤ, lextra_spec (sym - 257) v_call21 ∧ (∃ v_call22 : ℤ, field_spec s a v_call21 v_call22 ∧ len = (v_call20 + v_call22)))) ∧ ((∃ v_call20 : ℤ, lbase_spec (sym - 257) v_call20 ∧ (∃ v_call21 : ℤ, lextra_spec (sym - 257) v_call21 ∧ (∃ v_call22 : ℤ, field_spec s a v_call21 v_call22 ∧ len = (v_call20 + v_call22)))) → ((∃ v_call23 : ℤ, lextra_spec (sym - 257) v_call23 ∧ b = (a + v_call23)) ∧ ((∃ v_call23 : ℤ, lextra_spec (sym - 257) v_call23 ∧ b = (a + v_call23)) → (symbol_spec s b dist dc ∧ (symbol_spec s b dist dc → ((∃ v_call24 : ℤ, dbase_spec dc v_call24 ∧ (∃ v_call25 : ℤ, dextra_spec dc v_call25 ∧ (∃ v_call26 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call25 v_call26 ∧ d = (v_call24 + v_call26)))) ∧ ((∃ v_call24 : ℤ, dbase_spec dc v_call24 ∧ (∃ v_call25 : ℤ, dextra_spec dc v_call25 ∧ (∃ v_call26 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call25 v_call26 ∧ d = (v_call24 + v_call26)))) → ((∃ v_call27 : ℤ, dextra_spec dc v_call27 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call27)) ∧ ((∃ v_call27 : ℤ, dextra_spec dc v_call27 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call27)) → ((a < c ∧ c ≤ (8 * (s.length : ℤ))) ∧ ((a < c ∧ c ≤ (8 * (s.length : ℤ))) → (∃ v_call28 : List U8, copy_spec prev d len v_call28 ∧ (copy_spec prev d len v_call28 → symbols_spec s c lit dist v_call28 out j)))))))))))))) → (dbase_pre dc)) ∧
      (∀ sym : ℤ, ∀ a : ℤ, (symbol_spec s i lit sym ∧ (symbol_spec s i lit sym → (a = (i + ((lit[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((lit[sym.toNat]!).val : ℤ)) → ((i < a ∧ a ≤ (8 * (s.length : ℤ))) ∧ ((i < a ∧ a ≤ (8 * (s.length : ℤ))) → ((sym = 256 → (out = prev ∧ j = a)) ∧ (¬(sym = 256) → ((sym < 256 → (∃ v_call0 : List U8, append_spec prev sym v_call0 ∧ (append_spec prev sym v_call0 → symbols_spec s a lit dist v_call0 out j))) ∧ (¬(sym < 256) → (∃ (len : ℤ) (b : ℤ) (dc : ℤ) (d : ℤ) (c : ℤ), ((∃ v_call10 : ℤ, lbase_spec (sym - 257) v_call10 ∧ (∃ v_call11 : ℤ, lextra_spec (sym - 257) v_call11 ∧ (∃ v_call12 : ℤ, field_spec s a v_call11 v_call12 ∧ len = (v_call10 + v_call12)))) ∧ ((∃ v_call10 : ℤ, lbase_spec (sym - 257) v_call10 ∧ (∃ v_call11 : ℤ, lextra_spec (sym - 257) v_call11 ∧ (∃ v_call12 : ℤ, field_spec s a v_call11 v_call12 ∧ len = (v_call10 + v_call12)))) → ((∃ v_call13 : ℤ, lextra_spec (sym - 257) v_call13 ∧ b = (a + v_call13)) ∧ ((∃ v_call13 : ℤ, lextra_spec (sym - 257) v_call13 ∧ b = (a + v_call13)) → (symbol_spec s b dist dc ∧ (symbol_spec s b dist dc → ((∃ v_call14 : ℤ, dbase_spec dc v_call14 ∧ (∃ v_call15 : ℤ, dextra_spec dc v_call15 ∧ (∃ v_call16 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call15 v_call16 ∧ d = (v_call14 + v_call16)))) ∧ ((∃ v_call14 : ℤ, dbase_spec dc v_call14 ∧ (∃ v_call15 : ℤ, dextra_spec dc v_call15 ∧ (∃ v_call16 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call15 v_call16 ∧ d = (v_call14 + v_call16)))) → ((∃ v_call17 : ℤ, dextra_spec dc v_call17 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call17)) ∧ ((∃ v_call17 : ℤ, dextra_spec dc v_call17 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call17)) → ((a < c ∧ c ≤ (8 * (s.length : ℤ))) ∧ ((a < c ∧ c ≤ (8 * (s.length : ℤ))) → (∃ v_call18 : List U8, copy_spec prev d len v_call18 ∧ (copy_spec prev d len v_call18 → symbols_spec s c lit dist v_call18 out j))))))))))))))))))))))))) → ¬(sym = 256) → ¬(sym < 256) → ∀ len : ℤ, ∀ b : ℤ, ∀ dc : ℤ, ∀ d : ℤ, ∀ c : ℤ, ((∃ v_call20 : ℤ, lbase_spec (sym - 257) v_call20 ∧ (∃ v_call21 : ℤ, lextra_spec (sym - 257) v_call21 ∧ (∃ v_call22 : ℤ, field_spec s a v_call21 v_call22 ∧ len = (v_call20 + v_call22)))) ∧ ((∃ v_call20 : ℤ, lbase_spec (sym - 257) v_call20 ∧ (∃ v_call21 : ℤ, lextra_spec (sym - 257) v_call21 ∧ (∃ v_call22 : ℤ, field_spec s a v_call21 v_call22 ∧ len = (v_call20 + v_call22)))) → ((∃ v_call23 : ℤ, lextra_spec (sym - 257) v_call23 ∧ b = (a + v_call23)) ∧ ((∃ v_call23 : ℤ, lextra_spec (sym - 257) v_call23 ∧ b = (a + v_call23)) → (symbol_spec s b dist dc ∧ (symbol_spec s b dist dc → ((∃ v_call24 : ℤ, dbase_spec dc v_call24 ∧ (∃ v_call25 : ℤ, dextra_spec dc v_call25 ∧ (∃ v_call26 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call25 v_call26 ∧ d = (v_call24 + v_call26)))) ∧ ((∃ v_call24 : ℤ, dbase_spec dc v_call24 ∧ (∃ v_call25 : ℤ, dextra_spec dc v_call25 ∧ (∃ v_call26 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call25 v_call26 ∧ d = (v_call24 + v_call26)))) → ((∃ v_call27 : ℤ, dextra_spec dc v_call27 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call27)) ∧ ((∃ v_call27 : ℤ, dextra_spec dc v_call27 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call27)) → ((a < c ∧ c ≤ (8 * (s.length : ℤ))) ∧ ((a < c ∧ c ≤ (8 * (s.length : ℤ))) → (∃ v_call28 : List U8, copy_spec prev d len v_call28 ∧ (copy_spec prev d len v_call28 → symbols_spec s c lit dist v_call28 out j)))))))))))))) → ∀ v_call33 : ℤ, dbase_spec dc v_call33 → ∀ v_call34 : ℤ, dextra_spec dc v_call34 → (0 ≤ dc ∧ dc < (dist.length : ℤ)) ∧ (field_pre s (b + ((dist[dc.toNat]!).val : ℤ)) v_call34)) ∧
      (∀ sym : ℤ, ∀ a : ℤ, (symbol_spec s i lit sym ∧ (symbol_spec s i lit sym → (a = (i + ((lit[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((lit[sym.toNat]!).val : ℤ)) → ((i < a ∧ a ≤ (8 * (s.length : ℤ))) ∧ ((i < a ∧ a ≤ (8 * (s.length : ℤ))) → ((sym = 256 → (out = prev ∧ j = a)) ∧ (¬(sym = 256) → ((sym < 256 → (∃ v_call0 : List U8, append_spec prev sym v_call0 ∧ (append_spec prev sym v_call0 → symbols_spec s a lit dist v_call0 out j))) ∧ (¬(sym < 256) → (∃ (len : ℤ) (b : ℤ) (dc : ℤ) (d : ℤ) (c : ℤ), ((∃ v_call10 : ℤ, lbase_spec (sym - 257) v_call10 ∧ (∃ v_call11 : ℤ, lextra_spec (sym - 257) v_call11 ∧ (∃ v_call12 : ℤ, field_spec s a v_call11 v_call12 ∧ len = (v_call10 + v_call12)))) ∧ ((∃ v_call10 : ℤ, lbase_spec (sym - 257) v_call10 ∧ (∃ v_call11 : ℤ, lextra_spec (sym - 257) v_call11 ∧ (∃ v_call12 : ℤ, field_spec s a v_call11 v_call12 ∧ len = (v_call10 + v_call12)))) → ((∃ v_call13 : ℤ, lextra_spec (sym - 257) v_call13 ∧ b = (a + v_call13)) ∧ ((∃ v_call13 : ℤ, lextra_spec (sym - 257) v_call13 ∧ b = (a + v_call13)) → (symbol_spec s b dist dc ∧ (symbol_spec s b dist dc → ((∃ v_call14 : ℤ, dbase_spec dc v_call14 ∧ (∃ v_call15 : ℤ, dextra_spec dc v_call15 ∧ (∃ v_call16 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call15 v_call16 ∧ d = (v_call14 + v_call16)))) ∧ ((∃ v_call14 : ℤ, dbase_spec dc v_call14 ∧ (∃ v_call15 : ℤ, dextra_spec dc v_call15 ∧ (∃ v_call16 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call15 v_call16 ∧ d = (v_call14 + v_call16)))) → ((∃ v_call17 : ℤ, dextra_spec dc v_call17 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call17)) ∧ ((∃ v_call17 : ℤ, dextra_spec dc v_call17 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call17)) → ((a < c ∧ c ≤ (8 * (s.length : ℤ))) ∧ ((a < c ∧ c ≤ (8 * (s.length : ℤ))) → (∃ v_call18 : List U8, copy_spec prev d len v_call18 ∧ (copy_spec prev d len v_call18 → symbols_spec s c lit dist v_call18 out j))))))))))))))))))))))))) → ¬(sym = 256) → ¬(sym < 256) → ∀ len : ℤ, ∀ b : ℤ, ∀ dc : ℤ, ∀ d : ℤ, ∀ c : ℤ, ((∃ v_call20 : ℤ, lbase_spec (sym - 257) v_call20 ∧ (∃ v_call21 : ℤ, lextra_spec (sym - 257) v_call21 ∧ (∃ v_call22 : ℤ, field_spec s a v_call21 v_call22 ∧ len = (v_call20 + v_call22)))) ∧ ((∃ v_call20 : ℤ, lbase_spec (sym - 257) v_call20 ∧ (∃ v_call21 : ℤ, lextra_spec (sym - 257) v_call21 ∧ (∃ v_call22 : ℤ, field_spec s a v_call21 v_call22 ∧ len = (v_call20 + v_call22)))) → ((∃ v_call23 : ℤ, lextra_spec (sym - 257) v_call23 ∧ b = (a + v_call23)) ∧ ((∃ v_call23 : ℤ, lextra_spec (sym - 257) v_call23 ∧ b = (a + v_call23)) → (symbol_spec s b dist dc ∧ (symbol_spec s b dist dc → ((∃ v_call24 : ℤ, dbase_spec dc v_call24 ∧ (∃ v_call25 : ℤ, dextra_spec dc v_call25 ∧ (∃ v_call26 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call25 v_call26 ∧ d = (v_call24 + v_call26)))) ∧ ((∃ v_call24 : ℤ, dbase_spec dc v_call24 ∧ (∃ v_call25 : ℤ, dextra_spec dc v_call25 ∧ (∃ v_call26 : ℤ, field_spec s (b + ((dist[dc.toNat]!).val : ℤ)) v_call25 v_call26 ∧ d = (v_call24 + v_call26)))) → ((∃ v_call27 : ℤ, dextra_spec dc v_call27 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call27)) ∧ ((∃ v_call27 : ℤ, dextra_spec dc v_call27 ∧ c = ((b + ((dist[dc.toNat]!).val : ℤ)) + v_call27)) → ((a < c ∧ c ≤ (8 * (s.length : ℤ))) ∧ ((a < c ∧ c ≤ (8 * (s.length : ℤ))) → (∃ v_call28 : List U8, copy_spec prev d len v_call28 ∧ (copy_spec prev d len v_call28 → symbols_spec s c lit dist v_call28 out j)))))))))))))) → ∀ v_call36 : ℤ, dextra_spec dc v_call36 → (0 ≤ dc ∧ dc < (dist.length : ℤ))) := by
  intro s i lit dist prev out j h
  simp only [lbase_pre, dbase_pre, field_pre]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sym a hh
    exact symbol_bounds s i lit sym hh.1
  · intro sym a hh hn hg len b dc d c hc
    obtain ⟨v, hv, _⟩ := hc.1
    exact lbase_bounds _ _ hv
  · intro sym a hh hn hg len b dc d c hc v hv e he
    exact lextra.ens_0 _ _ he
  · intro sym a hh hn hg len b dc d c hc
    have hb := hc.2 hc.1
    have hd := hb.2 hb.1
    obtain ⟨v, hv, _⟩ := (hd.2 hd.1).1
    exact dbase_bounds _ _ hv
  · intro sym a hh hn hg len b dc d c hc v hv e he
    have hb := hc.2 hc.1
    have hd := hb.2 hb.1
    exact ⟨symbol_bounds s b dist dc hd.1, dextra.ens_0 _ _ he⟩
  · intro sym a hh hn hg len b dc d c hc e he
    have hb := hc.2 hc.1
    have hd := hb.2 hb.1
    exact symbol_bounds s b dist dc hd.1

/-! ## stored -/

theorem stored.wf :
    ∀ (s : List U8) (i : ℤ) (prev : List U8) (out : List U8) (j : ℤ),
      stored_spec s i prev out j →
      (∀ a : ℤ, ∀ len : ℤ, (a = ((i + 7) / 8) ∧ u16le_spec s a len ∧ u16le_spec s (a + 2) (65535 - len) ∧ ((a + 4) + len) ≤ (s.length : ℤ) ∧ (out.length : ℤ) = ((prev.length : ℤ) + len) ∧ ((out.drop 0).take ((prev.length : ℤ)).toNat) = prev ∧ ((out.drop ((prev.length : ℤ)).toNat).take ((out.length : ℤ) - (prev.length : ℤ)).toNat) = ((s.drop ((a + 4)).toNat).take (((a + 4) + len) - (a + 4)).toNat) ∧ j = (8 * ((a + 4) + len))) → (8 ≠ 0)) ∧
      (∀ a : ℤ, ∀ len : ℤ, (a = ((i + 7) / 8) ∧ u16le_spec s a len ∧ u16le_spec s (a + 2) (65535 - len) ∧ ((a + 4) + len) ≤ (s.length : ℤ) ∧ (out.length : ℤ) = ((prev.length : ℤ) + len) ∧ ((out.drop 0).take ((prev.length : ℤ)).toNat) = prev ∧ ((out.drop ((prev.length : ℤ)).toNat).take ((out.length : ℤ) - (prev.length : ℤ)).toNat) = ((s.drop ((a + 4)).toNat).take (((a + 4) + len) - (a + 4)).toNat) ∧ j = (8 * ((a + 4) + len))) → (0 ≤ 0 ∧ 0 ≤ (prev.length : ℤ) ∧ (prev.length : ℤ) ≤ (out.length : ℤ))) ∧
      (∀ a : ℤ, ∀ len : ℤ, (a = ((i + 7) / 8) ∧ u16le_spec s a len ∧ u16le_spec s (a + 2) (65535 - len) ∧ ((a + 4) + len) ≤ (s.length : ℤ) ∧ (out.length : ℤ) = ((prev.length : ℤ) + len) ∧ ((out.drop 0).take ((prev.length : ℤ)).toNat) = prev ∧ ((out.drop ((prev.length : ℤ)).toNat).take ((out.length : ℤ) - (prev.length : ℤ)).toNat) = ((s.drop ((a + 4)).toNat).take (((a + 4) + len) - (a + 4)).toNat) ∧ j = (8 * ((a + 4) + len))) → (0 ≤ (prev.length : ℤ) ∧ (prev.length : ℤ) ≤ (out.length : ℤ) ∧ (out.length : ℤ) ≤ (out.length : ℤ)) ∧ (0 ≤ (a + 4) ∧ (a + 4) ≤ ((a + 4) + len) ∧ ((a + 4) + len) ≤ (s.length : ℤ))) := by
  intro s i prev out j h
  refine ⟨?_, ?_, ?_⟩
  · intros
    norm_num
  · intro a len h
    obtain ⟨_, hl, _, _, _, hp, _⟩ := h
    have hb := prefix_length prev out (by simpa using hp)
    omega
  · intro a len h
    obtain ⟨_, hl, _, hs, hn, hp, _⟩ := h
    have hb := u16le_bounds s a len hl
    split_conjs <;> omega

/-! ## lengths -/

theorem lengths.wf :
    ∀ (s : List U8) (i : ℤ) (cl : List U8) (p : ℤ) (all : List U8) (j : ℤ),
      lengths_spec s i cl p all j →
      (¬(p = (all.length : ℤ)) → ∀ sym : ℤ, ∀ a : ℤ, ∀ n : ℤ, (symbol_spec s i cl sym ∧ (symbol_spec s i cl sym → (a = (i + ((cl[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((cl[sym.toNat]!).val : ℤ)) → ((sym < 16 → (n = 1 ∧ (n = 1 → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) → lengths_spec s a cl (p + n) all j))))) ∧ (¬(sym < 16) → ((sym = 16 → (1 ≤ p ∧ (1 ≤ p → ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) ∧ ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) → lengths_spec s (a + 2) cl (p + n) all j))))))))) ∧ (¬(sym = 16) → ((sym = 17 → ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) ∧ ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 3) cl (p + n) all j))))))) ∧ (¬(sym = 17) → (sym = 18 ∧ (sym = 18 → ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) ∧ ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 7) cl (p + n) all j)))))))))))))))))) → (0 ≤ sym ∧ sym < (cl.length : ℤ))) ∧
      (¬(p = (all.length : ℤ)) → ∀ sym : ℤ, ∀ a : ℤ, ∀ n : ℤ, (symbol_spec s i cl sym ∧ (symbol_spec s i cl sym → (a = (i + ((cl[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((cl[sym.toNat]!).val : ℤ)) → ((sym < 16 → (n = 1 ∧ (n = 1 → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) → lengths_spec s a cl (p + n) all j))))) ∧ (¬(sym < 16) → ((sym = 16 → (1 ≤ p ∧ (1 ≤ p → ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) ∧ ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) → lengths_spec s (a + 2) cl (p + n) all j))))))))) ∧ (¬(sym = 16) → ((sym = 17 → ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) ∧ ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 3) cl (p + n) all j))))))) ∧ (¬(sym = 17) → (sym = 18 ∧ (sym = 18 → ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) ∧ ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 7) cl (p + n) all j)))))))))))))))))) → sym < 16 → ∀ k : ℤ, p ≤ k → k < (p + n) → (0 ≤ k ∧ k < (all.length : ℤ))) ∧
      (¬(p = (all.length : ℤ)) → ∀ sym : ℤ, ∀ a : ℤ, ∀ n : ℤ, (symbol_spec s i cl sym ∧ (symbol_spec s i cl sym → (a = (i + ((cl[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((cl[sym.toNat]!).val : ℤ)) → ((sym < 16 → (n = 1 ∧ (n = 1 → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) → lengths_spec s a cl (p + n) all j))))) ∧ (¬(sym < 16) → ((sym = 16 → (1 ≤ p ∧ (1 ≤ p → ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) ∧ ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) → lengths_spec s (a + 2) cl (p + n) all j))))))))) ∧ (¬(sym = 16) → ((sym = 17 → ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) ∧ ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 3) cl (p + n) all j))))))) ∧ (¬(sym = 17) → (sym = 18 ∧ (sym = 18 → ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) ∧ ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 7) cl (p + n) all j)))))))))))))))))) → sym < 16 → (lengths_pre s a cl (p + n) all)) ∧
      (¬(p = (all.length : ℤ)) → ∀ sym : ℤ, ∀ a : ℤ, ∀ n : ℤ, (symbol_spec s i cl sym ∧ (symbol_spec s i cl sym → (a = (i + ((cl[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((cl[sym.toNat]!).val : ℤ)) → ((sym < 16 → (n = 1 ∧ (n = 1 → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) → lengths_spec s a cl (p + n) all j))))) ∧ (¬(sym < 16) → ((sym = 16 → (1 ≤ p ∧ (1 ≤ p → ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) ∧ ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) → lengths_spec s (a + 2) cl (p + n) all j))))))))) ∧ (¬(sym = 16) → ((sym = 17 → ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) ∧ ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 3) cl (p + n) all j))))))) ∧ (¬(sym = 17) → (sym = 18 ∧ (sym = 18 → ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) ∧ ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 7) cl (p + n) all j)))))))))))))))))) → ¬(sym < 16) → sym = 16 → (field_pre s a 2)) ∧
      (¬(p = (all.length : ℤ)) → ∀ sym : ℤ, ∀ a : ℤ, ∀ n : ℤ, (symbol_spec s i cl sym ∧ (symbol_spec s i cl sym → (a = (i + ((cl[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((cl[sym.toNat]!).val : ℤ)) → ((sym < 16 → (n = 1 ∧ (n = 1 → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) → lengths_spec s a cl (p + n) all j))))) ∧ (¬(sym < 16) → ((sym = 16 → (1 ≤ p ∧ (1 ≤ p → ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) ∧ ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) → lengths_spec s (a + 2) cl (p + n) all j))))))))) ∧ (¬(sym = 16) → ((sym = 17 → ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) ∧ ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 3) cl (p + n) all j))))))) ∧ (¬(sym = 17) → (sym = 18 ∧ (sym = 18 → ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) ∧ ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 7) cl (p + n) all j)))))))))))))))))) → ¬(sym < 16) → sym = 16 → ∀ k : ℤ, p ≤ k → k < (p + n) → (0 ≤ k ∧ k < (all.length : ℤ)) ∧ (0 ≤ (p - 1) ∧ (p - 1) < (all.length : ℤ))) ∧
      (¬(p = (all.length : ℤ)) → ∀ sym : ℤ, ∀ a : ℤ, ∀ n : ℤ, (symbol_spec s i cl sym ∧ (symbol_spec s i cl sym → (a = (i + ((cl[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((cl[sym.toNat]!).val : ℤ)) → ((sym < 16 → (n = 1 ∧ (n = 1 → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) → lengths_spec s a cl (p + n) all j))))) ∧ (¬(sym < 16) → ((sym = 16 → (1 ≤ p ∧ (1 ≤ p → ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) ∧ ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) → lengths_spec s (a + 2) cl (p + n) all j))))))))) ∧ (¬(sym = 16) → ((sym = 17 → ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) ∧ ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 3) cl (p + n) all j))))))) ∧ (¬(sym = 17) → (sym = 18 ∧ (sym = 18 → ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) ∧ ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 7) cl (p + n) all j)))))))))))))))))) → ¬(sym < 16) → sym = 16 → (lengths_pre s (a + 2) cl (p + n) all)) ∧
      (¬(p = (all.length : ℤ)) → ∀ sym : ℤ, ∀ a : ℤ, ∀ n : ℤ, (symbol_spec s i cl sym ∧ (symbol_spec s i cl sym → (a = (i + ((cl[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((cl[sym.toNat]!).val : ℤ)) → ((sym < 16 → (n = 1 ∧ (n = 1 → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) → lengths_spec s a cl (p + n) all j))))) ∧ (¬(sym < 16) → ((sym = 16 → (1 ≤ p ∧ (1 ≤ p → ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) ∧ ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) → lengths_spec s (a + 2) cl (p + n) all j))))))))) ∧ (¬(sym = 16) → ((sym = 17 → ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) ∧ ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 3) cl (p + n) all j))))))) ∧ (¬(sym = 17) → (sym = 18 ∧ (sym = 18 → ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) ∧ ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 7) cl (p + n) all j)))))))))))))))))) → ¬(sym < 16) → ¬(sym = 16) → sym = 17 → (field_pre s a 3)) ∧
      (¬(p = (all.length : ℤ)) → ∀ sym : ℤ, ∀ a : ℤ, ∀ n : ℤ, (symbol_spec s i cl sym ∧ (symbol_spec s i cl sym → (a = (i + ((cl[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((cl[sym.toNat]!).val : ℤ)) → ((sym < 16 → (n = 1 ∧ (n = 1 → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) → lengths_spec s a cl (p + n) all j))))) ∧ (¬(sym < 16) → ((sym = 16 → (1 ≤ p ∧ (1 ≤ p → ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) ∧ ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) → lengths_spec s (a + 2) cl (p + n) all j))))))))) ∧ (¬(sym = 16) → ((sym = 17 → ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) ∧ ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 3) cl (p + n) all j))))))) ∧ (¬(sym = 17) → (sym = 18 ∧ (sym = 18 → ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) ∧ ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 7) cl (p + n) all j)))))))))))))))))) → ¬(sym < 16) → ¬(sym = 16) → sym = 17 → ∀ k : ℤ, p ≤ k → k < (p + n) → (0 ≤ k ∧ k < (all.length : ℤ))) ∧
      (¬(p = (all.length : ℤ)) → ∀ sym : ℤ, ∀ a : ℤ, ∀ n : ℤ, (symbol_spec s i cl sym ∧ (symbol_spec s i cl sym → (a = (i + ((cl[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((cl[sym.toNat]!).val : ℤ)) → ((sym < 16 → (n = 1 ∧ (n = 1 → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) → lengths_spec s a cl (p + n) all j))))) ∧ (¬(sym < 16) → ((sym = 16 → (1 ≤ p ∧ (1 ≤ p → ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) ∧ ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) → lengths_spec s (a + 2) cl (p + n) all j))))))))) ∧ (¬(sym = 16) → ((sym = 17 → ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) ∧ ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 3) cl (p + n) all j))))))) ∧ (¬(sym = 17) → (sym = 18 ∧ (sym = 18 → ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) ∧ ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 7) cl (p + n) all j)))))))))))))))))) → ¬(sym < 16) → ¬(sym = 16) → sym = 17 → (lengths_pre s (a + 3) cl (p + n) all)) ∧
      (¬(p = (all.length : ℤ)) → ∀ sym : ℤ, ∀ a : ℤ, ∀ n : ℤ, (symbol_spec s i cl sym ∧ (symbol_spec s i cl sym → (a = (i + ((cl[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((cl[sym.toNat]!).val : ℤ)) → ((sym < 16 → (n = 1 ∧ (n = 1 → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) → lengths_spec s a cl (p + n) all j))))) ∧ (¬(sym < 16) → ((sym = 16 → (1 ≤ p ∧ (1 ≤ p → ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) ∧ ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) → lengths_spec s (a + 2) cl (p + n) all j))))))))) ∧ (¬(sym = 16) → ((sym = 17 → ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) ∧ ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 3) cl (p + n) all j))))))) ∧ (¬(sym = 17) → (sym = 18 ∧ (sym = 18 → ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) ∧ ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 7) cl (p + n) all j)))))))))))))))))) → ¬(sym < 16) → ¬(sym = 16) → ¬(sym = 17) → (field_pre s a 7)) ∧
      (¬(p = (all.length : ℤ)) → ∀ sym : ℤ, ∀ a : ℤ, ∀ n : ℤ, (symbol_spec s i cl sym ∧ (symbol_spec s i cl sym → (a = (i + ((cl[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((cl[sym.toNat]!).val : ℤ)) → ((sym < 16 → (n = 1 ∧ (n = 1 → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) → lengths_spec s a cl (p + n) all j))))) ∧ (¬(sym < 16) → ((sym = 16 → (1 ≤ p ∧ (1 ≤ p → ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) ∧ ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) → lengths_spec s (a + 2) cl (p + n) all j))))))))) ∧ (¬(sym = 16) → ((sym = 17 → ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) ∧ ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 3) cl (p + n) all j))))))) ∧ (¬(sym = 17) → (sym = 18 ∧ (sym = 18 → ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) ∧ ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 7) cl (p + n) all j)))))))))))))))))) → ¬(sym < 16) → ¬(sym = 16) → ¬(sym = 17) → ∀ k : ℤ, p ≤ k → k < (p + n) → (0 ≤ k ∧ k < (all.length : ℤ))) ∧
      (¬(p = (all.length : ℤ)) → ∀ sym : ℤ, ∀ a : ℤ, ∀ n : ℤ, (symbol_spec s i cl sym ∧ (symbol_spec s i cl sym → (a = (i + ((cl[sym.toNat]!).val : ℤ)) ∧ (a = (i + ((cl[sym.toNat]!).val : ℤ)) → ((sym < 16 → (n = 1 ∧ (n = 1 → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = sym) → lengths_spec s a cl (p + n) all j))))) ∧ (¬(sym < 16) → ((sym = 16 → (1 ≤ p ∧ (1 ≤ p → ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) ∧ ((∃ v_call0 : ℤ, field_spec s a 2 v_call0 ∧ n = (3 + v_call0)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → all[k.toNat]! = all[(p - 1).toNat]!) → lengths_spec s (a + 2) cl (p + n) all j))))))))) ∧ (¬(sym = 16) → ((sym = 17 → ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) ∧ ((∃ v_call1 : ℤ, field_spec s a 3 v_call1 ∧ n = (3 + v_call1)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 3) cl (p + n) all j))))))) ∧ (¬(sym = 17) → (sym = 18 ∧ (sym = 18 → ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) ∧ ((∃ v_call2 : ℤ, field_spec s a 7 v_call2 ∧ n = (11 + v_call2)) → ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) ∧ ((p < (p + n) ∧ (p + n) ≤ (all.length : ℤ)) → ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) ∧ ((∀ k : ℤ, p ≤ k → k < (p + n) → ((all[k.toNat]!).val : ℤ) = 0) → lengths_spec s (a + 7) cl (p + n) all j)))))))))))))))))) → ¬(sym < 16) → ¬(sym = 16) → ¬(sym = 17) → (lengths_pre s (a + 7) cl (p + n) all)) := by
  intro s i cl p all j h
  have hp := lengths_bounds s i cl p all j h
  simp only [lengths_pre, field_pre]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hz sym a n hh
    exact symbol_bounds s i cl sym hh.1
  · intro hz sym a n hh hs k hk hk'
    have ha := hh.2 hh.1
    have hn := (ha.2 ha.1).1 hs
    omega
  · intro hz sym a n hh hs
    have ha := hh.2 hh.1
    have hn := (ha.2 ha.1).1 hs
    omega
  · intros
    norm_num
  · intro hz sym a n hh hs hs16 k hk hk'
    have ha := hh.2 hh.1
    have h16 := (ha.2 ha.1).2 hs
    have hb := h16.1 hs16
    have hc := hb.2 hb.1
    have hd := hc.2 hc.1
    omega
  · intro hz sym a n hh hs hs16
    have ha := hh.2 hh.1
    have h16 := (ha.2 ha.1).2 hs
    have hb := h16.1 hs16
    have hc := hb.2 hb.1
    have hd := hc.2 hc.1
    omega
  · intros
    norm_num
  · intro hz sym a n hh hs hs16 hs17 k hk hk'
    have ha := hh.2 hh.1
    have hb := ((ha.2 ha.1).2 hs).2 hs16
    have hc := hb.1 hs17
    have hd := hc.2 hc.1
    omega
  · intro hz sym a n hh hs hs16 hs17
    have ha := hh.2 hh.1
    have hb := ((ha.2 ha.1).2 hs).2 hs16
    have hc := hb.1 hs17
    have hd := hc.2 hc.1
    omega
  · intros
    norm_num
  · intro hz sym a n hh hs hs16 hs17 k hk hk'
    have ha := hh.2 hh.1
    have hb := ((ha.2 ha.1).2 hs).2 hs16
    have hc := hb.2 hs17
    have hd := hc.2 hc.1
    have he := hd.2 hd.1
    omega
  · intro hz sym a n hh hs hs16 hs17
    have ha := hh.2 hh.1
    have hb := ((ha.2 ha.1).2 hs).2 hs16
    have hc := hb.2 hs17
    have hd := hc.2 hc.1
    have he := hd.2 hd.1
    omega

/-! ## tables -/

theorem tables.wf :
    ∀ (s : List U8) (i : ℤ) (lit : List U8) (dist : List U8) (j : ℤ),
      tables_spec s i lit dist j →
      (∀ hclen : ℤ, ∀ cl : List U8, ∀ all : List U8, ((∃ v_call0 : ℤ, field_spec s i 5 v_call0 ∧ (lit.length : ℤ) = (257 + v_call0)) ∧ (∃ v_call1 : ℤ, field_spec s (i + 5) 5 v_call1 ∧ (dist.length : ℤ) = (1 + v_call1)) ∧ (∃ v_call2 : ℤ, field_spec s (i + 10) 4 v_call2 ∧ hclen = (4 + v_call2)) ∧ (cl.length : ℤ) = 19 ∧ (∀ k : ℤ, 0 ≤ k → k < 19 → ((k < hclen → (∃ v_out3 : ℤ, field_spec s ((i + 14) + (3 * k)) 3 v_out3 ∧ v_out3 = ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ))) ∧ (¬(k < hclen) → ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ) = 0))) ∧ valid_spec cl 7 true ∧ (all.length : ℤ) = ((lit.length : ℤ) + (dist.length : ℤ)) ∧ ((all.drop 0).take ((lit.length : ℤ)).toNat) = lit ∧ ((all.drop ((lit.length : ℤ)).toNat).take ((all.length : ℤ) - (lit.length : ℤ)).toNat) = dist ∧ lengths_spec s ((i + 14) + (3 * hclen)) cl 0 all j ∧ valid_spec lit 15 true ∧ valid_spec dist 15 true) → (field_pre s i 5)) ∧
      (∀ hclen : ℤ, ∀ cl : List U8, ∀ all : List U8, ((∃ v_call0 : ℤ, field_spec s i 5 v_call0 ∧ (lit.length : ℤ) = (257 + v_call0)) ∧ (∃ v_call1 : ℤ, field_spec s (i + 5) 5 v_call1 ∧ (dist.length : ℤ) = (1 + v_call1)) ∧ (∃ v_call2 : ℤ, field_spec s (i + 10) 4 v_call2 ∧ hclen = (4 + v_call2)) ∧ (cl.length : ℤ) = 19 ∧ (∀ k : ℤ, 0 ≤ k → k < 19 → ((k < hclen → (∃ v_out3 : ℤ, field_spec s ((i + 14) + (3 * k)) 3 v_out3 ∧ v_out3 = ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ))) ∧ (¬(k < hclen) → ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ) = 0))) ∧ valid_spec cl 7 true ∧ (all.length : ℤ) = ((lit.length : ℤ) + (dist.length : ℤ)) ∧ ((all.drop 0).take ((lit.length : ℤ)).toNat) = lit ∧ ((all.drop ((lit.length : ℤ)).toNat).take ((all.length : ℤ) - (lit.length : ℤ)).toNat) = dist ∧ lengths_spec s ((i + 14) + (3 * hclen)) cl 0 all j ∧ valid_spec lit 15 true ∧ valid_spec dist 15 true) → (field_pre s (i + 5) 5)) ∧
      (∀ hclen : ℤ, ∀ cl : List U8, ∀ all : List U8, ((∃ v_call0 : ℤ, field_spec s i 5 v_call0 ∧ (lit.length : ℤ) = (257 + v_call0)) ∧ (∃ v_call1 : ℤ, field_spec s (i + 5) 5 v_call1 ∧ (dist.length : ℤ) = (1 + v_call1)) ∧ (∃ v_call2 : ℤ, field_spec s (i + 10) 4 v_call2 ∧ hclen = (4 + v_call2)) ∧ (cl.length : ℤ) = 19 ∧ (∀ k : ℤ, 0 ≤ k → k < 19 → ((k < hclen → (∃ v_out3 : ℤ, field_spec s ((i + 14) + (3 * k)) 3 v_out3 ∧ v_out3 = ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ))) ∧ (¬(k < hclen) → ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ) = 0))) ∧ valid_spec cl 7 true ∧ (all.length : ℤ) = ((lit.length : ℤ) + (dist.length : ℤ)) ∧ ((all.drop 0).take ((lit.length : ℤ)).toNat) = lit ∧ ((all.drop ((lit.length : ℤ)).toNat).take ((all.length : ℤ) - (lit.length : ℤ)).toNat) = dist ∧ lengths_spec s ((i + 14) + (3 * hclen)) cl 0 all j ∧ valid_spec lit 15 true ∧ valid_spec dist 15 true) → (field_pre s (i + 10) 4)) ∧
      (∀ hclen : ℤ, ∀ cl : List U8, ∀ all : List U8, ((∃ v_call0 : ℤ, field_spec s i 5 v_call0 ∧ (lit.length : ℤ) = (257 + v_call0)) ∧ (∃ v_call1 : ℤ, field_spec s (i + 5) 5 v_call1 ∧ (dist.length : ℤ) = (1 + v_call1)) ∧ (∃ v_call2 : ℤ, field_spec s (i + 10) 4 v_call2 ∧ hclen = (4 + v_call2)) ∧ (cl.length : ℤ) = 19 ∧ (∀ k : ℤ, 0 ≤ k → k < 19 → ((k < hclen → (∃ v_out3 : ℤ, field_spec s ((i + 14) + (3 * k)) 3 v_out3 ∧ v_out3 = ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ))) ∧ (¬(k < hclen) → ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ) = 0))) ∧ valid_spec cl 7 true ∧ (all.length : ℤ) = ((lit.length : ℤ) + (dist.length : ℤ)) ∧ ((all.drop 0).take ((lit.length : ℤ)).toNat) = lit ∧ ((all.drop ((lit.length : ℤ)).toNat).take ((all.length : ℤ) - (lit.length : ℤ)).toNat) = dist ∧ lengths_spec s ((i + 14) + (3 * hclen)) cl 0 all j ∧ valid_spec lit 15 true ∧ valid_spec dist 15 true) → ∀ k : ℤ, 0 ≤ k → k < 19 → k < hclen → (0 ≤ k ∧ k < ([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8].length : ℤ)) ∧ ((([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val : ℤ) < (cl.length : ℤ)) ∧ (field_pre s ((i + 14) + (3 * k)) 3) ∧ (0 ≤ k ∧ k < ([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8].length : ℤ)) ∧ ((([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val : ℤ) < (cl.length : ℤ))) ∧
      (∀ hclen : ℤ, ∀ cl : List U8, ∀ all : List U8, ((∃ v_call0 : ℤ, field_spec s i 5 v_call0 ∧ (lit.length : ℤ) = (257 + v_call0)) ∧ (∃ v_call1 : ℤ, field_spec s (i + 5) 5 v_call1 ∧ (dist.length : ℤ) = (1 + v_call1)) ∧ (∃ v_call2 : ℤ, field_spec s (i + 10) 4 v_call2 ∧ hclen = (4 + v_call2)) ∧ (cl.length : ℤ) = 19 ∧ (∀ k : ℤ, 0 ≤ k → k < 19 → ((k < hclen → (∃ v_out3 : ℤ, field_spec s ((i + 14) + (3 * k)) 3 v_out3 ∧ v_out3 = ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ))) ∧ (¬(k < hclen) → ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ) = 0))) ∧ valid_spec cl 7 true ∧ (all.length : ℤ) = ((lit.length : ℤ) + (dist.length : ℤ)) ∧ ((all.drop 0).take ((lit.length : ℤ)).toNat) = lit ∧ ((all.drop ((lit.length : ℤ)).toNat).take ((all.length : ℤ) - (lit.length : ℤ)).toNat) = dist ∧ lengths_spec s ((i + 14) + (3 * hclen)) cl 0 all j ∧ valid_spec lit 15 true ∧ valid_spec dist 15 true) → ∀ k : ℤ, 0 ≤ k → k < 19 → ¬(k < hclen) → (0 ≤ k ∧ k < ([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8].length : ℤ)) ∧ ((([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val : ℤ) < (cl.length : ℤ))) ∧
      (∀ hclen : ℤ, ∀ cl : List U8, ∀ all : List U8, ((∃ v_call0 : ℤ, field_spec s i 5 v_call0 ∧ (lit.length : ℤ) = (257 + v_call0)) ∧ (∃ v_call1 : ℤ, field_spec s (i + 5) 5 v_call1 ∧ (dist.length : ℤ) = (1 + v_call1)) ∧ (∃ v_call2 : ℤ, field_spec s (i + 10) 4 v_call2 ∧ hclen = (4 + v_call2)) ∧ (cl.length : ℤ) = 19 ∧ (∀ k : ℤ, 0 ≤ k → k < 19 → ((k < hclen → (∃ v_out3 : ℤ, field_spec s ((i + 14) + (3 * k)) 3 v_out3 ∧ v_out3 = ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ))) ∧ (¬(k < hclen) → ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ) = 0))) ∧ valid_spec cl 7 true ∧ (all.length : ℤ) = ((lit.length : ℤ) + (dist.length : ℤ)) ∧ ((all.drop 0).take ((lit.length : ℤ)).toNat) = lit ∧ ((all.drop ((lit.length : ℤ)).toNat).take ((all.length : ℤ) - (lit.length : ℤ)).toNat) = dist ∧ lengths_spec s ((i + 14) + (3 * hclen)) cl 0 all j ∧ valid_spec lit 15 true ∧ valid_spec dist 15 true) → (valid_pre cl 7)) ∧
      (∀ hclen : ℤ, ∀ cl : List U8, ∀ all : List U8, ((∃ v_call0 : ℤ, field_spec s i 5 v_call0 ∧ (lit.length : ℤ) = (257 + v_call0)) ∧ (∃ v_call1 : ℤ, field_spec s (i + 5) 5 v_call1 ∧ (dist.length : ℤ) = (1 + v_call1)) ∧ (∃ v_call2 : ℤ, field_spec s (i + 10) 4 v_call2 ∧ hclen = (4 + v_call2)) ∧ (cl.length : ℤ) = 19 ∧ (∀ k : ℤ, 0 ≤ k → k < 19 → ((k < hclen → (∃ v_out3 : ℤ, field_spec s ((i + 14) + (3 * k)) 3 v_out3 ∧ v_out3 = ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ))) ∧ (¬(k < hclen) → ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ) = 0))) ∧ valid_spec cl 7 true ∧ (all.length : ℤ) = ((lit.length : ℤ) + (dist.length : ℤ)) ∧ ((all.drop 0).take ((lit.length : ℤ)).toNat) = lit ∧ ((all.drop ((lit.length : ℤ)).toNat).take ((all.length : ℤ) - (lit.length : ℤ)).toNat) = dist ∧ lengths_spec s ((i + 14) + (3 * hclen)) cl 0 all j ∧ valid_spec lit 15 true ∧ valid_spec dist 15 true) → (0 ≤ 0 ∧ 0 ≤ (lit.length : ℤ) ∧ (lit.length : ℤ) ≤ (all.length : ℤ))) ∧
      (∀ hclen : ℤ, ∀ cl : List U8, ∀ all : List U8, ((∃ v_call0 : ℤ, field_spec s i 5 v_call0 ∧ (lit.length : ℤ) = (257 + v_call0)) ∧ (∃ v_call1 : ℤ, field_spec s (i + 5) 5 v_call1 ∧ (dist.length : ℤ) = (1 + v_call1)) ∧ (∃ v_call2 : ℤ, field_spec s (i + 10) 4 v_call2 ∧ hclen = (4 + v_call2)) ∧ (cl.length : ℤ) = 19 ∧ (∀ k : ℤ, 0 ≤ k → k < 19 → ((k < hclen → (∃ v_out3 : ℤ, field_spec s ((i + 14) + (3 * k)) 3 v_out3 ∧ v_out3 = ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ))) ∧ (¬(k < hclen) → ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ) = 0))) ∧ valid_spec cl 7 true ∧ (all.length : ℤ) = ((lit.length : ℤ) + (dist.length : ℤ)) ∧ ((all.drop 0).take ((lit.length : ℤ)).toNat) = lit ∧ ((all.drop ((lit.length : ℤ)).toNat).take ((all.length : ℤ) - (lit.length : ℤ)).toNat) = dist ∧ lengths_spec s ((i + 14) + (3 * hclen)) cl 0 all j ∧ valid_spec lit 15 true ∧ valid_spec dist 15 true) → (0 ≤ (lit.length : ℤ) ∧ (lit.length : ℤ) ≤ (all.length : ℤ) ∧ (all.length : ℤ) ≤ (all.length : ℤ))) ∧
      (∀ hclen : ℤ, ∀ cl : List U8, ∀ all : List U8, ((∃ v_call0 : ℤ, field_spec s i 5 v_call0 ∧ (lit.length : ℤ) = (257 + v_call0)) ∧ (∃ v_call1 : ℤ, field_spec s (i + 5) 5 v_call1 ∧ (dist.length : ℤ) = (1 + v_call1)) ∧ (∃ v_call2 : ℤ, field_spec s (i + 10) 4 v_call2 ∧ hclen = (4 + v_call2)) ∧ (cl.length : ℤ) = 19 ∧ (∀ k : ℤ, 0 ≤ k → k < 19 → ((k < hclen → (∃ v_out3 : ℤ, field_spec s ((i + 14) + (3 * k)) 3 v_out3 ∧ v_out3 = ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ))) ∧ (¬(k < hclen) → ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ) = 0))) ∧ valid_spec cl 7 true ∧ (all.length : ℤ) = ((lit.length : ℤ) + (dist.length : ℤ)) ∧ ((all.drop 0).take ((lit.length : ℤ)).toNat) = lit ∧ ((all.drop ((lit.length : ℤ)).toNat).take ((all.length : ℤ) - (lit.length : ℤ)).toNat) = dist ∧ lengths_spec s ((i + 14) + (3 * hclen)) cl 0 all j ∧ valid_spec lit 15 true ∧ valid_spec dist 15 true) → (lengths_pre s ((i + 14) + (3 * hclen)) cl 0 all)) ∧
      (∀ hclen : ℤ, ∀ cl : List U8, ∀ all : List U8, ((∃ v_call0 : ℤ, field_spec s i 5 v_call0 ∧ (lit.length : ℤ) = (257 + v_call0)) ∧ (∃ v_call1 : ℤ, field_spec s (i + 5) 5 v_call1 ∧ (dist.length : ℤ) = (1 + v_call1)) ∧ (∃ v_call2 : ℤ, field_spec s (i + 10) 4 v_call2 ∧ hclen = (4 + v_call2)) ∧ (cl.length : ℤ) = 19 ∧ (∀ k : ℤ, 0 ≤ k → k < 19 → ((k < hclen → (∃ v_out3 : ℤ, field_spec s ((i + 14) + (3 * k)) 3 v_out3 ∧ v_out3 = ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ))) ∧ (¬(k < hclen) → ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ) = 0))) ∧ valid_spec cl 7 true ∧ (all.length : ℤ) = ((lit.length : ℤ) + (dist.length : ℤ)) ∧ ((all.drop 0).take ((lit.length : ℤ)).toNat) = lit ∧ ((all.drop ((lit.length : ℤ)).toNat).take ((all.length : ℤ) - (lit.length : ℤ)).toNat) = dist ∧ lengths_spec s ((i + 14) + (3 * hclen)) cl 0 all j ∧ valid_spec lit 15 true ∧ valid_spec dist 15 true) → (valid_pre lit 15)) ∧
      (∀ hclen : ℤ, ∀ cl : List U8, ∀ all : List U8, ((∃ v_call0 : ℤ, field_spec s i 5 v_call0 ∧ (lit.length : ℤ) = (257 + v_call0)) ∧ (∃ v_call1 : ℤ, field_spec s (i + 5) 5 v_call1 ∧ (dist.length : ℤ) = (1 + v_call1)) ∧ (∃ v_call2 : ℤ, field_spec s (i + 10) 4 v_call2 ∧ hclen = (4 + v_call2)) ∧ (cl.length : ℤ) = 19 ∧ (∀ k : ℤ, 0 ≤ k → k < 19 → ((k < hclen → (∃ v_out3 : ℤ, field_spec s ((i + 14) + (3 * k)) 3 v_out3 ∧ v_out3 = ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ))) ∧ (¬(k < hclen) → ((cl[([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8][k.toNat]!).val]!).val : ℤ) = 0))) ∧ valid_spec cl 7 true ∧ (all.length : ℤ) = ((lit.length : ℤ) + (dist.length : ℤ)) ∧ ((all.drop 0).take ((lit.length : ℤ)).toNat) = lit ∧ ((all.drop ((lit.length : ℤ)).toNat).take ((all.length : ℤ) - (lit.length : ℤ)).toNat) = dist ∧ lengths_spec s ((i + 14) + (3 * hclen)) cl 0 all j ∧ valid_spec lit 15 true ∧ valid_spec dist 15 true) → (valid_pre dist 15)) := by
  intro s i lit dist j h
  simp only [field_pre, valid_pre, lengths_pre, List.length_cons, List.length_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; norm_num
  · intros; norm_num
  · intros; norm_num
  · intro hclen cl all hh k hk hk' hc
    have hl := hh.2.2.2.1
    have hb := cl_order_bounds k hk hk'
    split_conjs <;> omega
  · intro hclen cl all hh k hk hk' hc
    have hl := hh.2.2.2.1
    have hb := cl_order_bounds k hk hk'
    omega
  · intros; norm_num
  · intro hclen cl all hh
    have hl := hh.2.2.2.2.2.2.1
    omega
  · intro hclen cl all hh
    have hl := hh.2.2.2.2.2.2.1
    omega
  · intro hclen cl all hh
    omega
  · intros; norm_num
  · intros; norm_num

/-! ## block -/

theorem block.wf :
    ∀ (s : List U8) (i : ℤ) (prev : List U8) (out : List U8) (j : ℤ),
      block_spec s i prev out j →
      ((field_pre s i 2)) ∧
      (¬(field_spec s i 2 0) → (field_pre s i 2)) ∧
      (¬(field_spec s i 2 0) → ¬(field_spec s i 2 1) → (field_pre s i 2)) := by
  intros
  simp [field_pre]

/-! ## blocks -/

/-! ## xor -/

theorem xor.ens_0 :
    ∀ (a : ℤ) (b : ℤ) (c : ℤ),
      xor_spec a b c → 0 ≤ c := by
  intro a b c h
  rw [xor_spec] at h
  obtain ⟨hp, hh⟩ := h
  have hab : 0 ≤ a ∧ 0 ≤ b := hp
  specialize hh hab
  by_cases hz : a = 0 ∧ b = 0
  · have := hh.1 hz
    omega
  · obtain ⟨x, hx, he⟩ := hh.2 hz
    have hn := xor.ens_0 (a / 2) (b / 2) x hx
    have hm := Int.emod_nonneg (a + b) (by norm_num : (2 : ℤ) ≠ 0)
    omega
termination_by a b _ _ => (a + b).toNat
decreasing_by simp_wf; simp only [xor_pre] at *; omega

theorem xor.wf :
    ∀ (a : ℤ) (b : ℤ) (c : ℤ),
      xor_spec a b c →
      (¬((a = 0 ∧ b = 0)) → (2 ≠ 0) ∧ (2 ≠ 0) ∧ (xor_pre (a / 2) (b / 2))) ∧
      (¬((a = 0 ∧ b = 0)) → ∀ v_call0 : ℤ, xor_spec (a / 2) (b / 2) v_call0 → (2 ≠ 0)) := by
  intro a b c h
  rw [xor_spec] at h
  simp only [xor_pre] at *
  split_conjs <;> intros <;> omega

/-! ## crcbit -/

theorem crcbit.ens_0 :
    ∀ (c : ℤ) (d : ℤ),
      crcbit_spec c d → 0 ≤ d := by
  intro c d h
  obtain ⟨hc, ht, hf⟩ := h
  simp only [crcbit_pre] at hc
  by_cases hp : c % 2 = 1
  · exact xor.ens_0 _ _ _ (ht hp)
  · have := hf hp
    omega

theorem crcbit.wf :
    ∀ (c : ℤ) (d : ℤ),
      crcbit_spec c d →
      ((2 ≠ 0)) ∧
      ((c % 2) = 1 → (2 ≠ 0) ∧ (xor_pre (c / 2) 3988292384)) ∧
      (¬((c % 2) = 1) → (2 ≠ 0)) := by
  intro c d h
  obtain ⟨hc, _⟩ := h
  simp only [crcbit_pre] at hc
  simp only [xor_pre]
  split_conjs <;> intros <;> omega

/-! ## crcbits -/

theorem crcbits.ens_0 :
    ∀ (c : ℤ) (n : ℤ) (d : ℤ),
      crcbits_spec c n d → 0 ≤ d := by
  intro c n d h
  rw [crcbits_spec] at h
  obtain ⟨hp, hh⟩ := h
  have hc : 0 ≤ c ∧ 0 ≤ n := hp
  specialize hh hc
  by_cases hz : n = 0
  · have := hh.1 hz
    omega
  · obtain ⟨v, _, hd⟩ := hh.2 hz
    exact crcbit.ens_0 v d hd

theorem crcbits.wf :
    ∀ (c : ℤ) (n : ℤ) (d : ℤ),
      crcbits_spec c n d →
      (¬(n = 0) → (crcbits_pre c (n - 1))) ∧
      (¬(n = 0) → ∀ v_call0 : ℤ, crcbits_spec c (n - 1) v_call0 → (crcbit_pre v_call0)) := by
  intro c n d h
  rw [crcbits_spec] at h
  simp only [crcbits_pre, crcbit_pre] at *
  exact ⟨by intros; omega, fun _ v hv => crcbits.ens_0 c (n - 1) v hv⟩

/-! ## crcreg -/

theorem crcreg.ens_0 :
    ∀ (data : List U8) (n : ℤ) (c : ℤ),
      crcreg_spec data n c → 0 ≤ c := by
  intro data n c h
  rw [crcreg_spec] at h
  obtain ⟨hp, hh⟩ := h
  have hn : 0 ≤ n ∧ n ≤ (data.length : ℤ) := hp
  specialize hh hn
  by_cases hz : n = 0
  · have := hh.1 hz
    omega
  · obtain ⟨v, _, x, _, hc⟩ := hh.2 hz
    exact crcbits.ens_0 x 8 c hc

theorem crcreg.wf :
    ∀ (data : List U8) (n : ℤ) (c : ℤ),
      crcreg_spec data n c →
      (¬(n = 0) → (crcreg_pre data (n - 1))) ∧
      (¬(n = 0) → ∀ v_call0 : ℤ, crcreg_spec data (n - 1) v_call0 → (0 ≤ (n - 1) ∧ (n - 1) < (data.length : ℤ)) ∧ (xor_pre v_call0 ((data[(n - 1).toNat]!).val : ℤ))) ∧
      (¬(n = 0) → ∀ v_call0 : ℤ, crcreg_spec data (n - 1) v_call0 → ∀ v_call1 : ℤ, xor_spec v_call0 ((data[(n - 1).toNat]!).val : ℤ) v_call1 → (crcbits_pre v_call1 8)) := by
  intro data n c h
  rw [crcreg_spec] at h
  have hn : 0 ≤ n ∧ n ≤ (data.length : ℤ) := h.1
  simp only [crcreg_pre, xor_pre, crcbits_pre]
  refine ⟨by intros; omega, ?_, ?_⟩
  · intro hz v hv
    have hpos := crcreg.ens_0 data (n - 1) v hv
    split_conjs <;> omega
  · intro hz v hv x hx
    have hpos := xor.ens_0 v _ x hx
    omega

/-! ## crc32 -/


theorem xor_unique (a b x y : ℤ) (hx : xor_spec a b x) (hy : xor_spec a b y) : x = y := by
  rw [xor_spec] at hx hy
  have hp : 0 ≤ a ∧ 0 ≤ b := hx.1
  have hxx := hx.2 hp
  have hyy := hy.2 hp
  by_cases hz : a = 0 ∧ b = 0
  · exact (hxx.1 hz).trans (hyy.1 hz).symm
  · obtain ⟨v, hv, he⟩ := hxx.2 hz
    obtain ⟨w, hw, hf⟩ := hyy.2 hz
    have := xor_unique (a / 2) (b / 2) v w hv hw
    omega
termination_by (a + b).toNat
decreasing_by simp_wf; simp only [xor_pre] at *; omega

theorem crcbit_unique (c x y : ℤ) (hx : crcbit_spec c x) (hy : crcbit_spec c y) : x = y := by
  by_cases hp : c % 2 = 1
  · exact xor_unique _ _ _ _ (hx.2.1 hp) (hy.2.1 hp)
  · exact (hx.2.2 hp).trans (hy.2.2 hp).symm

theorem crcbits_unique (c n x y : ℤ) (hx : crcbits_spec c n x) (hy : crcbits_spec c n y) : x = y := by
  rw [crcbits_spec] at hx hy
  have hp : 0 ≤ c ∧ 0 ≤ n := hx.1
  have hxx := hx.2 hp
  have hyy := hy.2 hp
  by_cases hz : n = 0
  · exact (hxx.1 hz).trans (hyy.1 hz).symm
  · obtain ⟨v, hv, he⟩ := hxx.2 hz
    obtain ⟨w, hw, hf⟩ := hyy.2 hz
    have h := crcbits_unique c (n - 1) v w hv hw
    subst w
    exact crcbit_unique _ _ _ he hf
termination_by n.toNat
decreasing_by simp_wf; simp only [crcbits_pre] at *; omega

theorem crcreg_unique (data : List U8) (n x y : ℤ)
    (hx : crcreg_spec data n x) (hy : crcreg_spec data n y) : x = y := by
  rw [crcreg_spec] at hx hy
  have hp : 0 ≤ n ∧ n ≤ (data.length : ℤ) := hx.1
  have hxx := hx.2 hp
  have hyy := hy.2 hp
  by_cases hz : n = 0
  · exact (hxx.1 hz).trans (hyy.1 hz).symm
  · obtain ⟨v, hv, q, hq, he⟩ := hxx.2 hz
    obtain ⟨w, hw, r, hr, hf⟩ := hyy.2 hz
    have h := crcreg_unique data (n - 1) v w hv hw
    subst w
    have h := xor_unique _ _ _ _ hq hr
    subst r
    exact crcbits_unique _ _ _ _ he hf
termination_by n.toNat
decreasing_by simp_wf; simp only [crcreg_pre] at *; omega

theorem crc32.unambiguous :
    ∀ (data : List U8) (o₁ : U32) (o₂ : U32),
      crc32_spec data o₁ → crc32_spec data o₂ → o₁ = o₂ := by
  intro data x y hx hy
  obtain ⟨_, v, hv, q, hq, he⟩ := hx
  obtain ⟨_, w, hw, r, hr, hf⟩ := hy
  have h := crcreg_unique data _ v w hv hw
  subst w
  have h := xor_unique _ _ _ _ hq hr
  scalar_tac

theorem crc32.wf :
    ∀ (data : List U8) (c : U32),
      crc32_spec data c →
      ((crcreg_pre data (data.length : ℤ))) ∧
      (∀ v_call0 : ℤ, crcreg_spec data (data.length : ℤ) v_call0 → (xor_pre v_call0 4294967295)) := by
  intro data c h
  simp only [crcreg_pre, xor_pre]
  exact ⟨by omega, fun v hv => ⟨crcreg.ens_0 data _ v hv, by norm_num⟩⟩

theorem crc32.impl_correct :
    ∀ (data : Aeneas.Std.Slice U8), crc32_pre data.val →
      Gzip.spec.crc32 data ⦃ c => crc32_spec data.val c ⦄ := by
  intro data _
  unfold Gzip.spec.crc32
  exact Crc.correct data

/-! ## flag -/

theorem flag.wf :
    ∀ (f : ℤ) (k : ℤ) (b : Bool),
      flag_spec f k b →
      (0 ≤ k) ∧ ((2 ^ (k).toNat) ≠ 0) ∧ (2 ≠ 0) := by
  intro f k b h
  exact ⟨h.1, pow_ne_zero _ (by norm_num), by norm_num⟩

/-! ## zero -/

theorem zero.wf :
    ∀ (s : List U8) (i : ℤ) (z : ℤ),
      zero_spec s i z →
      ((0 ≤ z ∧ z < (s.length : ℤ))) ∧
      (∀ k : ℤ, i ≤ k → k < z → (0 ≤ k ∧ k < (s.length : ℤ))) := by
  intro s i z h
  obtain ⟨_, hi, _⟩ := h
  split_conjs <;> intros <;> omega

/-! ## header -/

theorem header.wf :
    ∀ (s : List U8) (n : ℤ),
      header_spec s n →
      ((0 < (s.length : ℤ))) ∧
      (((s[0]!).val : ℤ) = 31 → (1 < (s.length : ℤ))) ∧
      ((((s[0]!).val : ℤ) = 31 ∧ ((s[1]!).val : ℤ) = 139) → (2 < (s.length : ℤ))) ∧
      ((3 < (s.length : ℤ))) ∧
      (∀ a : ℤ, ∀ b : ℤ, ∀ c : ℤ, (((flag_spec ((s[3]!).val : ℤ) 2 true → (∃ v_call0 : ℤ, u16le_spec s 10 v_call0 ∧ a = (12 + v_call0))) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 2 true) → a = 10)) ∧ ((flag_spec ((s[3]!).val : ℤ) 3 true → (∃ v_call1 : ℤ, zero_spec s a v_call1 ∧ b = (v_call1 + 1))) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 3 true) → b = a)) ∧ ((flag_spec ((s[3]!).val : ℤ) 4 true → (∃ v_call2 : ℤ, zero_spec s b v_call2 ∧ c = (v_call2 + 1))) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 4 true) → c = b)) ∧ ((flag_spec ((s[3]!).val : ℤ) 1 true → n = (c + 2)) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 1 true) → n = c)) ∧ n ≤ (s.length : ℤ)) → (3 < (s.length : ℤ)) ∧ (flag_pre ((s[3]!).val : ℤ) 2)) ∧
      (∀ a : ℤ, ∀ b : ℤ, ∀ c : ℤ, (((flag_spec ((s[3]!).val : ℤ) 2 true → (∃ v_call0 : ℤ, u16le_spec s 10 v_call0 ∧ a = (12 + v_call0))) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 2 true) → a = 10)) ∧ ((flag_spec ((s[3]!).val : ℤ) 3 true → (∃ v_call1 : ℤ, zero_spec s a v_call1 ∧ b = (v_call1 + 1))) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 3 true) → b = a)) ∧ ((flag_spec ((s[3]!).val : ℤ) 4 true → (∃ v_call2 : ℤ, zero_spec s b v_call2 ∧ c = (v_call2 + 1))) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 4 true) → c = b)) ∧ ((flag_spec ((s[3]!).val : ℤ) 1 true → n = (c + 2)) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 1 true) → n = c)) ∧ n ≤ (s.length : ℤ)) → (3 < (s.length : ℤ)) ∧ (flag_pre ((s[3]!).val : ℤ) 3)) ∧
      (∀ a : ℤ, ∀ b : ℤ, ∀ c : ℤ, (((flag_spec ((s[3]!).val : ℤ) 2 true → (∃ v_call0 : ℤ, u16le_spec s 10 v_call0 ∧ a = (12 + v_call0))) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 2 true) → a = 10)) ∧ ((flag_spec ((s[3]!).val : ℤ) 3 true → (∃ v_call1 : ℤ, zero_spec s a v_call1 ∧ b = (v_call1 + 1))) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 3 true) → b = a)) ∧ ((flag_spec ((s[3]!).val : ℤ) 4 true → (∃ v_call2 : ℤ, zero_spec s b v_call2 ∧ c = (v_call2 + 1))) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 4 true) → c = b)) ∧ ((flag_spec ((s[3]!).val : ℤ) 1 true → n = (c + 2)) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 1 true) → n = c)) ∧ n ≤ (s.length : ℤ)) → (3 < (s.length : ℤ)) ∧ (flag_pre ((s[3]!).val : ℤ) 4)) ∧
      (∀ a : ℤ, ∀ b : ℤ, ∀ c : ℤ, (((flag_spec ((s[3]!).val : ℤ) 2 true → (∃ v_call0 : ℤ, u16le_spec s 10 v_call0 ∧ a = (12 + v_call0))) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 2 true) → a = 10)) ∧ ((flag_spec ((s[3]!).val : ℤ) 3 true → (∃ v_call1 : ℤ, zero_spec s a v_call1 ∧ b = (v_call1 + 1))) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 3 true) → b = a)) ∧ ((flag_spec ((s[3]!).val : ℤ) 4 true → (∃ v_call2 : ℤ, zero_spec s b v_call2 ∧ c = (v_call2 + 1))) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 4 true) → c = b)) ∧ ((flag_spec ((s[3]!).val : ℤ) 1 true → n = (c + 2)) ∧ (¬(flag_spec ((s[3]!).val : ℤ) 1 true) → n = c)) ∧ n ≤ (s.length : ℤ)) → (3 < (s.length : ℤ)) ∧ (flag_pre ((s[3]!).val : ℤ) 1)) := by
  intro s n h
  have hn := h.2.1
  simp only [flag_pre]
  split_conjs <;> intros <;> omega

/-! ## member -/

theorem member.wf :
    ∀ (s : List U8) (out : List U8),
      member_spec s out →
      (∀ h : ℤ, ∀ j : ℤ, ∀ t : ℤ, (header_spec s h ∧ blocks_spec s (8 * h) ([] : List U8) out j ∧ t = ((j + 7) / 8) ∧ (s.length : ℤ) = (t + 8) ∧ (∃ v_call0 : U32, crc32_spec out v_call0 ∧ (∃ v_out1 : ℤ, u32le_spec s t v_out1 ∧ v_out1 = (v_call0.val : ℤ))) ∧ u32le_spec s (t + 4) ((out.length : ℤ) % 4294967296)) → (8 ≠ 0)) ∧
      (∀ h : ℤ, ∀ j : ℤ, ∀ t : ℤ, (header_spec s h ∧ blocks_spec s (8 * h) ([] : List U8) out j ∧ t = ((j + 7) / 8) ∧ (s.length : ℤ) = (t + 8) ∧ (∃ v_call0 : U32, crc32_spec out v_call0 ∧ (∃ v_out1 : ℤ, u32le_spec s t v_out1 ∧ v_out1 = (v_call0.val : ℤ))) ∧ u32le_spec s (t + 4) ((out.length : ℤ) % 4294967296)) → (4294967296 ≠ 0)) := by
  intros
  constructor <;> intros <;> norm_num

/-! ## decompress -/

theorem decompress.wf :
    ∀ (s : List U8) (r : Option (List U8)),
      decompress_spec s r →
      r.isSome = true → (r.isSome = true) := by
  intros
  assumption

/-! ## compress -/

theorem compress.unambiguous :
    ∀ (data : List U8) (level : U8) (o : (List U8) → U8 → List U8) (o₁ : List U8) (o₂ : List U8),
      compress_body data level o o₁ → compress_body data level o o₂ → o₁ = o₂ := by
  intro data level o a b ha hb
  exact ha.2.2.1.trans hb.2.2.1.symm

theorem compress.ens_0 :
    ∀ (data : List U8) (level : U8) (out : List U8),
      compress_spec data level out → (∃ v_out1 : Option (List U8), decompress_spec out v_out1 ∧ v_out1 = (some data)) := by
  intro data level out h
  obtain ⟨o, hpre, hr, heq, _⟩ := h
  rw [heq]
  exact hr

theorem compress.wf :
    ∀ (data : List U8) (level : U8) (o : (List U8) → U8 → List U8) (out : List U8),
      compress_body data level o out →
      ((0 ≤ 0 ∧ 0 ≤ 8 ∧ 8 ≤ (out.length : ℤ))) ∧
      ((8 < (out.length : ℤ))) ∧
      ((9 < (out.length : ℤ))) := by
  intro data level o out h
  have hn := h.2.2.2.1
  omega

/-! ## obligations added by a later `translate` (specification changed) -/

theorem compress.impl_correct :
    ∀ (data : Aeneas.Std.Slice U8) (level : U8), compress_pre data.val level →
      Gzip.spec.compress data level ⦃ out => compress_spec data.val level out.val ⦄ := by
  intro data level hp
  unfold Gzip.spec.compress
  exact Runtime.correct data level hp

/-! ## decompress (the decoder, merged from example/gzip-decompress) -/

theorem guard_and (p q : Prop) : (p ∧ (p → q)) ↔ p ∧ q := by tauto

theorem xor_decreases (a b : ℤ) (hp : 0 ≤ a ∧ 0 ≤ b) (hz : ¬(a = 0 ∧ b = 0)) :
    (a / 2 + b / 2).toNat < (a + b).toNat := by omega

theorem decompress.unambiguous :
    ∀ (s : List U8) (o₁ : Option (List U8)) (o₂ : Option (List U8)),
      decompress_spec s o₁ → decompress_spec s o₂ → o₁ = o₂ := by
  intro s x y hx hy
  exact Decode.Decoding.decompress_unique_of_member_unique s (Decode.Parsing.member_unique s) x y hx hy

theorem decompress.impl_correct :
    ∀ (s : Aeneas.Std.Slice U8), decompress_pre s.val →
      Gzip.spec.decompress s ⦃ r => decompress_spec s.val r ⦄ := by
  intro s _
  unfold Gzip.spec.decompress
  apply WP.spec_mono (Decode.DecompressImpl.decompress_correct crc32.unambiguous s)
  intro res hr
  cases res <;> exact Decode.DecompressImpl.dec_post_spec s.val _ hr

end Gzip.Proofs
