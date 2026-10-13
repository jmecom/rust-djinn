import Gzip.Proofs.Matches

open Aeneas Std Result
open Gzip.solution

namespace Gzip.Proofs.Chains

/-- The match finder's tables: a nonempty head table and the link table of 65536 entries (the
hash chains of the greedy levels use its first half, the binary tree of the optimal levels all
of it). Their contents are only a guide: every candidate is checked where it is used, so the
invariant is just the sizes; the position argument is kept for the callers' convenience. -/
def Tables (head : List U32) (chain : List U32) (_p : ℕ) : Prop :=
  0 < head.length ∧ chain.length = 65536

/-- The tables at a level: level 1 follows no links and has no link table, so only its head
table counts there. -/
def LTables (level : ℕ) (head : List U32) (chain : List U32) (p : ℕ) : Prop :=
  0 < head.length ∧ (level = 1 ∨ chain.length = 65536)

theorem ltables_of_tables {level : ℕ} {head chain : List U32} {p : ℕ} (h : Tables head chain p) :
    LTables level head chain p := ⟨h.1, Or.inr h.2⟩

theorem tables_of_ltables {level : ℕ} {head chain : List U32} {p : ℕ} (h : LTables level head chain p)
    (hl : level ≠ 1) : Tables head chain p := ⟨h.1, h.2.resolve_left hl⟩

theorem tables_advance {head : List U32} {chain : List U32} {p : ℕ} (h : Tables head chain p) :
    Tables head chain (p + 1) := h

theorem tables_advance_to {head : List U32} {chain : List U32} {p next : ℕ}
    (h : Tables head chain p) (_hp : p ≤ next) : Tables head chain next := h

theorem tables_set {head : List U32} {chain : List U32} {p q : ℕ} (h : Tables head chain p)
    (i j : ℕ) (x : U32) (y : U32) : Tables (head.set i x) (chain.set j y) q := by
  obtain ⟨hh, hc⟩ := h
  exact ⟨by simpa using hh, by simpa using hc⟩

theorem tables_set_chain {head : List U32} {chain : List U32} {p q : ℕ} (h : Tables head chain p)
    (j : ℕ) (y : U32) : Tables head (chain.set j y) q := by
  obtain ⟨hh, hc⟩ := h
  exact ⟨hh, by simpa using hc⟩

theorem get_set (xs : List Usize) (i k : ℕ) (x : Usize) (hk : k < xs.length) :
    (xs.set i x)[k]! = if i = k then x else xs[k]! := by
  rw [getElem!_pos (xs.set i x) k (by simpa using hk), List.getElem_set,
    getElem!_pos xs k hk]

@[step]
theorem insert_hashed (data : Aeneas.Std.Slice U8) (h p : Usize)
    (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32) (hp : p.val < data.val.length)
    (ht : Tables head.val chain.val p.val) :
    Gzip.solution.insert_hashed h p head chain ⦃ r => Tables r.1.val r.2.val (p.val + 1) ⦄ := by
  obtain ⟨hhead, hchain⟩ := ht
  have hslot : (p &&& 32767#usize).val < chain.val.length := by
    rw [UScalar.val_and]
    change p.val &&& 32767 < chain.val.length
    rw [hchain]
    have hmask : p.val &&& 32767 ≤ 32767 := Nat.and_le_right
    omega
  unfold Gzip.solution.insert_hashed
  dsimp only
  split
  · have hhash : h.val < head.val.length := by scalar_tac
    step*
    rw [index_mut_back1_post, index_mut_back_post]
    simp only [alloc.vec.Vec.set_val_eq]
    exact ⟨by simpa using hhead, by simpa using hchain⟩
  · step*
    exact ⟨hhead, hchain⟩

@[step]
theorem insert (data : Aeneas.Std.Slice U8) (p : Usize)
    (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32) (four : Bool) (hp : p.val < data.val.length)
    (ht : Tables head.val chain.val p.val) :
    Gzip.solution.insert data p head chain four ⦃ r => Tables r.1.val r.2.val (p.val + 1) ⦄ := by
  have hhead := ht.1
  have hp' : p.val ≤ data.val.length := by omega
  unfold Gzip.solution.insert
  step*

@[step]
theorem insert_at (data : Aeneas.Std.Slice U8) (p : Usize)
    (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32) (level : U8) (four : Bool)
    (hp : p.val < data.val.length) (ht : Tables head.val chain.val p.val) :
    Gzip.solution.insert_at data p head chain level four ⦃ r => Tables r.1.val r.2.val (p.val + 1) ⦄ := by
  have hhead := ht.1
  have hchain := ht.2
  have hp' : p.val ≤ data.val.length := by omega
  unfold Gzip.solution.insert_at
  split
  · step*
  · step as ⟨h, _⟩
    split
    · have hhash : h.val < head.val.length := by scalar_tac
      step*
      rw [index_mut_back_post]
      simp only [alloc.vec.Vec.set_val_eq]
      exact ⟨by simpa using hhead, hchain⟩
    · step*
      exact ⟨hhead, hchain⟩

@[step]
theorem zeros_correct (n : Usize) :
    zeros n ⦃ out => out.val = List.replicate n.val 0#usize ⦄ := by
  unfold zeros
  have hr := alloc.vec.Vec.resize_spec core.clone.CloneUsize (alloc.vec.Vec.new Usize) n 0#usize
    (by rfl)
  step as ⟨v, hv⟩
  rw [hv]
  unfold List.resize
  simp [alloc.vec.Vec.new]

@[step]
theorem zeros_u32_correct (n : Usize) :
    zeros_u32 n ⦃ out => out.val = List.replicate n.val 0#u32 ⦄ := by
  unfold zeros_u32
  have hr := alloc.vec.Vec.resize_spec core.clone.CloneU32 (alloc.vec.Vec.new U32) n 0#u32
    (by rfl)
  step as ⟨v, hv⟩
  rw [hv]
  unfold List.resize
  simp [alloc.vec.Vec.new]

theorem initial_tables (n : ℕ) (hn : 0 < n) :
    Tables (List.replicate n 0#u32) (List.replicate 65536 0#u32) 0 :=
  ⟨by simpa only [List.length_replicate] using hn, by rw [List.length_replicate]⟩

end Gzip.Proofs.Chains
