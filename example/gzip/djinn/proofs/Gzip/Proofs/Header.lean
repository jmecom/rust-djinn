import Gzip.Proofs.Dyn
import Mathlib.Tactic.IntervalCases

open Aeneas Std Result
open Gzip.Spec Gzip.Proofs.Writer Gzip.Proofs.Codes Gzip.Proofs.Dyn

set_option maxHeartbeats 2000000

namespace Gzip.Proofs.Header

/-- The extra bits of a run-length symbol. -/
def extraWidth (sym : ℕ) : ℕ :=
  if sym = 16 then 2 else if sym = 17 then 3 else if sym = 18 then 7 else 0

def itemBits (cl : Tab) (sym e : ℕ) : List Bool :=
  encodeSym cl.lens cl.words sym ++ lowBits e (extraWidth sym)

def itemsBits (cl : Tab) : List Usize → List Usize → List Bool
  | s :: ss, e :: es => itemBits cl s.val e.val ++ itemsBits cl ss es
  | _, _ => []

@[simp] theorem itemsBits_nil (cl : Tab) : itemsBits cl [] [] = [] := rfl

@[simp] theorem itemsBits_cons (cl : Tab) (s e : Usize) (ss es : List Usize) :
    itemsBits cl (s :: ss) (e :: es) = itemBits cl s.val e.val ++ itemsBits cl ss es := rfl

@[simp] theorem itemsBits_nil_left (cl : Tab) (es : List Usize) : itemsBits cl [] es = [] := by
  cases es <;> rfl

@[simp] theorem itemsBits_nil_right (cl : Tab) (ss : List Usize) : itemsBits cl ss [] = [] := by
  cases ss <;> rfl

theorem itemsBits_append (cl : Tab) (s1 s2 e1 e2 : List Usize) (h : s1.length = e1.length) :
    itemsBits cl (s1 ++ s2) (e1 ++ e2) = itemsBits cl s1 e1 ++ itemsBits cl s2 e2 := by
  induction s1 generalizing e1 with
  | nil =>
      cases e1 with
      | nil => simp
      | cons _ _ => simp at h
  | cons s ss ih =>
      cases e1 with
      | nil => simp at h
      | cons e es =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h
          simp only [List.cons_append, itemsBits_cons, ih es h, List.append_assoc]

/-- Run-length items that cover the lengths from `p` on (§3.2.7): a length below 16, a repeat
    of the previous length 3–6 times, 3–10 zeros, 11–138 zeros. -/
inductive Covers (all : List U8) : ℕ → List Usize → List Usize → Prop
  | nil : Covers all all.length [] []
  | lit (p : ℕ) (sym e : Usize) (ss es : List Usize) (hp : p < all.length) (hs : sym.val < 16)
      (he : (all[p]!).val = sym.val) (tail : Covers all (p + 1) ss es) :
      Covers all p (sym :: ss) (e :: es)
  | rep (p : ℕ) (sym e : Usize) (ss es : List Usize) (hs : sym.val = 16) (hp : 1 ≤ p)
      (he : e.val < 4) (hn : p + 3 + e.val ≤ all.length)
      (hall : ∀ k, p ≤ k → k < p + 3 + e.val → all[k]! = all[p - 1]!)
      (tail : Covers all (p + 3 + e.val) ss es) :
      Covers all p (sym :: ss) (e :: es)
  | zeros (p : ℕ) (sym e : Usize) (ss es : List Usize) (hs : sym.val = 17)
      (he : e.val < 8) (hn : p + 3 + e.val ≤ all.length)
      (hz : ∀ k, p ≤ k → k < p + 3 + e.val → (all[k]!).val = 0)
      (tail : Covers all (p + 3 + e.val) ss es) :
      Covers all p (sym :: ss) (e :: es)
  | zeros2 (p : ℕ) (sym e : Usize) (ss es : List Usize) (hs : sym.val = 18)
      (he : e.val < 128) (hn : p + 11 + e.val ≤ all.length)
      (hz : ∀ k, p ≤ k → k < p + 11 + e.val → (all[k]!).val = 0)
      (tail : Covers all (p + 11 + e.val) ss es) :
      Covers all p (sym :: ss) (e :: es)

theorem covers_lengths {all : List U8} {p : ℕ} {ss es : List Usize} (h : Covers all p ss es) :
    ss.length = es.length := by
  induction h <;> simp_all

/-- Every item's symbol has a codeword in the code-length code. -/
def Usable (cl : List U8) (ss : List Usize) : Prop :=
  ∀ s ∈ ss, s.val < cl.length ∧ 1 ≤ (cl[s.val]!).val

theorem covers_decode {all : List U8} {p : ℕ} {ss es : List Usize} (cl : Tab)
    (hcl : TableOk cl.lens cl.words 7)
    (h : Covers all p ss es) (hu : Usable cl.lens ss) (s : List U8) (front tail : List Bool)
    (hs : byteBits s = front ++ itemsBits cl ss es ++ tail) :
    lengths_spec s front.length cl.lens p all (front.length + (itemsBits cl ss es).length) := by
  induction h generalizing front with
  | nil =>
      rw [lengths_spec]
      refine ⟨⟨by omega, by omega⟩, fun _ => ⟨fun _ => by simp, fun hne => absurd rfl hne⟩⟩
  | lit p sym e ss es hp hsym he htail ih =>
      have hu' : Usable cl.lens ss := fun x hx => hu x (List.mem_cons_of_mem _ hx)
      obtain ⟨hs19, hpos⟩ := hu sym (List.mem_cons_self ..)
      have hw0 : extraWidth sym.val = 0 := by unfold extraWidth; split_ifs <;> omega
      have hsymbol := symbol_decode s front
        (lowBits e.val (extraWidth sym.val) ++ itemsBits cl ss es ++ tail) cl.lens cl.words 7
        sym.val hcl hs19 hpos (by simpa only [itemsBits_cons, itemBits, List.append_assoc] using hs)
      have hih := ih hu' (front ++ itemBits cl sym.val e.val)
        (by simpa only [itemsBits_cons, List.append_assoc] using hs)
      have hlen : (front ++ itemBits cl sym.val e.val).length =
          front.length + (cl.lens[sym.val]!).val := by
        simp only [List.length_append, itemBits, encodeSym_length, lowBits_length, hw0] <;> omega
      rw [lengths_spec]
      refine ⟨⟨by omega, by omega⟩, fun _ => ⟨fun heq => by omega, fun _ => ?_⟩⟩
      refine ⟨sym.val, (front ++ itemBits cl sym.val e.val).length, 1, hsymbol, fun _ => ⟨?_, fun _ => ?_⟩⟩
      · rw [hlen]
        simp only [Int.toNat_natCast, Nat.cast_add]
      · refine ⟨fun _ => ⟨rfl, fun _ => ⟨?_, fun _ => ?_⟩⟩, fun hn => absurd (by exact_mod_cast hsym) hn⟩
        · intro k hk1 hk2
          have hkp : k.toNat = p := by omega
          rw [hkp]
          exact_mod_cast he
        · have hj : (front.length : ℤ) + ((itemsBits cl (sym :: ss) (e :: es)).length : ℕ) =
              ((front ++ itemBits cl sym.val e.val).length + (itemsBits cl ss es).length : ℕ) := by
            simp only [itemsBits_cons, List.length_append]
            push_cast
            ring
          rw [hj]
          convert hih using 2 <;> simp only [hlen, Nat.cast_add] <;> ring
  | rep p sym e ss es hsym hp he hn hall htail ih =>
      have hu' : Usable cl.lens ss := fun x hx => hu x (List.mem_cons_of_mem _ hx)
      obtain ⟨hs19, hpos⟩ := hu sym (List.mem_cons_self ..)
      have hw : extraWidth sym.val = 2 := by unfold extraWidth; split_ifs <;> omega
      have hsymbol := symbol_decode s front
        (lowBits e.val (extraWidth sym.val) ++ itemsBits cl ss es ++ tail) cl.lens cl.words 7
        sym.val hcl hs19 hpos (by simpa only [itemsBits_cons, itemBits, List.append_assoc] using hs)
      have hfield := field_at_prefix s (front ++ encodeSym cl.lens cl.words sym.val)
        (itemsBits cl ss es ++ tail) e.val 2
        (by simpa only [itemsBits_cons, itemBits, hw, List.append_assoc] using hs) (by omega)
      simp only [List.length_append, encodeSym_length, Nat.cast_add] at hfield
      have hih := ih hu' (front ++ itemBits cl sym.val e.val)
        (by simpa only [itemsBits_cons, List.append_assoc] using hs)
      have hlen : (front ++ itemBits cl sym.val e.val).length =
          front.length + (cl.lens[sym.val]!).val + 2 := by
        simp only [List.length_append, itemBits, encodeSym_length, lowBits_length, hw] <;> omega
      rw [lengths_spec]
      refine ⟨⟨by omega, by omega⟩, fun _ => ⟨fun heq => by omega, fun _ => ?_⟩⟩
      refine ⟨sym.val, front.length + (cl.lens[sym.val]!).val, 3 + e.val, hsymbol,
        fun _ => ⟨by simp only [Int.toNat_natCast, Nat.cast_add], fun _ => ?_⟩⟩
      refine ⟨fun h16 => by omega, fun _ => ⟨fun _ => ?_, fun hn => absurd (by exact_mod_cast hsym) hn⟩⟩
      refine ⟨by omega, fun _ => ⟨⟨e.val, hfield, by push_cast; ring⟩, fun _ => ⟨⟨by omega, by omega⟩, fun _ => ⟨?_, fun _ => ?_⟩⟩⟩⟩
      · intro k hk1 hk2
        have hkp : (p : ℤ) - 1 = ((p - 1 : ℕ) : ℤ) := by omega
        rw [hkp, Int.toNat_natCast]
        exact hall k.toNat (by omega) (by omega)
      · have hj : (front.length : ℤ) + ((itemsBits cl (sym :: ss) (e :: es)).length : ℕ) =
            ((front ++ itemBits cl sym.val e.val).length + (itemsBits cl ss es).length : ℕ) := by
          simp only [itemsBits_cons, List.length_append]
          push_cast
          ring
        rw [hj]
        have hpn : (p : ℤ) + (3 + (e.val : ℤ)) = ((p + 3 + e.val : ℕ) : ℤ) := by push_cast; ring
        rw [hpn]
        convert hih using 2 <;> simp only [hlen, Nat.cast_add] <;> ring
  | zeros p sym e ss es hsym he hn hz htail ih =>
      have hu' : Usable cl.lens ss := fun x hx => hu x (List.mem_cons_of_mem _ hx)
      obtain ⟨hs19, hpos⟩ := hu sym (List.mem_cons_self ..)
      have hw : extraWidth sym.val = 3 := by unfold extraWidth; split_ifs <;> omega
      have hsymbol := symbol_decode s front
        (lowBits e.val (extraWidth sym.val) ++ itemsBits cl ss es ++ tail) cl.lens cl.words 7
        sym.val hcl hs19 hpos (by simpa only [itemsBits_cons, itemBits, List.append_assoc] using hs)
      have hfield := field_at_prefix s (front ++ encodeSym cl.lens cl.words sym.val)
        (itemsBits cl ss es ++ tail) e.val 3
        (by simpa only [itemsBits_cons, itemBits, hw, List.append_assoc] using hs) (by omega)
      simp only [List.length_append, encodeSym_length, Nat.cast_add] at hfield
      have hih := ih hu' (front ++ itemBits cl sym.val e.val)
        (by simpa only [itemsBits_cons, List.append_assoc] using hs)
      have hlen : (front ++ itemBits cl sym.val e.val).length =
          front.length + (cl.lens[sym.val]!).val + 3 := by
        simp only [List.length_append, itemBits, encodeSym_length, lowBits_length, hw] <;> omega
      rw [lengths_spec]
      refine ⟨⟨by omega, by omega⟩, fun _ => ⟨fun heq => by omega, fun _ => ?_⟩⟩
      refine ⟨sym.val, front.length + (cl.lens[sym.val]!).val, 3 + e.val, hsymbol,
        fun _ => ⟨by simp only [Int.toNat_natCast, Nat.cast_add], fun _ => ?_⟩⟩
      refine ⟨fun h16 => by omega, fun _ => ⟨fun h16 => by omega, fun _ => ⟨fun _ => ?_, fun hn => absurd (by exact_mod_cast hsym) hn⟩⟩⟩
      refine ⟨⟨e.val, hfield, by push_cast; ring⟩, fun _ => ⟨⟨by omega, by omega⟩, fun _ => ⟨?_, fun _ => ?_⟩⟩⟩
      · intro k hk1 hk2
        exact_mod_cast hz k.toNat (by omega) (by omega)
      · have hj : (front.length : ℤ) + ((itemsBits cl (sym :: ss) (e :: es)).length : ℕ) =
            ((front ++ itemBits cl sym.val e.val).length + (itemsBits cl ss es).length : ℕ) := by
          simp only [itemsBits_cons, List.length_append]
          push_cast
          ring
        rw [hj]
        have hpn : (p : ℤ) + (3 + (e.val : ℤ)) = ((p + 3 + e.val : ℕ) : ℤ) := by push_cast; ring
        rw [hpn]
        convert hih using 2 <;> simp only [hlen, Nat.cast_add] <;> ring
  | zeros2 p sym e ss es hsym he hn hz htail ih =>
      have hu' : Usable cl.lens ss := fun x hx => hu x (List.mem_cons_of_mem _ hx)
      obtain ⟨hs19, hpos⟩ := hu sym (List.mem_cons_self ..)
      have hw : extraWidth sym.val = 7 := by unfold extraWidth; split_ifs <;> omega
      have hsymbol := symbol_decode s front
        (lowBits e.val (extraWidth sym.val) ++ itemsBits cl ss es ++ tail) cl.lens cl.words 7
        sym.val hcl hs19 hpos (by simpa only [itemsBits_cons, itemBits, List.append_assoc] using hs)
      have hfield := field_at_prefix s (front ++ encodeSym cl.lens cl.words sym.val)
        (itemsBits cl ss es ++ tail) e.val 7
        (by simpa only [itemsBits_cons, itemBits, hw, List.append_assoc] using hs) (by omega)
      simp only [List.length_append, encodeSym_length, Nat.cast_add] at hfield
      have hih := ih hu' (front ++ itemBits cl sym.val e.val)
        (by simpa only [itemsBits_cons, List.append_assoc] using hs)
      have hlen : (front ++ itemBits cl sym.val e.val).length =
          front.length + (cl.lens[sym.val]!).val + 7 := by
        simp only [List.length_append, itemBits, encodeSym_length, lowBits_length, hw] <;> omega
      rw [lengths_spec]
      refine ⟨⟨by omega, by omega⟩, fun _ => ⟨fun heq => by omega, fun _ => ?_⟩⟩
      refine ⟨sym.val, front.length + (cl.lens[sym.val]!).val, 11 + e.val, hsymbol,
        fun _ => ⟨by simp only [Int.toNat_natCast, Nat.cast_add], fun _ => ?_⟩⟩
      refine ⟨fun h16 => by omega, fun _ => ⟨fun h16 => by omega, fun _ => ⟨fun h17 => by omega, fun _ => ⟨by exact_mod_cast hsym, fun _ => ?_⟩⟩⟩⟩
      refine ⟨⟨e.val, hfield, by push_cast; ring⟩, fun _ => ⟨⟨by omega, by omega⟩, fun _ => ⟨?_, fun _ => ?_⟩⟩⟩
      · intro k hk1 hk2
        exact_mod_cast hz k.toNat (by omega) (by omega)
      · have hj : (front.length : ℤ) + ((itemsBits cl (sym :: ss) (e :: es)).length : ℕ) =
            ((front ++ itemBits cl sym.val e.val).length + (itemsBits cl ss es).length : ℕ) := by
          simp only [itemsBits_cons, List.length_append]
          push_cast
          ring
        rw [hj]
        have hpn : (p : ℤ) + (11 + (e.val : ℤ)) = ((p + 11 + e.val : ℕ) : ℤ) := by push_cast; ring
        rw [hpn]
        convert hih using 2 <;> simp only [hlen, Nat.cast_add] <;> ring

/-- The order in which the header sends the code-length lengths (RFC 1951 §3.2.7). -/
def clOrder : List ℕ := [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

theorem clOrder_spec (k : ℕ) (hk : k < 19) :
    (([16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8, 11#u8, 4#u8, 12#u8, 3#u8,
      13#u8, 2#u8, 14#u8, 1#u8, 15#u8] : List U8)[k]!).val = clOrder[k]! := by
  interval_cases k <;> rfl

theorem clOrder_lt (k : ℕ) (hk : k < 19) : clOrder[k]! < 19 := by
  interval_cases k <;> decide

/-- The three-bit lengths of the first `k` code-length symbols in `clOrder`. -/
def clBits (cl : List U8) : ℕ → List Bool
  | 0 => []
  | k + 1 => clBits cl k ++ lowBits (cl[clOrder[k]!]!).val 3

@[simp] theorem clBits_length (cl : List U8) (k : ℕ) : (clBits cl k).length = 3 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [clBits, ih]; omega

theorem clBits_split (cl : List U8) (k hclen : ℕ) (hk : k < hclen) :
    ∃ rest, clBits cl hclen = clBits cl k ++ lowBits (cl[clOrder[k]!]!).val 3 ++ rest := by
  induction hclen with
  | zero => omega
  | succ m ih =>
      by_cases hkm : k = m
      · subst hkm
        exact ⟨[], by simp [clBits]⟩
      · obtain ⟨rest, hr⟩ := ih (by omega)
        exact ⟨rest ++ lowBits (cl[clOrder[m]!]!).val 3, by simp only [clBits, hr, List.append_assoc]⟩

/-- The whole header after the block type: the three counts, the code-length lengths, the
    run-length coded lengths. -/
def headerBits (nlit ndist hclen : ℕ) (cl : Tab) (ss es : List Usize) : List Bool :=
  lowBits (nlit - 257) 5 ++ lowBits (ndist - 1) 5 ++ lowBits (hclen - 4) 4 ++
    clBits cl.lens hclen ++ itemsBits cl ss es

theorem tables_decode (s : List U8) (front tail : List Bool) (lit dist : List U8) (cl : Tab)
    (ss es : List Usize) (hclen : ℕ)
    (hlit : 257 ≤ lit.length ∧ lit.length ≤ 286) (hdist : 1 ≤ dist.length ∧ dist.length ≤ 30)
    (hcl19 : cl.lens.length = 19) (hclok : TableOk cl.lens cl.words 7) (hkcl : Kraft cl.lens 7)
    (hklit : Kraft lit 15) (hkdist : Kraft dist 15)
    (hhclen : 4 ≤ hclen ∧ hclen ≤ 19)
    (hzero : ∀ k, hclen ≤ k → k < 19 → (cl.lens[clOrder[k]!]!).val = 0)
    (hcov : Covers (lit ++ dist) 0 ss es) (hu : Usable cl.lens ss)
    (hs : byteBits s = front ++ headerBits lit.length dist.length hclen cl ss es ++ tail) :
    tables_spec s front.length lit dist
      (front.length + (headerBits lit.length dist.length hclen cl ss es).length) := by
  have h1 := field_at_prefix s front
    (lowBits (dist.length - 1) 5 ++ lowBits (hclen - 4) 4 ++ clBits cl.lens hclen ++
      itemsBits cl ss es ++ tail) (lit.length - 257) 5
    (by simpa only [headerBits, List.append_assoc] using hs) (by omega)
  have h2 := field_at_prefix s (front ++ lowBits (lit.length - 257) 5)
    (lowBits (hclen - 4) 4 ++ clBits cl.lens hclen ++ itemsBits cl ss es ++ tail) (dist.length - 1) 5
    (by simpa only [headerBits, List.append_assoc] using hs) (by omega)
  have h3 := field_at_prefix s (front ++ lowBits (lit.length - 257) 5 ++ lowBits (dist.length - 1) 5)
    (clBits cl.lens hclen ++ itemsBits cl ss es ++ tail) (hclen - 4) 4
    (by simpa only [headerBits, List.append_assoc] using hs) (by omega)
  simp only [List.length_append, lowBits_length, Nat.cast_add] at h2 h3
  have hlens := covers_decode cl hclok hcov hu s
    (front ++ lowBits (lit.length - 257) 5 ++ lowBits (dist.length - 1) 5 ++ lowBits (hclen - 4) 4 ++
      clBits cl.lens hclen) tail (by simpa only [headerBits, List.append_assoc] using hs)
  simp only [List.length_append, lowBits_length, clBits_length, Nat.cast_add] at hlens
  refine ⟨trivial, hclen, cl.lens, lit ++ dist, ⟨(lit.length - 257 : ℕ), h1, by omega⟩,
    ⟨(dist.length - 1 : ℕ), h2, by omega⟩, ⟨(hclen - 4 : ℕ), h3, by omega⟩, by omega, ?_,
    kraft_valid _ _ hkcl, by simp, by simp, ?_, ?_, kraft_valid _ _ hklit, kraft_valid _ _ hkdist⟩
  · intro k hk0 hk19
    have hkn : k.toNat < 19 := by omega
    rw [clOrder_spec k.toNat hkn]
    constructor
    · intro hkh
      obtain ⟨rest, hr⟩ := clBits_split cl.lens k.toNat hclen (by omega)
      have hbound : (cl.lens[clOrder[k.toNat]!]!).val < 2 ^ 3 := by
        have := hkcl.1 (clOrder[k.toNat]!) (by rw [hcl19]; exact clOrder_lt _ hkn)
        omega
      have hf := field_at_prefix s
        (front ++ lowBits (lit.length - 257) 5 ++ lowBits (dist.length - 1) 5 ++
          lowBits (hclen - 4) 4 ++ clBits cl.lens k.toNat)
        (rest ++ itemsBits cl ss es ++ tail) (cl.lens[clOrder[k.toNat]!]!).val 3
        (by rw [hs, headerBits, hr]; simp only [List.append_assoc]) hbound
      simp only [List.length_append, lowBits_length, clBits_length, Nat.cast_add] at hf
      refine ⟨_, ?_, rfl⟩
      convert hf using 2 <;> push_cast <;> omega
    · intro hkh
      exact_mod_cast hzero k.toNat (by omega) hkn
  · simp only [Int.toNat_natCast, List.drop_left, List.length_append]
    have hd : ((((lit.length + dist.length : ℕ) : ℤ) - (lit.length : ℤ)).toNat) = dist.length := by omega
    rw [hd, List.take_length]
  · have hpos : (front.length : ℤ) + 14 + 3 * (hclen : ℤ) =
        ((front.length + 5 + 5 + 4 + 3 * hclen : ℕ) : ℤ) := by push_cast; ring
    rw [hpos]
    convert hlens using 1 <;> (try simp only [headerBits, List.length_append, lowBits_length, clBits_length]) <;> push_cast <;> ring

end Gzip.Proofs.Header
