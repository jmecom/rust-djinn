import Aeneas
import Gzip.Spec

open Aeneas Std Result
open Gzip.Spec

namespace Gzip.Proofs.Encoder

inductive Token where
  | literal (byte : U8)
  | copy (distance length : ℤ)

/-- A plan's bit-level encoding, independent of how its matches were found.
    Positions and code lengths are mathematical integers. Copies may overlap. -/
inductive Writes (s lit dist : List U8) : ℤ → List U8 → List Token → List U8 → ℤ → Prop
  | finish (i j : ℤ) (prev : List U8)
      (symbol : symbol_spec s i lit 256)
      (after : j = i + (lit[256]!).val)
      (bounds : i < j ∧ j ≤ 8 * (s.length : ℤ)) :
      Writes s lit dist i prev [] prev j
  | literal (i a j : ℤ) (prev mid out : List U8) (byte : U8) (rest : List Token)
      (symbol : symbol_spec s i lit byte.val)
      (after : a = i + (lit[byte.val]!).val)
      (bounds : i < a ∧ a ≤ 8 * (s.length : ℤ))
      (append : append_spec prev byte.val mid)
      (tail : Writes s lit dist a mid rest out j) :
      Writes s lit dist i prev (.literal byte :: rest) out j
  | copy (i a b c j k dc lb le lx db de dx len d : ℤ)
      (prev mid out : List U8) (rest : List Token)
      (symbol : symbol_spec s i lit (257 + k))
      (after : a = i + (lit[(257 + k).toNat]!).val)
      (bounds : i < a ∧ a ≤ 8 * (s.length : ℤ))
      (lengthBase : lbase_spec k lb)
      (lengthExtra : lextra_spec k le)
      (lengthField : field_spec s a le lx)
      (lengthValue : len = lb + lx)
      (afterLength : b = a + le)
      (distanceSymbol : symbol_spec s b dist dc)
      (distanceBase : dbase_spec dc db)
      (distanceExtra : dextra_spec dc de)
      (distanceField : field_spec s (b + (dist[dc.toNat]!).val) de dx)
      (distanceValue : d = db + dx)
      (afterDistance : c = b + (dist[dc.toNat]!).val + de)
      (copyBounds : a < c ∧ c ≤ 8 * (s.length : ℤ))
      (copy : copy_spec prev d len mid)
      (tail : Writes s lit dist c mid rest out j) :
      Writes s lit dist i prev (.copy d len :: rest) out j

theorem writes_decode {s lit dist : List U8} {i j : ℤ} {prev out : List U8} {plan : List Token}
    (h : Writes s lit dist i prev plan out j) : symbols_spec s i lit dist prev out j := by
  induction h with
  | finish i j prev hs ha hb =>
      rw [symbols_spec]
      refine ⟨trivial, fun _ => ⟨256, j, hs, fun _ => ⟨ha, fun _ => ⟨hb, fun _ => ?_⟩⟩⟩⟩
      exact ⟨fun _ => ⟨rfl, rfl⟩, fun hn => False.elim (hn rfl)⟩
  | literal i a j prev mid out byte rest hs ha hb happ htail ih =>
      rw [symbols_spec]
      refine ⟨trivial, fun _ => ⟨byte.val, a, hs, fun _ => ⟨by simpa using ha, fun _ => ⟨hb, fun _ => ?_⟩⟩⟩⟩
      have hn : (byte.val : ℤ) < 256 := by scalar_tac
      refine ⟨fun he => by omega, fun _ => ⟨fun _ => ⟨mid, happ, fun _ => ih⟩, fun he => False.elim (he hn)⟩⟩
  | copy i a b c j k dc lb le lx db de dx len d prev mid out rest hs ha hb hlb hle hlx hlen
      hafter hds hdb hde hdx hd hc hcb hcopy htail ih =>
      rw [symbols_spec]
      refine ⟨trivial, fun _ => ⟨257 + k, a, hs, fun _ => ⟨ha, fun _ => ⟨hb, fun _ => ?_⟩⟩⟩⟩
      have hk : 0 ≤ k := by rw [lbase_spec] at hlb; exact hlb.1
      refine ⟨fun he => by omega, fun _ => ⟨fun he => by omega, fun _ => ?_⟩⟩
      refine ⟨len, b, dc, d, c, ?_, fun _ => ?_⟩
      · exact ⟨lb, by simpa using hlb, le, by simpa using hle, lx, hlx, hlen⟩
      · refine ⟨⟨le, by simpa using hle, hafter⟩, fun _ => ⟨hds, fun _ => ?_⟩⟩
        refine ⟨⟨db, hdb, de, hde, dx, hdx, hd⟩, fun _ => ?_⟩
        exact ⟨⟨de, hde, hc⟩, fun _ => ⟨hcb, fun _ => ⟨mid, hcopy, fun _ => ih⟩⟩⟩

/-- The same plan lemma applies to every valid pair of Huffman tables. -/
theorem fixed_block_decode {s prev out : List U8} {i j : ℤ} {plan : List Token}
    {lit dist : List U8} (hlit : fixedlit_spec lit) (hdist : fixeddist_spec dist)
    (hzero : ¬ field_spec s i 2 0) (htype : field_spec s i 2 1)
    (hw : Writes s lit dist (i + 2) prev plan out j) : block_spec s i prev out j := by
  refine ⟨trivial, ?_, ?_⟩
  · intro h
    exact False.elim (hzero h)
  · intro _
    exact ⟨fun _ => ⟨lit, hlit, dist, hdist, writes_decode hw⟩,
      fun h => False.elim (h htype)⟩

theorem bit_unique {s : List U8} {i a b : ℤ}
    (ha : bit_spec s i a) (hb : bit_spec s i b) : a = b := ha.2.2.trans hb.2.2.symm

theorem final_block_decode {s prev out : List U8} {i j : ℤ}
    (hfinal : bit_spec s i 1) (hblock : block_spec s (i + 1) prev out j) :
    blocks_spec s i prev out j := by
  rw [blocks_spec]
  refine ⟨trivial, fun _ => ⟨?_, fun _ => hblock⟩⟩
  intro hz
  have := bit_unique hz hfinal
  omega

/-- Whole-member relation. Block planning and match search do not occur here;
    the only obligations are the bits written, the decoded tokens, and the trailer. -/
structure MemberWrites (s data : List U8) (endBit : ℤ) : Prop where
  header : header_spec s 10
  blocks : blocks_spec s 80 [] data endBit
  size : (s.length : ℤ) = (endBit + 7) / 8 + 8
  crc : ∃ c : U32, crc32_spec data c ∧ u32le_spec s ((endBit + 7) / 8) c.val
  length : u32le_spec s ((endBit + 7) / 8 + 4) ((data.length : ℤ) % 4294967296)

theorem member_writes_decode {s data : List U8} {j : ℤ} (h : MemberWrites s data j) : member_spec s data := by
  refine ⟨trivial, 10, j, (j + 7) / 8, h.header, ?_, rfl, h.size, ?_, h.length⟩
  · exact h.blocks
  · obtain ⟨c, hc, ht⟩ := h.crc
    exact ⟨c, hc, c.val, ht, rfl⟩

theorem member_round_trip {s data : List U8} {j : ℤ} (h : MemberWrites s data j)
    (hbound : (data.length : ℤ) ≤ 1073741824) : decompress_spec s (some data) := by
  have hm := member_writes_decode h
  refine ⟨trivial, ?_, fun _ => hm⟩
  constructor
  · intro _
    exact ⟨⟨trivial, data, hm⟩, data, hm, hbound⟩
  · intro _
    rfl

end Gzip.Proofs.Encoder
