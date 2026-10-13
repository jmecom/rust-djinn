import Gzip.Proofs.Blocks

open Aeneas Std Result
open Gzip.solution Gzip.Spec Gzip.Proofs.Writer Gzip.Proofs.Runtime

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

namespace Gzip.Proofs.Runtime

def gzipHeader (xfl : U8) : List U8 :=
  [31#u8, 139#u8, 8#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, xfl, 255#u8]

theorem header_decode (s : List U8) (xfl : U8) (h : gzipHeader xfl <+: s) : header_spec s 10 := by
  have hn : 10 ≤ s.length := by simpa [gzipHeader] using h.length_le
  have h0 := get_prefix s _ h 0 (by simp [gzipHeader])
  have h1 := get_prefix s _ h 1 (by simp [gzipHeader])
  have h2 := get_prefix s _ h 2 (by simp [gzipHeader])
  have h3 := get_prefix s _ h 3 (by simp [gzipHeader])
  simp only [gzipHeader, List.getElem!_cons_zero, List.getElem!_cons_succ] at h0 h1 h2 h3
  refine ⟨trivial, by omega, ?_, ?_, 10, 10, 10, ?_⟩
  · rw [h0, h1, h2]; scalar_tac
  · rw [h3]; scalar_tac
  · rw [h3]
    norm_num [flag_spec, flag_pre]
    omega

def le32 (v : ℕ) : List U8 := le16 (v % 65536) ++ le16 (v / 65536)

theorem u32_prefix (s front tail : List U8) (v : ℕ) (hv : v < 4294967296)
    (hp : front ++ le32 v ++ tail <+: s) : u32le_spec s front.length v := by
  have hlo := u16_prefix s front (le16 (v / 65536) ++ tail) (v % 65536) (by omega)
    (by simpa only [le32, List.append_assoc] using hp)
  have hhi := u16_prefix s (front ++ le16 (v % 65536)) tail (v / 65536) (by omega)
    (by simpa only [le32, List.append_assoc] using hp)
  refine ⟨trivial, (v % 65536 : ℕ), hlo, (v / 65536 : ℕ), ?_, ?_⟩
  · simpa [le16] using hhi
  · omega

/-- A named witness for the weakly specified gzip member choice. -/
def memberChoice (member : List U8) : List U8 → U8 → List U8 := fun _ _ => member

theorem correct (data : Aeneas.Std.Slice U8) (level : U8) (hp : compress_pre data.val level) :
    Gzip.solution.compress data level ⦃ out => compress_spec data.val level out.val ⦄ := by
  have hd : data.val.length ≤ 1073741824 := by unfold compress_pre at hp; omega
  have hxflSpec :
      (if level = 0#u8 then ok 0#u8 else if level < 5#u8 then ok 4#u8 else ok 2#u8) ⦃ xfl =>
        (xfl.val : ℤ) = if (level.val : ℤ) = 0 then 0 else if (level.val : ℤ) < 5 then 4 else 2 ⦄ := by
    split
    · step*
    · split <;> step* <;> split_ifs <;> scalar_tac
  have hheadSize : (if level = 1#u8 then ok 16384#usize
      else if level >= 9#u8 then ok 65536#usize else ok 32768#usize) ⦃ n =>
      0 < n.val ∧ n.val ≤ 65536 ⦄ := by
    split
    · step*
    · split <;> step*
  unfold Gzip.solution.compress
  step as ⟨xfl, hxfl⟩
  step as ⟨reserveChunks, hreserveChunks⟩
  step as ⟨framing, hframing⟩
  step as ⟨reserve, hreserve⟩
  step as ⟨capacity, hcapacity⟩
  have hreserve : (if capacity < 4194304#usize then ok 4194304#usize else ok capacity : Result Usize)
      ⦃ (_ : Usize) => True ⦄ := by
    split <;> simp
  step with hreserve as ⟨reserved, _⟩
  simp only [alloc.vec.Vec.with_capacity]
  step as ⟨v0, hv0⟩
  have hlen0' : v0.val.length = 1 := by simp [hv0, alloc.vec.Vec.with_capacity]
  step as ⟨v1, hv1⟩
  have hlen1' : v1.val.length = 2 := by simp [hv1, hlen0']
  step as ⟨v2, hv2⟩
  have hlen2' : v2.val.length = 3 := by simp [hv2, hlen1']
  step as ⟨v3, hv3⟩
  have hlen3' : v3.val.length = 4 := by simp [hv3, hlen2']
  step as ⟨v4, hv4⟩
  have hlen4' : v4.val.length = 5 := by simp [hv4, hlen3']
  step as ⟨v5, hv5⟩
  have hlen5' : v5.val.length = 6 := by simp [hv5, hlen4']
  step as ⟨v6, hv6⟩
  have hlen6' : v6.val.length = 7 := by simp [hv6, hlen5']
  step as ⟨v7, hv7⟩
  have hlen7' : v7.val.length = 8 := by simp [hv7, hlen6']
  step as ⟨v8, hv8⟩
  have hlen8' : v8.val.length = 9 := by simp [hv8, hlen7']
  step as ⟨v9, hv9⟩
  have hout0 : v9.val = gzipHeader xfl := by
    simp only [hv9, hv8, hv7, hv6, hv5, hv4, hv3, hv2, hv1, hv0, alloc.vec.Vec.with_capacity]
    rfl
  step as ⟨n, hn0, hn1⟩
  step as ⟨head, hhead⟩
  have hcsize : ((if level = 1#u8 then ok 0#usize else ok 65536#usize) : Result Usize)
      ⦃ c => level.val = 1 ∨ c.val = 65536 ⦄ := by
    split
    · rename_i hl
      simp only [WP.spec_ok]
      left
      rw [hl]
      rfl
    · simp
  step with hcsize as ⟨csize, hcs⟩
  step as ⟨chain, hchain⟩
  have ht : Chains.LTables level.val head.val chain.val 0 := by
    refine ⟨by rw [hhead, List.length_replicate]; exact hn0, ?_⟩
    rcases hcs with h | h
    · exact Or.inl h
    · right
      rw [hchain, List.length_replicate, h]
  step as ⟨lcost, hlcost⟩
  step as ⟨dcost, hdcost⟩
  have hpr : Dp.Prices lcost.val dcost.val := by
    rw [hlcost, hdcost]
    exact zero_prices
  let initial : Gzip.solution.Writer := { out := v9, bits := 0#u64, count := 0#u32 }
  have hnp := Merge.no_pending_spec 0#usize
  step as ⟨pd0, hpd0s, hpd0l, hpd0d, hpd0f⟩
  have hpd0sv : pd0.start.val = 0 := by rw [hpd0s]; scalar_tac
  have hstream0 : stream initial = byteBits (gzipHeader xfl) := by simp [stream, initial, hout0, lowBits]
  have hlen0 : (stream initial).length = 80 := by rw [hstream0]; simp [gzipHeader]
  have hi : OuterState data.val level.val initial head chain lcost dcost pd0 0#usize false := by
    refine ⟨by scalar_tac, by simp, by simp, by simp, ?_, ?_, hpr, ?_, ?_, ?_⟩
    · refine ⟨by rw [hpd0sv]; simp, by rw [hpd0sv], by rw [hpd0sv]; simp, ?_⟩
      rw [hpd0sv]
      exact Merge.parsedOk_empty data.val 0 pd0.parsed hpd0l hpd0d hpd0f
    · simpa using ht
    · simp [Buffered, initial]
    · simp only [hlen0, hpd0sv]
      omega
    · intro s tail hs
      simp only [Bool.false_eq_true, if_false]
      simp only [hlen0, hpd0sv, List.take_zero]
      exact fun _ _ h => h
  step as ⟨w0, pd, hb0, hpd, hsize0, hsem0, hprefix0⟩
  change stream initial <+: stream w0 at hprefix0
  rw [hstream0] at hprefix0
  have hple := hpd.le
  have hpspan := hpd.span
  have hblock := block_correct data pd.start (Slice.len data) w0 pd.parsed true level (by simpa using hple)
    (by simp) (by simpa using hpspan) (by simpa using hpd.parsed) hb0 hsize0 hd
  step as ⟨w, hb, bits, he, hlen, hpos, hchain⟩
  have hlenv : (Slice.len data).val = data.val.length := by simp
  rw [hlenv] at hlen
  have hsem : Chain data.val data.val.length (stream w) true := by
    have h := hchain hsem0
    simpa only [hlenv] using h
  have hsize : (stream w).length ≤ 10080 + 17 * data.val.length := by
    rw [he, List.length_append]
    omega
  have hprefix : byteBits (gzipHeader xfl) <+: stream w := hprefix0.trans (by rw [he]; exact List.prefix_append _ _)
  have hspace : w.out.val.length + 12 ≤ Usize.max := space w 12 (by omega)
  have halign := align_stream w hb (by omega)
  step as ⟨w1, hc1, hw1, padding, hpad, hpadlen, hpadsize⟩
  have hprefix1 : gzipHeader xfl <+: w1.out.val := by
    have hbitsPrefix : byteBits (gzipHeader xfl) <+: byteBits w1.out.val := by
      rw [hpad]
      exact hprefix.trans (List.prefix_append _ _)
    obtain ⟨tail, he⟩ := hbitsPrefix
    rw [← bytes_prefix _ _ tail he.symm]
    exact List.take_prefix _ _
  have hsize1 : w1.out.val.length ≤ w.out.val.length + 4 := by simp only [stream_length] at hpadsize; have := hb.1; omega
  have hcrc := Crc.correct data
  step as ⟨crc, hcrcSpec⟩
  step as ⟨lo, hlo⟩
  have hloval : lo.val = crc.val % 65536 := by
    rw [hlo, UScalar.val_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 16
  have h2 := bits16a w1 lo hc1 hw1 (by rw [hloval]; omega) (by omega)
  step as ⟨w2, hout2, hc2, hw2⟩
  step as ⟨high, hhigh⟩
  have hhighval : high.val = crc.val / 65536 := by simpa only [Nat.shiftRight_eq_div_pow] using hhigh
  have hcrcBound : crc.val < 4294967296 := by scalar_tac
  have h3 := bits16b w2 high hc2 (by rw [hw2, hloval]; omega) (by rw [hhighval]; omega) (by rw [hout2]; omega)
  step as ⟨w3, hout3, hc3, hw3⟩
  have hsize3 : w3.out.val.length = w1.out.val.length + 4 := by simp [hout3, hout2, le16]
  step as ⟨size, hsizeCast⟩
  have hsizeval : size.val = data.val.length := by scalar_tac
  step as ⟨sizeLo, hsizeLo⟩
  have hsizeLoval : sizeLo.val = data.val.length % 65536 := by
    rw [hsizeLo, UScalar.val_and]
    change size.val &&& 65535 = _
    rw [Nat.and_two_pow_sub_one_eq_mod size.val 16, hsizeval]
  have h4 := bits16a w3 sizeLo hc3 hw3 (by rw [hsizeLoval]; omega) (by omega)
  step as ⟨w4, hout4, hc4, hw4⟩
  step as ⟨sizeHigh, hsizeHigh⟩
  have hsizeHighval : sizeHigh.val = data.val.length / 65536 := by
    rw [hsizeHigh, Nat.shiftRight_eq_div_pow, hsizeval]
  have h5 := bits16b w4 sizeHigh hc4 (by rw [hw4, hsizeLoval]; omega) (by rw [hsizeHighval]; omega) (by rw [hout4]; omega)
  step as ⟨w5, hout5, hc5, hw5⟩
  have hout : w5.out.val = w1.out.val ++ le32 crc.val ++ le32 data.val.length := by
    simp only [hout5, hout4, hout3, hout2, hw4, hw2, hloval, hhighval, hsizeLoval, hsizeHighval, le32, List.append_assoc]
  have hsize5 : w5.out.val.length = w1.out.val.length + 8 := by simp [hout, le32, le16]
  have hfinalbits : byteBits w5.out.val = stream w ++ (padding ++ byteBits (le32 crc.val ++ le32 data.val.length)) := by
    simp only [hout, byteBits_append, hpad, List.append_assoc]
  have hblocks := hsem w5.out.val _ hfinalbits
  simp only [Bool.true_eq, if_true, List.take_length] at hblocks
  have hpos : ((stream w).length + 7 : ℤ) / 8 = w1.out.val.length := by omega
  have hprefix5 : gzipHeader xfl <+: w5.out.val := by
    rw [hout]
    exact hprefix1.trans ((List.prefix_append _ _).trans (List.prefix_append _ _))
  have hm : Encoder.MemberWrites w5.out.val data.val (stream w).length := by
    refine ⟨header_decode _ _ hprefix5, hblocks, ?_, ?_, ?_⟩
    · rw [hpos]; omega
    · refine ⟨crc, hcrcSpec, ?_⟩
      rw [hpos]
      exact u32_prefix _ _ _ crc.val hcrcBound (by rw [hout])
    · rw [hpos]
      have hlenmod : (data.val.length : ℤ) % 4294967296 = data.val.length := by omega
      rw [hlenmod]
      have hu := u32_prefix w5.out.val (w1.out.val ++ le32 crc.val) [] data.val.length (by omega)
        (by simp only [List.append_nil, ← hout]; exact List.prefix_refl _)
      simpa [le32, le16] using hu
  have hround := Encoder.member_round_trip hm (by omega)
  refine ⟨memberChoice w5.out.val, hp, ⟨some data.val, hround, rfl⟩, rfl, ?_, ?_, ?_, ?_⟩
  · have hlen := hprefix1.length_le
    simp only [gzipHeader, List.length_cons, List.length_nil] at hlen
    omega
  · obtain ⟨tail, he⟩ := hprefix5
    rw [← he]
    simp [gzipHeader]
  · have hget := get_prefix w5.out.val _ hprefix5 8 (by simp [gzipHeader])
    simpa only [gzipHeader, List.getElem!_cons_succ, List.getElem!_cons_zero, hget] using hxfl
  · have hget := get_prefix w5.out.val _ hprefix5 9 (by simp [gzipHeader])
    simp only [hget, gzipHeader, List.getElem!_cons_succ, List.getElem!_cons_zero]
    scalar_tac

end Gzip.Proofs.Runtime
