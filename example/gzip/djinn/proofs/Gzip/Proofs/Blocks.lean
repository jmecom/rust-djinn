import Gzip.Proofs.Stored
import Gzip.Proofs.DynBlock
import Gzip.Proofs.Passes
import Gzip.Proofs.Merge
import Gzip.Proofs.Split

open Aeneas Std Result
open Gzip.solution Gzip.Spec Gzip.Proofs.Writer Gzip.Proofs.Plans Gzip.Proofs.Runtime

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

namespace Gzip.Proofs.Runtime

def Chain (data : List U8) (p : ℕ) (front : List Bool) (done : Bool) : Prop :=
  ∀ s tail, byteBits s = front ++ tail →
    if done then blocks_spec s 80 [] (data.take p) front.length
    else ∀ out j, blocks_spec s front.length (data.take p) out j → blocks_spec s 80 [] out j

theorem chain_extend (data : List U8) (p q : ℕ) (front bits : List Bool) (final : Bool)
    (h : Chain data p front false) (hf : Fragment data p q front bits final)
    (hpos : 0 < bits.length) : Chain data q (front ++ bits) final := by
  intro s tail hs
  have hprev := h s (bits ++ tail) (by simpa only [List.append_assoc] using hs)
  simp only [Bool.false_eq_true, if_false] at hprev
  obtain ⟨hbit, hblock⟩ := hf s tail (by simpa only [List.append_assoc] using hs)
  have hsz := congrArg List.length hs
  simp only [byteBits_length, List.length_append] at hsz
  cases final with
  | true =>
    simp only [Bool.true_eq, if_true] at hbit ⊢
    apply hprev
    convert Encoder.final_block_decode hbit hblock using 1 <;> simp only [List.length_append, Nat.cast_add]
  | false =>
    simp only [Bool.false_eq_true, if_false] at hbit ⊢
    intro out j hrest
    apply hprev
    rw [blocks_spec]
    refine ⟨trivial, fun _ => ⟨fun _ => ?_, fun hn => False.elim (hn hbit)⟩⟩
    refine ⟨data.take q, (front.length + bits.length : ℕ), ?_, fun _ => ?_⟩
    · simpa only [Nat.cast_add] using hblock
    · refine ⟨⟨by omega, by omega⟩, fun _ => ?_⟩
      simpa only [List.length_append, Nat.cast_add] using hrest

/-- A block written as one, or (the first block of a file at the dense levels) as two: the
stream grows by the block's bits, and the chain of blocks extends over the span. -/
theorem block_correct (data : Aeneas.Std.Slice U8) (start stop : Usize) (w : Gzip.solution.Writer)
    (pr : Parsed) (final : Bool) (level : U8)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length) (hspan : stop.val - start.val ≤ 1048576)
    (hpr : Counting.ParsedOk data.val start.val stop.val pr)
    (hb : Buffered w) (hsizeW : (stream w).length ≤ 80 + 17 * start.val)
    (hdsize : data.val.length ≤ 1073741824) :
    block w data start stop pr final level ⦃ r =>
      Buffered r ∧ ∃ bits, stream r = stream w ++ bits ∧
        bits.length ≤ 16 * (stop.val - start.val) + 10000 ∧ 3 ≤ bits.length ∧
        (Chain data.val start.val (stream w) false → Chain data.val stop.val (stream r) final) ⦄ := by
  have hr := hpr.1
  have hone : block1 w data start stop pr final (level >= 10#u8) ⦃ r =>
      Buffered r ∧ ∃ bits, stream r = stream w ++ bits ∧
        bits.length ≤ 16 * (stop.val - start.val) + 10000 ∧ 3 ≤ bits.length ∧
        (Chain data.val start.val (stream w) false → Chain data.val stop.val (stream r) final) ⦄ := by
    have hbudget : (stream w).length + 16 * (stop.val - start.val) + 5000 ≤ 34359738360 := by omega
    refine WP.spec_mono (DynBlock.block1_correct data start stop w pr final (level >= 10#u8) hs hd hspan hpr hb hbudget) ?_
    intro r ⟨hr', bits, he, hlen, hpos, hf⟩
    refine ⟨hr', bits, he, by omega, hpos, fun hc => ?_⟩
    rw [he]
    exact chain_extend data.val start.val stop.val (stream w) bits final hc hf (by omega)
  unfold block
  step as ⟨span, hspanv⟩
  have hsc := Split.split_choice_spec data start span pr.plan level (by omega)
  step as ⟨k, _⟩
  try dsimp only
  split
  · rename_i hk0
    split
    · rename_i hkl
      have hkl' : k.val < pr.plan.lengths.val.length := by scalar_tac
      split
      · rename_i heq
        have hsp := Split.split_plan_spec pr.plan k start data.val stop.val stop.val hr (by omega) (by scalar_tac)
        step as ⟨a, b, mid, hra, hrb, hsm, hms⟩
        try dsimp only at hra hrb hsm hms
        split
        · rename_i hsm'
          split
          · rename_i hms'
            have hsm'' : start.val < mid.val := by scalar_tac
            have hms'' : mid.val < stop.val := by scalar_tac
            step as ⟨pa, hpa, hpaf⟩
            have hb1 := DynBlock.block1_correct data start mid w pa false (level >= 10#u8) (by omega) (by omega) (by omega)
              (Counting.parsedOk_unfused hpa hpaf (Split.runs_tighten hra)) hb (by omega)
            step as ⟨w1, hbw1, bits1, he1, hlen1, hpos1, hf1⟩
            have hw1len : (stream w1).length = (stream w).length + bits1.length := by
              rw [he1, List.length_append]
            step as ⟨pb, hpb, hpbf⟩
            have hb2 := DynBlock.block1_correct data mid stop w1 pb final (level >= 10#u8) (by omega) hd (by omega)
              (Counting.parsedOk_unfused hpb hpbf hrb) hbw1 (by omega)
            refine WP.spec_mono hb2 ?_
            intro r ⟨hr', bits2, he2, hlen2, hpos2, hf2⟩
            refine ⟨hr', bits1 ++ bits2, by rw [he2, he1, List.append_assoc], ?_, ?_, fun hc => ?_⟩
            · rw [List.length_append]; omega
            · rw [List.length_append]; omega
            · have hc1 := chain_extend data.val start.val mid.val (stream w) bits1 false hc hf1 (by omega)
              rw [← he1] at hc1
              have hc2 := chain_extend data.val mid.val stop.val (stream w1) bits2 final hc1 hf2 (by omega)
              rw [he2]
              exact hc2
          · exact hone
        · exact hone
      · exact hone
    · exact hone
  · exact hone

/-- The initial price list (all zeros) is a price list. -/
theorem zero_prices : Dp.Prices (List.replicate 545 0#u32) (List.replicate 30 0#u32) := by
  refine ⟨by simp, by simp, ?_, ?_, ?_⟩
  · intro k hk
    rw [List.getElem!_replicate] <;> scalar_tac
  · intro k hk
    rw [List.getElem!_replicate] <;> scalar_tac
  · intro k hk1 hk2
    rw [List.getElem!_replicate] <;> scalar_tac

/-! ### One chunk -/

/-- One chunk: the parse keeps the tables and prices; the chunk is written at once (a non-final
block, nothing left pending), or the pending block grows by the chunk's plan, or the pending
block is written (if there is one) and replaced; the stream so far always encodes the data
before the pending block's start. -/
theorem chunk_correct (data : Aeneas.Std.Slice U8) (start stop : Usize) (level : U8)
    (w : Gzip.solution.Writer) (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32)
    (lcost dcost : alloc.vec.Vec U32) (pd : Pending)
    (ht : Chains.LTables level.val head.val chain.val start.val) (hprices : Dp.Prices lcost.val dcost.val)
    (hs : start.val ≤ stop.val) (hd : stop.val ≤ data.val.length) (hsize : stop.val - start.val ≤ 32768)
    (hdsize : data.val.length ≤ 1073741824)
    (hfull : stop.val < data.val.length → stop.val - start.val = 32768)
    (hpd : Merge.PendingOk data.val pd start.val) (haligned : start.val % 32768 = 0)
    (hb : Buffered w) (hsizeW : (stream w).length ≤ 80 + 17 * pd.start.val)
    (hsem : Chain data.val pd.start.val (stream w) false) :
    chunk data start stop level w head chain lcost dcost pd ⦃ r =>
      Dp.Prices r.1.1.val r.1.2.1.val ∧
      Merge.PendingOk data.val r.1.2.2 stop.val ∧
      Chains.LTables level.val r.2.2.1.val r.2.2.2.val stop.val ∧
      Buffered r.2.1 ∧ (stream r.2.1).length ≤ 80 + 17 * r.1.2.2.start.val ∧
      Chain data.val r.1.2.2.start.val (stream r.2.1) false ∧ stream w <+: stream r.2.1 ⦄ := by
  unfold chunk
  have hparse := Passes.parse_correct data start stop level head chain lcost dcost ht hs hd hsize hprices
  step as ⟨pl, head1, chain1, hpr, hpr', htable⟩
  obtain ⟨parsed, lcost1, dcost1⟩ := pl
  dsimp only at hpr hpr' ⊢
  have hrun := hpr.1
  have hple := hpd.le
  have hpal := hpd.aligned
  have hll := runs_lengths hrun
  have hpl := runs_lengths hpd.parsed.1
  have hfn := Merge.flush_now_spec level stop (Slice.len data) pd.start start
  step as ⟨early, hearly⟩
  split
  · rename_i het
    obtain ⟨h9, hlt, hpeq⟩ := hearly het
    have hlt' : stop.val < data.val.length := by simpa using hlt
    have hspan32 := hfull hlt'
    rw [hpeq] at hsem hsizeW
    have hblock := block_correct data start stop w parsed false level hs hd (by omega) hpr hb hsizeW hdsize
    step as ⟨w1, hb1, bits, he, hlen, hpos', hchain⟩
    have hnp := Merge.no_pending_spec stop
    step as ⟨pd1, hpd1s, hpd1l, hpd1d, hpd1f⟩
    try simp only [WP.spec_ok]
    refine ⟨hpr', ⟨?_, ?_, ?_, ?_⟩, htable, hb1, ?_, ?_, ?_⟩
    · show pd1.start.val ≤ stop.val
      rw [hpd1s]
    · show pd1.start.val % 32768 = 0
      rw [hpd1s]
      omega
    · show stop.val - pd1.start.val ≤ 1048576
      rw [hpd1s]
      omega
    · show Counting.ParsedOk data.val pd1.start.val stop.val pd1.parsed
      rw [hpd1s]
      exact Merge.parsedOk_empty data.val stop.val pd1.parsed hpd1l hpd1d hpd1f
    · show (stream w1).length ≤ 80 + 17 * pd1.start.val
      rw [he, List.length_append, hpd1s]
      omega
    · show Chain data.val pd1.start.val (stream w1) false
      rw [hpd1s]
      exact hchain hsem
    · rw [he]
      exact List.prefix_append _ _
  · have hca := Merge.costs_at_spec data start stop level parsed hpr hs hd hsize
    step as ⟨parsed1, cost1, hpr1⟩
    have hmc := Merge.merged_costs_spec level pd.parsed.lfreq pd.parsed.dfreq parsed1.lfreq parsed1.dfreq
    step as ⟨lfreq2, dfreq2, cost2, _⟩
    have hmd := Merge.merge_decision_spec level pd.start start stop pd.cost cost1 cost2 (by omega)
    step as ⟨b, hbdec⟩
    split
    · rename_i hbt
      obtain ⟨h9, hstart, hspan⟩ := hbdec hbt
      have hll1 := runs_lengths hpr1.1
      have hap := Merge.append_plan_spec pd.parsed.plan parsed1.plan hll1.1 (by have := hpd.span; omega)
        (by have := hpd.span; omega)
      step as ⟨merged, hml, hmdist⟩
      try simp only [WP.spec_ok]
      refine ⟨hpr', ⟨?_, hpd.aligned, ?_, ⟨?_, fun hf => by simp at hf⟩⟩, htable, hb, hsizeW, hsem, List.prefix_refl _⟩
      · show pd.start.val ≤ stop.val
        omega
      · show stop.val - pd.start.val ≤ 1048576
        exact hspan
      · show Runs data.val stop.val pd.start.val stop.val merged.lengths.val merged.distances.val
        rw [hml, hmdist]
        exact runs_concat (runs_mono hpd.parsed.1 hs) hpr1.1
    · split
      · rename_i hlt
        have hlt' : pd.start.val < start.val := by scalar_tac
        have hbig : 32768 ≤ start.val - pd.start.val := by omega
        have hblock := block_correct data pd.start start w pd.parsed false level hple (by omega) hpd.span hpd.parsed
          hb hsizeW hdsize
        step as ⟨w1, hb1, bits, he, hlen, hpos', hchain⟩
        try simp only [WP.spec_ok]
        refine ⟨hpr', ⟨hs, haligned, ?_, hpr1⟩, htable, hb1, ?_, ?_, ?_⟩
        · show stop.val - start.val ≤ 1048576
          omega
        · show (stream w1).length ≤ 80 + 17 * start.val
          rw [he, List.length_append]
          omega
        · show Chain data.val start.val (stream w1) false
          exact hchain hsem
        · rw [he]
          exact List.prefix_append _ _
      · rename_i hge
        have hpeq : pd.start.val = start.val := by scalar_tac
        try simp only [WP.spec_ok]
        refine ⟨hpr', ⟨hs, haligned, ?_, hpr1⟩, htable, hb, ?_, ?_, List.prefix_refl _⟩
        · show stop.val - start.val ≤ 1048576
          omega
        · show (stream w).length ≤ 80 + 17 * start.val
          omega
        · show Chain data.val start.val (stream w) false
          rw [← hpeq]
          exact hsem

/-! ### The loop over the chunks -/

/-- The state of the loop over the chunks: the writer so far, the match finder's tables, the
price list for the next optimal parse, the pending block, the next chunk's start. -/
structure OuterState (data : List U8) (level : ℕ) (w : Gzip.solution.Writer)
    (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32) (lcost dcost : alloc.vec.Vec U32) (pd : Pending)
    (start : Usize) (done : Bool) : Prop where
  position : start.val ≤ data.length
  finished : done = true → start.val = data.length
  inside : done = false → 0 < start.val → start.val < data.length
  aligned : start.val < data.length → start.val % 32768 = 0
  pending : Merge.PendingOk data pd start.val
  tables : Chains.LTables level head.val chain.val start.val
  prices : Dp.Prices lcost.val dcost.val
  buffer : Buffered w
  size : (stream w).length ≤ 80 + 17 * pd.start.val
  semantics : Chain data pd.start.val (stream w) false

theorem outer_body (data : Aeneas.Std.Slice U8) (level : U8)
    (w : Gzip.solution.Writer) (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32)
    (lcost dcost : alloc.vec.Vec U32) (pd : Pending) (start : Usize) (done : Bool)
    (h : OuterState data.val level.val w head chain lcost dcost pd start done)
    (hdsize : data.val.length ≤ 1073741824) :
    compress_loop.body data level w head chain lcost dcost pd start done ⦃ r =>
      match r with
      | .done (w', pd') => Buffered w' ∧ Merge.PendingOk data.val pd' data.val.length ∧
          (stream w').length ≤ 80 + 17 * pd'.start.val ∧
          Chain data.val pd'.start.val (stream w') false ∧ stream w <+: stream w'
      | .cont (w', head', chain', lcost', dcost', pd', start', done') =>
          OuterState data.val level.val w' head' chain' lcost' dcost' pd' start' done' ∧
          data.val.length - start'.val + (if done' then 0 else 1) <
            data.val.length - start.val + (if done then 0 else 1) ∧ stream w <+: stream w' ⦄ := by
  have hp := h.position
  unfold compress_loop.body
  split
  · rename_i hd
    have hd' : done = true := by simpa using hd
    have hpeq := h.finished hd'
    simp only [WP.spec_ok]
    refine ⟨h.buffer, ?_, h.size, h.semantics, List.prefix_refl _⟩
    rw [← hpeq]
    exact h.pending
  · rename_i hdone
    have hd' : done = false := by cases done <;> simp_all
    dsimp only
    step as ⟨remaining, hrem, _⟩
    have hremval : remaining.val = data.val.length - start.val := by scalar_tac
    have hspanSpec :
        (if remaining < 32768#usize then Slice.len data - start else ok 32768#usize) ⦃ span =>
          span.val = min (data.val.length - start.val) 32768 ⦄ := by
      split <;> step*
      all_goals simp only [min_def]; split_ifs <;> scalar_tac
    step as ⟨span, hspan⟩
    step as ⟨stop, hstop⟩
    have hstopval : stop.val = start.val + span.val := hstop
    have hs : start.val ≤ stop.val := by omega
    have hstopbound : stop.val ≤ data.val.length := by omega
    have hspanbound : stop.val - start.val ≤ 32768 := by omega
    have hinside := h.inside hd'
    have haligned : start.val % 32768 = 0 := by
      by_cases h0 : 0 < start.val
      · exact h.aligned (hinside h0)
      · have hz : start.val = 0 := by omega
        rw [hz]
    have hfinal : decide (stop = Slice.len data) = (stop.val == data.val.length) := by
      simp only [UScalar.eq_equiv, Slice.len_val, Slice.length, beq_eq_decide]
    have hfull : stop.val < data.val.length → stop.val - start.val = 32768 := by
      intro hlt
      omega
    have hchunk := chunk_correct data start stop level w head chain lcost dcost pd h.tables h.prices hs
      hstopbound hspanbound hdsize hfull h.pending haligned h.buffer h.size h.semantics
    step as ⟨r1, w1, head1, chain1, hpr, hpd, ht, hb, hsize, hsem, hprefix⟩
    obtain ⟨lcost1, dcost1, pd1⟩ := r1
    dsimp only at hpr hpd hsize hsem ⊢
    try simp only [WP.spec_ok]
    rw [hfinal]
    refine ⟨⟨hstopbound, ?_, ?_, ?_, hpd, ht, hpr, hb, hsize, hsem⟩, ?_, hprefix⟩
    · intro he
      simpa using he
    · intro hne _
      have : stop.val ≠ data.val.length := by simpa using hne
      omega
    · intro hlt
      have hsp : span.val = 32768 := by omega
      omega
    · by_cases heq : stop.val = data.val.length <;> simp [heq, hd'] <;> omega

@[step] theorem outer_loop (data : Aeneas.Std.Slice U8) (level : U8)
    (w : Gzip.solution.Writer) (head : alloc.vec.Vec U32) (chain : alloc.vec.Vec U32)
    (lcost dcost : alloc.vec.Vec U32) (pd : Pending) (start : Usize) (done : Bool)
    (h : OuterState data.val level.val w head chain lcost dcost pd start done)
    (hdsize : data.val.length ≤ 1073741824) :
    compress_loop data level w head chain lcost dcost pd start done ⦃ r =>
      Buffered r.1 ∧ Merge.PendingOk data.val r.2 data.val.length ∧
      (stream r.1).length ≤ 80 + 17 * r.2.start.val ∧
      Chain data.val r.2.start.val (stream r.1) false ∧ stream w <+: stream r.1 ⦄ := by
  unfold compress_loop
  apply loop.spec_decr_nat (fun (_, _, _, _, _, _, p, d) => data.val.length - p.val + (if d then 0 else 1))
    (fun (w', head', chain', lcost', dcost', pd', p, d) =>
      OuterState data.val level.val w' head' chain' lcost' dcost' pd' p d ∧ stream w <+: stream w')
  · rintro ⟨w', head', chain', lcost', dcost', pd', p, d⟩ ⟨hi, hprefix⟩
    refine WP.spec_mono (outer_body data level w' head' chain' lcost' dcost' pd' p d hi hdsize) ?_
    intro r hr
    cases r with
    | done state =>
      obtain ⟨w'', pd''⟩ := state
      obtain ⟨hb, hpd, hs, hc, hprefix'⟩ := hr
      exact ⟨hb, hpd, hs, hc, hprefix.trans hprefix'⟩
    | cont state => exact ⟨⟨hr.1, hprefix.trans hr.2.2⟩, hr.2.1⟩
  · exact ⟨h, List.prefix_refl _⟩

end Gzip.Proofs.Runtime
