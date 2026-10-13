import Gzip.Proofs.Decode.ReaderImpl

open Aeneas Std Result
open Gzip.Spec Gzip.solution
open Gzip.Proofs.Decode.ReaderImpl Gzip.Proofs.Decode.Parsing

namespace Gzip.Proofs.Decode.HeaderImpl

def ZeroInv (s : Aeneas.Std.Slice U8) (p q : Usize) : Prop :=
  p.val ≤ q.val ∧ q.val ≤ s.val.length ∧ ∀ k, p.val ≤ k → k < q.val → (s.val[k]!).val ≠ 0

def ZeroEnd (s : Aeneas.Std.Slice U8) (p q : Usize) : Prop :=
  ZeroInv s p q ∧ (q.val < s.val.length → (s.val[q.val]!).val = 0)

theorem zero_body (s : Aeneas.Std.Slice U8) (p q : Usize) (h : ZeroInv s p q) :
    skip_zero_loop.body s q ⦃ r => match r with
      | .done v => ZeroEnd s p v
      | .cont v => ZeroInv s p v ∧ s.val.length - v.val < s.val.length - q.val ⦄ := by
  obtain ⟨hp, hq, hprev⟩ := h
  unfold skip_zero_loop.body
  step*
  · refine ⟨⟨by omega, by scalar_tac, ?_⟩, by scalar_tac⟩
    intro k hk hkq
    by_cases he : k = q.val
    · subst k
      have hv : i1 = s.val[q.val]! := by
        rw [getElem!_pos _ _ (by scalar_tac)]
        exact i1_post
      rw [← hv]
      intro hz
      have he : i1 = 0#u8 := by apply UScalar.eq_of_val_eq; exact hz
      simp_all
    · apply hprev k hk; scalar_tac
  · refine ⟨⟨hp, hq, hprev⟩, ?_⟩
    intro _
    rw [getElem!_pos _ _ (by scalar_tac), ← i1_post]
    scalar_tac
  · exact ⟨⟨hp, hq, hprev⟩, by scalar_tac⟩

@[step]
theorem zero_loop (s : Aeneas.Std.Slice U8) (p : Usize) (hp : p.val ≤ s.val.length) :
    skip_zero_loop s p ⦃ q => ZeroEnd s p q ⦄ := by
  unfold skip_zero_loop
  apply loop.spec_decr_nat (fun q => s.val.length - q.val) (ZeroInv s p)
  · intro q hq
    apply WP.spec_mono (zero_body s p q hq)
    intro r hr
    cases r <;> exact hr
  · exact ⟨_root_.le_refl _, hp, by omega⟩

def ZeroPost (s : Aeneas.Std.Slice U8) (p : Usize) (o : Option Usize) : Prop := match o with
  | none => ∀ z, ¬ zero_spec s.val p.val z
  | some q => q.val ≤ s.val.length ∧ zero_spec s.val p.val (q.val - 1)

@[step]
theorem skip_zero_correct (s : Aeneas.Std.Slice U8) (p : Usize) (hp : p.val ≤ s.val.length) :
    skip_zero s p ⦃ o => ZeroPost s p o ⦄ := by
  unfold skip_zero
  step*
  · obtain ⟨⟨hpq, hq, hprev⟩, hend⟩ := q_post
    refine ⟨by scalar_tac, trivial, ⟨⟨by omega, by scalar_tac⟩, by scalar_tac⟩, ?_, ?_⟩
    · have he : ((i1.val : ℤ) - 1).toNat = q.val := by scalar_tac
      rw [he, hend (by scalar_tac)]
      rfl
    · intro k hk hkq
      have h := hprev k.toNat (by omega) (by scalar_tac)
      omega
  · intro z hz
    obtain ⟨⟨hpq, hq, hprev⟩, hend⟩ := q_post
    obtain ⟨_, ⟨⟨hz0, hpz⟩, hzs⟩, he, _⟩ := hz
    have h := hprev z.toNat (by omega) (by scalar_tac)
    omega

def StepPost (s : Aeneas.Std.Slice U8) (R : ℤ → Prop) (o : Option Usize) : Prop := match o with
  | none => ∀ q, R q → q ≤ s.val.length → False
  | some p => R p.val ∧ p.val ≤ s.val.length ∧ ∀ q, R q → q = p.val

def Extra (s : List U8) (present : Bool) (q : ℤ) : Prop :=
  if present then ∃ v, u16le_spec s 10 v ∧ q = 12 + v else q = 10

def Zero (s : List U8) (p : ℤ) (present : Bool) (q : ℤ) : Prop :=
  if present then ∃ z, zero_spec s p z ∧ q = z + 1 else q = p

def Crc (p : ℤ) (present : Bool) (q : ℤ) : Prop :=
  q = if present then p + 2 else p

@[step]
theorem header_extra_correct (s : Aeneas.Std.Slice U8) (present : Bool)
    (hs : 10 ≤ s.val.length) :
    header_extra s present ⦃ o => StepPost s (Extra s.val present) o ⦄ := by
  unfold header_extra
  step*
  all_goals simp_all only [NumPost, StepPost, Extra, Bool.false_eq_true, if_true, if_false, UScalar.ofNatCore_val_eq, Nat.cast_ofNat]
  · intro q hq _
    obtain ⟨v, hv, _⟩ := hq
    exact hv
  · have hb := o_post.2.1
    scalar_tac
  · have hcast : n.val = value.val := by
      rw [n_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
    intro q hq hbound
    obtain ⟨v, hv, he⟩ := hq
    have heq := u16_unique s.val 10 value.val v o_post hv
    scalar_tac
  · have hcast : n.val = value.val := by
      rw [n_post, UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac
    refine ⟨⟨value.val, o_post, by scalar_tac⟩, by scalar_tac, ?_⟩
    intro q hq
    obtain ⟨v, hv, he⟩ := hq
    have heq := u16_unique s.val 10 value.val v o_post hv
    scalar_tac
  · simp_all [StepPost, Extra, Zero, Crc]

@[step]
theorem header_zero_correct (s : Aeneas.Std.Slice U8) (p : Usize) (present : Bool)
    (hp : p.val ≤ s.val.length) :
    header_zero s p present ⦃ o => StepPost s (Zero s.val p.val present) o ⦄ := by
  unfold header_zero
  step*
  · cases o with
    | none =>
      intro q hq _
      obtain ⟨z, hz, _⟩ := hq
      exact o_post z hz
    | some q =>
      obtain ⟨hq, hz⟩ := o_post
      refine ⟨⟨(q.val : ℤ) - 1, hz, by omega⟩, by omega, ?_⟩
      intro q' hq'
      obtain ⟨z, hz', he⟩ := hq'
      have heq := zero_unique s.val p.val (q.val - 1) z hz hz'
      omega
  · simp_all [StepPost, Extra, Zero, Crc]

@[step]
theorem header_crc_correct (s : Aeneas.Std.Slice U8) (p : Usize) (present : Bool)
    (hp : p.val ≤ s.val.length) :
    header_crc s p present ⦃ o => StepPost s (Crc p.val present) o ⦄ := by
  unfold header_crc
  step*
  all_goals simp_all only [StepPost, Crc, Bool.false_eq_true, if_true, if_false]
  · intro q hq hbound
    change q = (p.val : ℤ) + 2 at hq
    scalar_tac
  · refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    intro q hq
    change q = (p.val : ℤ) + 2 at hq
    scalar_tac
  · simp_all [StepPost, Extra, Zero, Crc]

def flag (s : List U8) (k : Nat) : Bool := decide (((s[3]!).val : ℤ) / 2 ^ k % 2 = 1)

def Base (s : List U8) : Prop :=
  10 ≤ s.length ∧ (s[0]!).val = 31 ∧ (s[1]!).val = 139 ∧ (s[2]!).val = 8 ∧ (s[3]!).val < 32

set_option maxHeartbeats 2000000 in
theorem header_iff (s : List U8) (n : ℤ) : header_spec s n ↔ Base s ∧
    ∃ a b c, Extra s (flag s 2) a ∧ Zero s a (flag s 3) b ∧
      Zero s b (flag s 4) c ∧ Crc c (flag s 1) n ∧ n ≤ s.length := by
  simp only [header_spec, header_pre, true_and, Base, Extra, Zero, Crc, flag]
  simp only [flag_spec, flag_pre, pow_succ, pow_zero]
  norm_num
  split_ifs <;> simp_all
  all_goals aesop (add safe (by omega))

theorem extra_nonneg (s : List U8) (f : Bool) (a : ℤ) (h : Extra s f a) : 0 ≤ a := by
  cases f with
  | false => change a = 10 at h; omega
  | true =>
    obtain ⟨v, hv, he⟩ := h
    obtain ⟨_, _, heq⟩ := hv
    omega

theorem zero_mono (s : List U8) (p q : ℤ) (f : Bool) (h : Zero s p f q) : p ≤ q := by
  cases f with
  | false => change q = p at h; omega
  | true => obtain ⟨z, ⟨_, ⟨⟨_, hpz⟩, _⟩, _⟩, he⟩ := h; omega

theorem crc_mono (p q : ℤ) (f : Bool) (h : Crc p f q) : p ≤ q := by
  cases f <;> simp only [Crc, Bool.false_eq_true, if_false, if_true] at h <;> omega

theorem flag_eq (s : List U8) (k : Nat) (y : U8)
    (h : y.val = (s[3]!).val / 2 ^ k % 2) : decide (y = 1#u8) = flag s k := by
  apply Bool.eq_iff_iff.mpr
  simp only [flag, decide_eq_true_eq]
  have hc : (((s[3]!).val : ℤ) / 2 ^ k % 2) = ((y.val : Nat) : ℤ) := by
    rw [h]
    push_cast
    rfl
  rw [hc]
  constructor
  · intro he; rw [he]; rfl
  · intro he; apply UScalar.eq_of_val_eq; change y.val = 1; omega

def HeaderPost (s : Aeneas.Std.Slice U8) (o : Option Usize) : Prop := match o with
  | none => ∀ n, ¬ header_spec s.val n
  | some p => header_spec s.val p.val ∧ p.val ≤ s.val.length

@[step]
theorem read_header_correct (s : Aeneas.Std.Slice U8) :
    read_header s ⦃ o => HeaderPost s o ⦄ := by
  unfold read_header
  step*
  all_goals try simp_all only [StepPost]
  all_goals try omega
  all_goals try (
    intro n hn
    have hb := (header_iff s.val n).mp hn |>.1
    unfold Base at hb
    simp only [getElem!_pos s.val 0 (by omega), getElem!_pos s.val 1 (by omega),
      getElem!_pos s.val 2 (by omega), getElem!_pos s.val 3 (by omega)] at hb
    simp_all only [bne_iff_ne, not_not]
    scalar_tac)
  all_goals
    have hf2 : decide (i6 = 1#u8) = flag s.val 2 := flag_eq s.val 2 i6 (by
      rw [getElem!_pos _ _ (by scalar_tac)]
      norm_num
      assumption)
    simp only [hf2] at *
  all_goals try (
    have hf3 : decide (i8 = 1#u8) = flag s.val 3 := flag_eq s.val 3 i8 (by
      rw [getElem!_pos _ _ (by scalar_tac)]
      norm_num
      assumption)
    simp only [hf3] at *)
  all_goals try (
    have hf4 : decide (i10 = 1#u8) = flag s.val 4 := flag_eq s.val 4 i10 (by
      rw [getElem!_pos _ _ (by scalar_tac)]
      norm_num
      assumption)
    simp only [hf4] at *)
  · intro n hn
    obtain ⟨_, a, b, c, ha, hb, hc, hd, hn⟩ := (header_iff s.val n).mp hn
    have hab := zero_mono _ _ _ _ hb
    have hbc := zero_mono _ _ _ _ hc
    have hcn := crc_mono _ _ _ hd
    exact o_post a ha (by omega)
  · intro n hn
    obtain ⟨_, a, b, c, ha, hb, hc, hd, hn⟩ := (header_iff s.val n).mp hn
    have he := o_post.2.2 a ha
    rw [he] at hb
    have hbc := zero_mono _ _ _ _ hc
    have hcn := crc_mono _ _ _ hd
    exact o1_post b hb (by omega)
  · intro n hn
    obtain ⟨_, a, b, c, ha, hb, hc, hd, hn⟩ := (header_iff s.val n).mp hn
    have he := o_post.2.2 a ha
    rw [he] at hb
    have he' := o1_post.2.2 b hb
    rw [he'] at hc
    have hcn := crc_mono _ _ _ hd
    exact o2_post c hc (by omega)
  · have hf1 : decide (i12 = 1#u8) = flag s.val 1 := flag_eq s.val 1 i12 (by
      rw [getElem!_pos _ _ (by scalar_tac)]
      norm_num
      assumption)
    have hlast : StepPost s (Crc value2.val (decide (i12 = 1#u8))) o := by assumption
    rw [hf1] at hlast
    have ha : Extra s.val (flag s.val 2) value.val ∧ value.val ≤ s.val.length ∧
        ∀ q, Extra s.val (flag s.val 2) q → q = value.val := by assumption
    cases o with
    | none =>
      intro n hn
      obtain ⟨_, a, b, c, ha', hb, hc, hd, hn⟩ := (header_iff s.val n).mp hn
      have he := ha.2.2 a ha'
      rw [he] at hb
      have he' := o1_post.2.2 b hb
      rw [he'] at hc
      have he'' := o2_post.2.2 c hc
      rw [he''] at hd
      exact hlast n hd hn
    | some q =>
      refine ⟨(header_iff s.val q.val).mpr ⟨?_, value.val, value1.val, value2.val,
        ha.1, o1_post.1, o2_post.1, hlast.1, by exact_mod_cast hlast.2.1⟩, hlast.2.1⟩
      unfold Base
      simp only [getElem!_pos s.val 0 (by scalar_tac), getElem!_pos s.val 1 (by scalar_tac),
        getElem!_pos s.val 2 (by scalar_tac), getElem!_pos s.val 3 (by scalar_tac)]
      simp_all only [bne_iff_ne, not_not]
      scalar_tac

end Gzip.Proofs.Decode.HeaderImpl
