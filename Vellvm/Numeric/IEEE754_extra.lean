/-
The Compcert verified compiler.
Xavier Leroy and Jacques-Henri Jourdan, INRIA Paris-Rocquencourt.
Copyright Institut National de Recherche en Informatique et en Automatique. All rights
reserved. This file is distributed under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation, either version 2.1 of the License,
or (at your option) any later version. This file is also distributed under the terms
of the INRIA Non-Commercial License Agreement.
-/
import Vellvm.Numeric.Flocq.Operations
import Vellvm.Numeric.Flocq.NormalizeCorrect
import Vellvm.Numeric.Flocq.Bounds
import Vellvm.Numeric.Flocq.Conversion
import Vellvm.Numeric.Flocq.Sterbenz
import Vellvm.Numeric.Flocq.OddBits
import Vellvm.Numeric.Flocq.RoundOdd
import Vellvm.Numeric.Flocq.Scale

namespace Vellvm.Numeric.IEEE754_extra

open Flocq


theorem is_finite_not_is_nan : ∀ (p e : Int) (f : binary_float p e), is_finite f = true → is_nan f =
    false := by
  intro p e f h
  cases f <;> simp_all [is_finite, is_nan]

theorem is_finite_strict_finite : ∀ (p e : Int) (f : binary_float p e), is_finite_strict f = true →
    is_finite f = true := by
  intro p e f h
  cases f <;> simp_all [is_finite_strict, is_finite]

def is_finite_pos0 (p e : Int) : binary_float p e → Bool
  | .B754_zero s => !s
  | .B754_finite .. => true
  | _ => false

theorem Bsign_pos0 : ∀ (p e : Int) (x : binary_float p e), is_finite_pos0 p e x = true → Bsign x =
    decide (B2R x < 0) := by
  intro p e x h
  cases x with
  | B754_zero s => cases s <;> simp_all [is_finite_pos0, B2R, B2F, Bsign]
  | B754_infinity | B754_nan => contradiction
  | B754_finite s m i _ =>
    have hpos : 0 < (m.val : ℝ) * (2 : ℝ) ^ i := mul_pos (Nat.cast_pos.mpr m.property) (by positivity)
    cases s <;> simp [B2F, B2R, Bsign, signed, hpos, hpos.not_gt]

def Beq_dec (p e : Int) (a b : binary_float p e) : Decidable (a = b) := inferInstance

noncomputable def integer_representable (p e n : Int) : Prop :=
  |n| ≤ pow2 e - pow2 (e - p) ∧ generic_format (fexp p e) (n : ℝ)

theorem int_upper_bound_eq : ∀ (p e : Int) (hp : 0 < p) (he : p < e), (pow2 e - pow2 (e - p)) = (pow2 p
    - 1) * pow2 (e - p) := by
  intro p e hp he
  have h := pow2_add (i := p) (j := e - p) hp.le (by omega)
  rw [show p + (e - p) = e by omega] at h
  rw [h]; ring

def BofZ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int) :=
  binary_normalize p e hp he .mode_NE n 0 false

def int_round_odd (x k : Int) : Int := oddInt x k

theorem int_round_odd_exact : ∀ k x : Int, 0 ≤ k → pow2 k ∣ x → int_round_odd x k = x := by
  intro k x _ h
  simp [int_round_odd, oddInt, Int.emod_eq_zero_of_dvd h, Int.ediv_mul_cancel h]

theorem int_round_odd_le : ∀ k x y : Int, 0 ≤ k → x ≤ y → int_round_odd x k ≤ int_round_odd y k := by
  intro k x y hk hxy
  have b := pow2_pos hk
  have hq := Int.ediv_le_ediv b hxy
  unfold int_round_odd oddInt
  apply mul_le_mul_of_nonneg_right _ b.le
  split_ifs with hx hy hy
  · exact hq
  · omega
  · by_contra! h
    have hEq : x / pow2 k = y / pow2 k := by omega
    have hxm := Int.ediv_mul_add_emod x (pow2 k)
    have hym := Int.ediv_mul_add_emod y (pow2 k)
    rw [hEq] at hxm
    have hrem := Int.emod_nonneg x b.ne'
    omega
  · omega

def ZofB (p e : Int) (f : binary_float p e) : Option Int :=
  if is_finite f then some (Ztrunc (B2Q f)) else none


theorem ZofB_correct : ∀ (p e : Int) (f : binary_float p e), ZofB p e f = if is_finite f then some
    (Ztrunc (B2R f)) else none := by
  intro p e f
  rw [← cast_B2Q f]
  by_cases h : B2Q f < 0
  · have h' : ((B2Q f : ℚ) : ℝ) < 0 := by exact_mod_cast h
    simp only [ZofB, Ztrunc, if_pos h, if_pos h', Rat.ceil_cast]
  · have h' : ¬ ((B2Q f : ℚ) : ℝ) < 0 := by exact_mod_cast h
    simp only [ZofB, Ztrunc, if_neg h, if_neg h', Rat.floor_cast]

theorem Ztrunc_range_pos : ∀ x : ℝ, 0 < Ztrunc x → (Ztrunc x : ℝ) ≤ x ∧ x < ((Ztrunc x + 1 : Int) : ℝ) := by
  intro x h
  by_cases hx : x < 0
  · simp only [Ztrunc, if_pos hx] at h
    exact False.elim (not_lt_of_ge (Int.ceil_nonpos.mpr hx.le) h)
  · simpa only [Ztrunc, if_neg hx, Int.cast_add, Int.cast_one] using
      And.intro (Int.floor_le x) (Int.lt_floor_add_one x)

theorem Ztrunc_range_zero : ∀ x : ℝ, Ztrunc x = 0 → -1 < x ∧ x < 1 := by
  intro x h
  unfold Ztrunc at h
  split at h <;> rename_i hx
  · have := Int.ceil_lt_add_one x
    rw [h, Int.cast_zero] at this
    constructor <;> linarith
  · have := Int.lt_floor_add_one x
    rw [h, Int.cast_zero] at this
    constructor <;> linarith

private theorem trunc_of_some {p e n} {f : binary_float p e} (h : ZofB p e f = some n) :
    Ztrunc (B2R f) = n := by
  rw [ZofB_correct] at h
  split at h <;> simp_all

theorem ZofB_range_pos : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (f : binary_float p e) (n : Int), ZofB
    p e f = some n → 0 < n → (n : ℝ) ≤ B2R f ∧ B2R f < ((n + 1 : Int) : ℝ) := by
  intro p e _ _ f n h hn
  rw [← trunc_of_some h] at hn ⊢
  exact Ztrunc_range_pos _ hn

theorem ZofB_range_neg : ∀ (p e : Int) (f : binary_float p e) (n : Int), ZofB p e f = some n → n < 0 →
    ((n - 1 : Int) : ℝ) < B2R f ∧ B2R f ≤ (n : ℝ) := by
  intro p e f n h hn
  have ht := trunc_of_some h
  unfold Ztrunc at ht
  split at ht <;> rename_i hs
  · subst n
    constructor
    · push_cast
      linarith [Int.ceil_lt_add_one (B2R f)]
    · exact Int.le_ceil _
  · have := Int.floor_nonneg.mpr (le_of_not_gt hs)
    omega

theorem ZofB_range_zero : ∀ (p e : Int) (f : binary_float p e), ZofB p e f = some 0 → -1 < B2R f ∧ B2R f
    < 1 := by
  intro p e f h
  exact Ztrunc_range_zero _ (trunc_of_some h)

theorem ZofB_range_nonneg : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (f : binary_float p e) (n : Int),
    ZofB p e f = some n → 0 ≤ n → -1 < B2R f ∧ B2R f < ((n + 1 : Int) : ℝ) := by
  intro p e hp he f n h hn
  rcases hn.eq_or_lt with hn | hn
  · subst n; simpa using ZofB_range_zero _ _ _ h
  · obtain ⟨hl, hu⟩ := ZofB_range_pos _ _ hp he f n h hn
    exact ⟨lt_of_lt_of_le (by exact_mod_cast (show -1 < n by omega)) hl, hu⟩

theorem Zfloor_minus : ∀ (x : ℝ) (n : Int), ⌊x - n⌋ = ⌊x⌋ - n := by
  exact Int.floor_sub_intCast

def ZofB_range (p e : Int) (f : binary_float p e) (lo hi : Int) : Option Int := do
  let n ← ZofB p e f
  if lo ≤ n ∧ n ≤ hi then some n else none

theorem ZofB_range_correct : ∀ (p e : Int) (f : binary_float p e) (l u : Int), let n := Ztrunc (B2R f);
    ZofB_range p e f l u = if is_finite f && decide (l ≤ n) && decide (n ≤ u) then some n else
    none := by
  intro p e f l u
  simp only [ZofB_range, ZofB_correct]
  cases is_finite f <;> simp

theorem ZofB_range_inversion : ∀ (p e : Int) (f : binary_float p e) (l u n : Int), ZofB_range p e f l u
    = some n → l ≤ n ∧ n ≤ u ∧ ZofB p e f = some n := by
  intro p e f l u n h
  cases hv : ZofB p e f with
  | none => simp [ZofB_range, hv] at h
  | some v =>
    by_cases h' : l ≤ v ∧ v ≤ u <;> simp_all [ZofB_range]

def Bexact_inverse_mantissa (p : Int) : Positive := ⟨2 ^ (p - 1).toNat, by positivity⟩

theorem Bexact_inverse_mantissa_value : ∀ (p : Int), 0 < p → (((Bexact_inverse_mantissa p).val : Nat) :
    Int) = pow2 (p - 1) := by
  intro p hp
  simp [Bexact_inverse_mantissa, pow2, zpowNat, show ¬ p - 1 < 0 by omega]

theorem Bexact_inverse_mantissa_digits2_pos : ∀ (p e : Int) (hp : 0 < p) (he : p < e), ((digits2_pos
    (Bexact_inverse_mantissa p)).val : Int) = p := by
  intro p e hp _
  simp only [Bexact_inverse_mantissa, digits2_pos, Nat.log_pow (by decide : 1 < 2), Nat.cast_add, Nat.cast_one]
  omega

theorem bounded_Bexact_inverse : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (i : Int), (emin p e ≤ i ∧ i ≤
    e - p) ↔ bounded p e (Bexact_inverse_mantissa p) i = true := by
  intro p e hp he i
  simp only [bounded, Bexact_inverse_mantissa_digits2_pos p e hp he, decide_eq_true_eq, fexp, FLT_exp]
  omega

theorem Bexact_inverse_obligation_1 : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (f : binary_float p e) (s
    : Bool) (m : Positive) (i : Int) (h : bounded p e m i = true), binary_float.B754_finite s m
    i h = f → m = (Bexact_inverse_mantissa p) → let j := -i - (p - 1) * 2; emin p e ≤ j →
    bounded p e m j = true := by
  intro p e hp he f s m i h _ hm
  subst m
  dsimp
  intro hlow
  apply (bounded_Bexact_inverse p e hp he _).mp
  have := (bounded_Bexact_inverse p e hp he i).mpr h
  unfold emin at *; omega

theorem Bexact_inverse_obligation_2 (p e : Int) (b : Bool) :
    let w : binary_float p e := .B754_zero b
    ∀ s m i (h : bounded p e m i = true), binary_float.B754_finite s m i h ≠ w := by
  exact fun _ _ _ _ ↦ nofun

theorem Bexact_inverse_obligation_3 (p e : Int) (b : Bool) :
    let w : binary_float p e := .B754_infinity b
    ∀ s m i (h : bounded p e m i = true), binary_float.B754_finite s m i h ≠ w := by
  exact fun _ _ _ _ ↦ nofun

theorem Bexact_inverse_obligation_4 : ∀ (p e : Int) (b : Bool) (pl : Positive) (v : nan_pl p pl = true),
    let w : binary_float p e := .B754_nan b pl v; ∀ (s : Bool) (m : Positive) (i : Int) (h :
    bounded p e m i = true), binary_float.B754_finite s m i h ≠ w := by
  exact fun _ _ _ _ _ _ _ _ _ ↦ nofun

def Bexact_inverse (p e : Int) (hp : 0 < p) (he : p < e) (f : binary_float p e) :
    Option (binary_float p e) :=
  match f with
  | .B754_finite s m i h =>
    if hm : m = Bexact_inverse_mantissa p then
      let j := -i - (p - 1) * 2
      if hl : emin p e ≤ j then
        if j ≤ e then
          some (.B754_finite s m j (Bexact_inverse_obligation_1 p e hp he _ s m i h rfl hm hl))
        else none
      else none
    else none
  | _ => none

def pos_pow (x y : Positive) : Positive := ⟨x.val ^ y.val, pow_pos x.property _⟩

theorem pos_pow_spec : ∀ x y : Positive, ((pos_pow x y).val : Int) = zpowNat (x.val : Int) (y.val : Int) := by
  intro x y
  simp [pos_pow, zpowNat]

def Bparse (p e : Int) (hp : 0 < p) (he : p < e) (base m : Positive) (i : Int) : binary_float p e :=
  if i = 0 then BofZ p e hp he m.val else
  if 0 < i then
    if i * log2 base.val < e then BofZ p e hp he (m.val * (base.val : Int) ^ i.toNat)
    else .B754_infinity false
  else if i * log2 base.val + log2up m.val < emin p e then .B754_zero false
  else roundQuotient p e hp he .mode_NE false m 0 ⟨base.val ^ i.natAbs, pow_pos base.property _⟩ 0

def Bconv (p₁ e₁ p₂ e₂ : Int) (hp : 0 < p₂) (he : p₂ < e₂) (nan : ConvNaN p₁ e₁ p₂ e₂)
    (md : Mode) (x : binary_float p₁ e₁) : binary_float p₂ e₂ :=
  match x with
  | .B754_nan .. => (nan x).val
  | .B754_infinity s => .B754_infinity s
  | .B754_zero s => .B754_zero s
  | .B754_finite s .. => ofRat p₂ e₂ hp he md (B2Q x) s

theorem B2R_inj_pos0 (p e : Int) (x y : binary_float p e) (hx : is_finite_pos0 p e x = true)
    (hy : is_finite_pos0 p e y = true) (hr : B2R x = B2R y) : x = y := by
  have hs : Bsign x = Bsign y := by rw [Bsign_pos0 _ _ _ hx, Bsign_pos0 _ _ _ hy, hr]
  have positive (m : Positive) (i : Int) : (0 : ℝ) < m.val * (2 : ℝ) ^ i :=
    mul_pos (Nat.cast_pos.mpr m.property) (by positivity)
  cases x with
  | B754_zero a =>
    cases y with
    | B754_zero b => congr 1
    | B754_finite b n j hj =>
      cases b <;> simp [B2R, B2F, signed, n.property.ne', zpow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0)] at hr
    | _ => contradiction
  | B754_finite a m i hi =>
    cases y with
    | B754_zero b =>
      cases a <;> simp [B2R, B2F, signed, m.property.ne', zpow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0)] at hr
    | B754_finite b n j hj =>
      change a = b at hs; subst b
      have h := congrArg (cexp (fexp p e)) hr
      change cexp (fexp p e) (signed a ((m.val : ℝ) * 2 ^ i)) =
          cexp (fexp p e) (signed a ((n.val : ℝ) * 2 ^ j)) at h
      rw [canonical_exp hi, canonical_exp hj] at h; subst j
      have hmn : m = n := by
        apply Subtype.ext
        cases a <;> simp [B2R, B2F, signed, zpow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0)] at hr <;>
          exact_mod_cast hr
      subst n; rfl
    | _ => contradiction
  | _ => contradiction

theorem integer_representable_n2p : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n k : Int), (-pow2 p < n ∧
    n < pow2 p) → 0 ≤ k → k ≤ e - p → integer_representable p e (n * pow2 k) := by
  intro p e hp he n k hn hk hke
  constructor
  · rw [abs_mul, abs_of_pos (pow2_pos hk), int_upper_bound_eq p e hp he]
    exact mul_le_mul_of_nonneg (by have := abs_lt.mpr hn; omega) (pow2_mono hk hke) (abs_nonneg _) (pow2_pos (by omega)).le
  · rw [Int.cast_mul, pow2_cast hk]
    exact format_scaled hp n k (abs_lt.mpr hn) (by unfold emin; omega)

theorem integer_representable_2p : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (k : Int), (0 ≤ k ∧ k ≤ e -
    1) → integer_representable p e (pow2 k) := by
  intro p e hp he k hk
  have hk0 := hk.1
  have hp' : 1 < pow2 p := by
    simp [pow2,zpowNat,hp.not_gt]; exact one_lt_pow₀ (by decide) (by omega)
  constructor
  · rw [abs_of_pos (pow2_pos hk0)]
    have h1 := pow2_mono hk0 hk.2
    have h2 := pow2_mono (i := e - p) (j := e - 1) (by omega) (by omega)
    have h3 := pow2_add (i := e-1) (j := 1) (by omega) (by decide)
    rw [show e-1+1=e by omega] at h3
    have : pow2 1 = 2 := by decide
    rw [this] at h3; omega
  · rw [pow2_cast hk0]
    simpa using format_scaled (e := e) hp 1 k (by simpa using hp') (by unfold emin; omega)

theorem integer_representable_opp : ∀ (p e : Int) (n : Int), integer_representable p e n →
    integer_representable p e (-n) := by
  intro p e n h
  exact ⟨by simpa using h.1, by simpa using format_neg h.2⟩

theorem integer_representable_n2p_wide : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n k : Int), (-pow2 p ≤
    n ∧ n ≤ pow2 p) → 0 ≤ k → k < e - p → integer_representable p e (n * pow2 k) := by
  intro p e hp he n k hn hk hke
  have h := pow2_add hp.le hk
  by_cases hpos : n = pow2 p
  · subst n; rw [← h]; exact integer_representable_2p _ _ hp he _ (by omega)
  by_cases hneg : n = -pow2 p
  · subst n; rw [neg_mul, ← h]; exact integer_representable_opp _ _ _ (integer_representable_2p _ _ hp he _ (by omega))
  exact integer_representable_n2p p e hp he n k (by omega) hk (by omega)

theorem integer_representable_n : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int), (-pow2 p ≤ n ∧ n ≤
    pow2 p) → integer_representable p e n := by
  intro p e hp he n hn
  have h := integer_representable_n2p_wide p e hp he n 0 hn (by decide) (by omega)
  simpa [pow2,zpowNat] using h

theorem Bplus_commut : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (m : Mode) (x y :
    binary_float p e), nan x y = nan y x → Bplus p e hp he nan m x y = Bplus p e hp he nan m y x := by
  intro p e hp he nan md x y h
  cases x <;> cases y <;> simp only [Bplus] <;> try rfl <;> try exact congrArg Subtype.val h
  all_goals first | rw [add_comm] | ((try split_ifs) <;> grind)

theorem Bmult_commut : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (m : Mode) (x y :
    binary_float p e), nan x y = nan y x → Bmult p e hp he nan m x y = Bmult p e hp he nan m y x := by
  intro p e hp he nan md x y h
  cases x <;> cases y <;> simp only [Bmult] <;> first | exact congrArg Subtype.val h | rw [Bool.xor_comm, mul_comm] | rw [Bool.xor_comm]

theorem Bexact_inverse_correct : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (f g : binary_float p e),
    Bexact_inverse p e hp he f = some g → is_finite_strict f = true ∧ is_finite_strict g = true
    ∧ B2R g = (B2R f)⁻¹ ∧ B2R f ≠ 0 ∧ Bsign g = Bsign f := by
  intro p e hp he f g h
  cases f with
  | B754_finite s m i hi =>
    simp only [Bexact_inverse] at h
    split at h <;> try contradiction
    rename_i hm
    split at h <;> try contradiction
    split at h <;> try contradiction
    cases h
    subst m
    have hc : ((Bexact_inverse_mantissa p).val : ℝ) = (2 : ℝ) ^ (p-1) := by
      rw [← pow2_cast (by omega)]; exact_mod_cast Bexact_inverse_mantissa_value p hp
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    simp only [is_finite_strict, Bsign, B2R, B2F, hc, ← zpow_add₀ h2]
    rw [show p - 1 + (-i - (p - 1) * 2) = -(p - 1 + i) by ring, zpow_neg]
    cases s <;> simp [signed, zpow_ne_zero _ h2]
  | _ => contradiction

theorem Bdiv_mult_inverse : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (a b : Nan₂ p e) (m : Mode) (x y z :
    binary_float p e), (∀ i j k, is_nan i = true → is_finite j = true → is_finite k = true → a i
    j = b i k) → Bexact_inverse p e hp he y = some z → Bdiv p e hp he a m x y = Bmult p e hp he
    b m x z := by
  intro p e hp he a b md x y z hn hi
  obtain ⟨hy,hz,hr,_,hs⟩ := Bexact_inverse_correct _ _ hp he y z hi
  have hq : B2Q z = (B2Q y)⁻¹ := by exact_mod_cast (show ((B2Q z : ℚ) : ℝ) = ((B2Q y : ℚ) : ℝ)⁻¹ by simpa only [cast_B2Q] using hr)
  cases y <;> try contradiction
  cases z <;> try contradiction
  cases x with
  | B754_nan => exact congrArg Subtype.val (hn _ _ _ rfl rfl rfl)
  | B754_zero | B754_infinity => simp only [Bdiv, Bmult, hs]
  | B754_finite => simp only [Bdiv, Bmult, hq, hs, div_eq_mul_inv]

theorem Bparse_obligation_1 : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (b m k : Positive), is_nan
    (roundQuotient p e hp he .mode_NE false m 0 (pos_pow b k) 0) = false := by
  intro p e hp he b m k
  apply ofRat_not_nan

theorem Zpower_log : ∀ (b : Radix) (n : Int), 0 < n → pow2 (n * log2 b.val) ≤ zpowNat b.val n ∧ zpowNat
    b.val n ≤ pow2 (n * log2up b.val) := by
  intro b n hn
  obtain ⟨b,hb⟩ := b
  lift b to Nat using (show 0 ≤ b by omega)
  lift n to Nat using hn.le
  have hb' : b ≠ 0 := by omega
  have lo := Nat.pow_log_le_self 2 hb'
  have hi := Nat.le_pow_clog (by decide : 1 < 2) b
  simp only [log2, log2up, Int.toNat_natCast, pow2, zpowNat, Int.ofNat_eq_natCast]
  push_cast
  simp only [Int.natCast_mul, Int.natCast_nonneg, not_lt.mpr, ite_false, Int.toNat_mul, Int.toNat_natCast]
  constructor
  · exact_mod_cast (show 2 ^ (n * Nat.log 2 b) ≤ b ^ n by rw [Nat.mul_comm, pow_mul]; gcongr)
  · exact_mod_cast (show b ^ n ≤ 2 ^ (n * Nat.clog 2 b) by rw [Nat.mul_comm, pow_mul]; gcongr)

theorem bpow_log_pos : ∀ (b : Radix) (n : Int), 0 < n → (2 : ℝ) ^ (n * log2 b.val) ≤ (b.val : ℝ) ^ n := by
  intro b n hn
  have h := (Zpower_log b n hn).1
  rw [← pow2_cast (show 0 ≤ n * log2 b.val from mul_nonneg hn.le (Int.natCast_nonneg _))]
  lift n to Nat using hn.le
  simpa [zpowNat, (Int.natCast_nonneg n).not_gt] using
    (show ((pow2 ((n : Int) * log2 b.val) : Int) : ℝ) ≤ (zpowNat b.val n : ℝ) by exact_mod_cast h)

theorem bpow_log_neg : ∀ (b : Radix) (n : Int), n < 0 → (b.val : ℝ) ^ n ≤ (2 : ℝ) ^ (n * log2 b.val) := by
  intro b n hn
  have h := bpow_log_pos b (-n) (by omega)
  have hb : (0 : ℝ) < b.val := by exact_mod_cast (show (0 : Int) < b.val from lt_of_lt_of_le (by decide) b.property)
  rw [neg_mul,zpow_neg,zpow_neg,inv_le_inv₀ (by positivity) (by positivity)] at h
  exact h

theorem round_int_no_overflow : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int), |n| ≤ (pow2 e - pow2
    (e - p)) → |round (fexp p e) (round_mode .mode_NE) (n : ℝ)| < (2 : ℝ) ^ e := by
  intro p e hp he n h
  have hp' := pow2_pos (i := e-p) (by omega)
  let u := pow2 e - pow2 (e-p)
  have hu : (u : ℝ) < (2 : ℝ)^e := by rw [← pow2_cast (by omega)]; exact_mod_cast (show u < pow2 e by dsimp [u]; omega)
  have hn : |(n : ℝ)| ≤ (u : ℝ) := by exact_mod_cast h
  have hj := bounded_cexp hp he (hn.trans_lt hu)
  have H : (u : ℝ) = ((pow2 p - 1 : Int) : ℝ) * 2 ^ (e-p) := by
    dsimp [u]; rw [int_upper_bound_eq _ _ hp he, Int.cast_mul, pow2_cast (by omega)]
  obtain ⟨hl, hh⟩ := abs_le.mp hn
  have hhigh := round_grid_le .mode_NE (pow2 p - 1) (e-p) hj (H ▸ hh)
  have hlow := round_grid_ge .mode_NE (-(pow2 p - 1)) (e-p) hj (by rw [Int.cast_neg,neg_mul, ← H]; exact hl)
  apply lt_of_le_of_lt _ hu
  apply abs_le.mpr
  rw [H]; push_cast at hlow hhigh ⊢; constructor <;> linarith

theorem BofZ_correct (p e : Int) (hp : 0 < p) (he : p < e) (n : Int) :
    let r := round (fexp p e) (round_mode .mode_NE) (n : ℝ)
    if |r| < (2 : ℝ)^e then B2R (BofZ p e hp he n) = r ∧ is_finite (BofZ p e hp he n) = true ∧
      Bsign (BofZ p e hp he n) = decide (n < 0)
    else B2FF (BofZ p e hp he n) = binary_overflow p e .mode_NE (decide (n < 0)) := by
  have h := ofRat_correct p e hp he .mode_NE (n : ℚ) false
  by_cases hn : n = 0
  · subst n; simpa [BofZ,binary_normalize] using h
  · simpa [BofZ,binary_normalize,hn] using h

theorem BofZ_finite : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int), |n| ≤ (pow2 e - pow2 (e - p)) →
    B2R (BofZ p e hp he n) = round (fexp p e) (round_mode .mode_NE) (n : ℝ) ∧ is_finite (BofZ p
    e hp he n) = true ∧ Bsign (BofZ p e hp he n) = decide (n < 0) := by
  intro p e hp he n hn
  simpa only [if_pos (round_int_no_overflow p e hp he n hn)] using BofZ_correct p e hp he n

theorem BofZ_representable : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int), integer_representable p
    e n → B2R (BofZ p e hp he n) = (n : ℝ) ∧ is_finite (BofZ p e hp he n) = true ∧ Bsign (BofZ p
    e hp he n) = decide (n < 0) := by
  intro p e hp he n hn
  simpa only [format_round hn.2] using BofZ_finite p e hp he n hn.1

theorem BofZ_exact : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int), (-pow2 p ≤ n ∧ n ≤ pow2 p) → B2R
    (BofZ p e hp he n) = (n : ℝ) ∧ is_finite (BofZ p e hp he n) = true ∧ Bsign (BofZ p e hp he
    n) = decide (n < 0) := by
  intro p e hp he n hn
  exact BofZ_representable p e hp he n (integer_representable_n p e hp he n hn)

theorem BofZ_finite_pos0 : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int), |n| ≤ (pow2 e - pow2 (e -
    p)) → is_finite_pos0 p e (BofZ p e hp he n) = true := by
  intro p e hp he n hn
  obtain ⟨hr,hf,hs⟩ := BofZ_finite p e hp he n hn
  cases h : BofZ p e hp he n with
  | B754_zero s =>
    rw [h] at hs hr
    cases s
    · rfl
    · change true = decide (n < 0) at hs
      have hneg : n < 0 := of_decide_eq_true hs.symm
      have := round_le_neg_pow (e := e) hp .mode_NE (n : ℝ) 0 (by unfold emin; omega) (by simpa using (show (n : ℝ) ≤ -1 by exact_mod_cast (show n ≤ -1 by omega)))
      change 0 = _ at hr; rw [← hr] at this; norm_num at this
  | B754_finite => rfl
  | _ => rw [h] at hf; contradiction

theorem BofZ_finite_equal : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (x y : Int), |x| ≤ (pow2 e - pow2 (e
    - p)) → |y| ≤ (pow2 e - pow2 (e - p)) → B2R (BofZ p e hp he x) = B2R (BofZ p e hp he y) →
    (BofZ p e hp he x) = (BofZ p e hp he y) := by
  intro p e hp he x y hx hy h
  exact B2R_inj_pos0 _ _ _ _ (BofZ_finite_pos0 _ _ hp he _ hx) (BofZ_finite_pos0 _ _ hp he _ hy) h

theorem ZofBofZ_exact : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int), integer_representable p e n →
    ZofB p e (BofZ p e hp he n) = some n := by
  intro p e hp he n h
  obtain ⟨hr,hf,_⟩ := BofZ_representable p e hp he n h
  rw [ZofB_correct, hf, hr]; simp

theorem Bconv_correct (p₁ e₁ p₂ e₂ : Int) (h₂ : 0 < p₂) (l₂ : p₂ < e₂)
    (nan : ConvNaN p₁ e₁ p₂ e₂) (md : Mode) (f : binary_float p₁ e₁) (hf : is_finite f = true) :
    let r := round (fexp p₂ e₂) (round_mode md) (B2R f)
    let g := Bconv p₁ e₁ p₂ e₂ h₂ l₂ nan md f
    if |r| < (2 : ℝ)^e₂ then B2R g = r ∧ is_finite g = true ∧ Bsign g = Bsign f
    else B2FF g = binary_overflow p₂ e₂ md (Bsign f) := by
  cases f with
  | B754_zero s =>
    have h : round_mode md (0 : ℝ) = 0 := by simpa only [Int.cast_zero] using mode_intCast (K := ℝ) md 0
    simp [B2R,B2F,Flocq.round,h,Bconv,Bsign,is_finite,zpow_pos (by norm_num : (0:ℝ)<2) e₂]
  | B754_finite s m i hi =>
    let f : binary_float p₁ e₁ := .B754_finite s m i hi
    have hr := ofRat_correct p₂ e₂ h₂ l₂ md (B2Q f) s
    have ha : 0 < (m.val : ℚ) * (2 : ℚ)^i := mul_pos (Nat.cast_pos.mpr m.property) (by positivity)
    have sig : (if B2Q f = 0 then s else decide (B2Q f < 0)) = s := by
      cases s <;> simp only [f,B2Q,B2F,signed, Bool.false_eq_true,if_false,if_true] <;>
        simp [ha,ha.not_gt,ha.ne']
    simpa only [Flocq.cast_B2Q, sig, Bconv,Bsign] using hr
  | _ => contradiction

theorem Bconv_widen_exact : ∀ (p₁ e₁ p₂ e₂ : Int) (h₁ : 0 < p₁) (h₂ : 0 < p₂) (l₂ : p₂ < e₂), p₁ ≤ p₂ →
    e₁ ≤ e₂ → ∀ (nan : ConvNaN p₁ e₁ p₂ e₂) (m : Mode) (f : binary_float p₁ e₁), is_finite f =
    true → B2R (Bconv p₁ e₁ p₂ e₂ h₂ l₂ nan m f) = B2R f ∧ is_finite (Bconv p₁ e₁ p₂ e₂ h₂ l₂
    nan m f) = true ∧ Bsign (Bconv p₁ e₁ p₂ e₂ h₂ l₂ nan m f) = Bsign f := by
  intro p₁ e₁ p₂ e₂ h₁ h₂ l₂ hw he nan md f hf
  have r := format_round (bounds_format h₂ hw he f) md
  have h := (finite_lt f).trans_le (zpow_right_mono₀ (by norm_num) he)
  simpa only [r,if_pos h] using Bconv_correct _ _ _ _ h₂ l₂ nan md f hf

theorem ZofB_Bconv : ∀ (p₁ e₁ p₂ e₂ : Int) (h₁ : 0 < p₁) (h₂ : 0 < p₂) (l₂ : p₂ < e₂), p₁ ≤ p₂ → e₁ ≤ e₂
    → ∀ (nan : ConvNaN p₁ e₁ p₂ e₂) (m : Mode) (f : binary_float p₁ e₁) (n : Int), ZofB p₁ e₁ f
    = some n → ZofB p₂ e₂ (Bconv p₁ e₁ p₂ e₂ h₂ l₂ nan m f) = some n := by
  intro p₁ e₁ p₂ e₂ h₁ h₂ l₂ hw he nan md f n hn
  rw [ZofB_correct] at hn ⊢
  split at hn <;> try contradiction
  rename_i h
  obtain ⟨hr,hf,_⟩ := Bconv_widen_exact _ _ _ _ h₁ h₂ l₂ hw he nan md f h
  simpa only [hf,if_true,hr] using hn

theorem ZofB_range_Bconv : ∀ (p₁ e₁ p₂ e₂ : Int) (h₁ : 0 < p₁) (h₂ : 0 < p₂) (l₂ : p₂ < e₂) (a b c d :
    Int), p₁ ≤ p₂ → e₁ ≤ e₂ → c ≤ a → b ≤ d → ∀ (nan : ConvNaN p₁ e₁ p₂ e₂) (m : Mode) (f :
    binary_float p₁ e₁) (n : Int), ZofB_range p₁ e₁ f a b = some n → ZofB_range p₂ e₂ (Bconv p₁
    e₁ p₂ e₂ h₂ l₂ nan m f) c d = some n := by
  intro p₁ e₁ p₂ e₂ h₁ h₂ l₂ a b c d hw he hl hu nan md f n h
  obtain ⟨hl',hu', hn⟩ := ZofB_range_inversion _ _ _ _ _ _ h
  have H := ZofB_Bconv _ _ _ _ h₁ h₂ l₂ hw he nan md f n hn
  simp [ZofB_range,H,hl.trans hl',hu'.trans hu]

theorem round_integer_overflow : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (b : Radix) (i : Int) (m :
    Positive), 0 < i → e ≤ i * log2 b.val → (2 : ℝ) ^ e ≤ round (fexp p e) (round_mode .mode_NE)
    ((m.val : ℝ) * (b.val : ℝ) ^ i) := by
  intro p e hp he b i m hi h
  have hb : 0 < (b.val : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : (0:Int)<2) b.property)
  have hm : (1 : ℝ) ≤ m.val := by exact_mod_cast m.property
  apply round_ge_pow hp _ _ _ (by unfold emin; omega)
  calc (2:ℝ)^e ≤ 2^(i*log2 b.val) := zpow_right_mono₀ (by norm_num) h
       _ ≤ (b.val : ℝ)^i := bpow_log_pos b i hi
       _ ≤ (m.val : ℝ)*(b.val : ℝ)^i := le_mul_of_one_le_left (by positivity) hm

theorem round_NE_underflows : ∀ (p e : Int) (hp : 0 < p) (x : ℝ), (0 ≤ x ∧ x ≤ (2 : ℝ) ^ (emin p e - 1))
    → round (fexp p e) (round_mode .mode_NE) x = 0 := by
  intro p e hp x hx
  by_cases h0 : x = 0
  · simp [h0,Flocq.round,round_mode,Znearest]
  have hpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm h0)
  have hlog := Int.log_mono_right (b := 2) hpos hx.2
  have hlog2 : Int.log 2 ((2:ℝ)^(emin p e-1)) = emin p e-1 := Int.log_zpow (by decide : 1 < 2) _
  have hj : cexp (fexp p e) x = emin p e := by simp only [cexp,fexp,FLT_exp,abs_of_pos hpos]; omega
  let y := x / (2:ℝ)^(emin p e)
  have hy : 0 ≤ y := div_nonneg hx.1 (by positivity)
  have hy' : y ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    rw [zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0),zpow_one] at hx; linarith [hx.2]
  have hfloor : ⌊y⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hy,by linarith⟩
  have hz : round_mode .mode_NE y = 0 := by
    simp only [round_mode,Znearest,hfloor,Int.cast_zero,sub_zero,if_neg (not_lt.mpr hy')]
    norm_num
  simp only [Flocq.round,hj]
  change (round_mode .mode_NE y : ℝ) * _ = 0
  simp [hz]

theorem round_integer_underflow : ∀ (p e : Int) (hp : 0 < p) (b : Radix) (i : Int) (m : Positive), i < 0
    → i * log2 b.val + log2up m.val < emin p e → round (fexp p e) (round_mode .mode_NE) ((m.val
    : ℝ) * (b.val : ℝ) ^ i) = 0 := by
  intro p e hp b i m hi hl
  apply round_NE_underflows _ _ hp
  have hb : 0 < (b.val : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : (0:Int)<2) b.property)
  constructor
  · positivity
  · have hu : (m.val : ℝ) ≤ 2^(log2up m.val) := by
      simp only [log2up,Int.toNat_natCast,zpow_natCast]; exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) m.val
    calc (m.val : ℝ) * b.val^i ≤ 2^(log2up m.val) * 2^(i*log2 b.val) := mul_le_mul_of_nonneg hu (bpow_log_neg b i hi) (by positivity) (by positivity)
         _ = (2 : ℝ) ^ (log2up m.val + i * log2 b.val) := (zpow_add₀ (by norm_num) _ _).symm
         _ ≤ 2^(emin p e-1) := zpow_right_mono₀ (by norm_num) (by omega)

private theorem finite_inj {p e} {f g : binary_float p e} (hf : is_finite f = true)
    (hg : is_finite g = true) (hr : B2R f = B2R g) (hs : Bsign f = Bsign g) : f = g := by
  by_cases h : is_finite_pos0 p e f = true ∧ is_finite_pos0 p e g = true
  · exact B2R_inj_pos0 p e f g h.1 h.2 hr
  have finite_zero (m : Positive) (i : Int) : ((m.val : ℝ) * 2^i) ≠ 0 :=
    (mul_pos (Nat.cast_pos.mpr m.property) (zpow_pos (by norm_num) _)).ne'
  have hs0 (s : Bool) (m : Positive) (i : Int) : signed s ((m.val : ℝ) * 2^i) ≠ 0 := by
    cases s <;> simpa only [signed,ite_true,ite_false,Bool.false_eq_true,neg_ne_zero] using finite_zero m i
  cases f <;> cases g <;> simp only [B2R,B2F,is_finite,Bsign,is_finite_pos0] at * <;>
    first | contradiction | (exfalso; exact hs0 _ _ _ hr) | (exfalso; exact hs0 _ _ _ hr.symm) | congr 1

private theorem FF_inj {p e} {f g : binary_float p e} (h : B2FF f = B2FF g) : f = g := by
  cases f <;> cases g <;> simp_all [B2FF]

private theorem ofRat_zero {p e} (hp : 0 < p) (he : p < e) (md : Mode) (s : Bool) :
    ofRat p e hp he md 0 s = .B754_zero s := by
  have h : round_mode md (0 : ℚ) = 0 := by simpa only [Int.cast_zero] using mode_intCast (K := ℚ) md 0
  simp [ofRat,h]

private theorem ofRat_sign_irrel {p e} (hp : 0 < p) (he : p < e) (md : Mode) (q : ℚ) (a b : Bool)
    (h : q = 0 → a = b) : ofRat p e hp he md q a = ofRat p e hp he md q b := by
  by_cases hq : q = 0
  · rw [h hq]
  · simp only [ofRat,if_neg hq]

private theorem BofZ_zero (p e) (hp : 0 < p) (he : p < e) : BofZ p e hp he 0 = .B754_zero false := by
  simp [BofZ,binary_normalize,ofRat_zero]

private theorem BofZ_Q {p e} (hp : 0 < p) (he : p < e) {n : Int} (hn : integer_representable p e n) :
    B2Q (BofZ p e hp he n) = (n : ℚ) := by
  have H := (BofZ_representable _ _ hp he _ hn).1
  exact_mod_cast (show ((B2Q (BofZ p e hp he n) : ℚ) : ℝ) = (n : ℝ) by simpa only [Flocq.cast_B2Q] using H)

private theorem BofZ_nonzero {p e} (hp : 0 < p) (he : p < e) {n : Int} (hn : integer_representable p e n)
    (h0 : n ≠ 0) : is_finite_strict (BofZ p e hp he n) = true := by
  obtain ⟨hr,hf,_⟩ := BofZ_representable _ _ hp he n hn
  cases h : BofZ p e hp he n <;> rw [h] at hf hr <;> first | rfl | contradiction |
    (change 0 = (n : ℝ) at hr; exact False.elim (h0 (by exact_mod_cast hr.symm)))

theorem BofZ_plus : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (x y : Int),
    integer_representable p e x → integer_representable p e y → Bplus p e hp he nan .mode_NE
    (BofZ p e hp he x) (BofZ p e hp he y) = BofZ p e hp he (x + y) := by
  intro p e hp he nan x y hx hy
  by_cases hx0 : x = 0
  · subst x; rw [BofZ_zero,zero_add]
    by_cases hy0 : y = 0
    · subst y; rw [BofZ_zero]; rfl
    · have h₂ := BofZ_nonzero hp he hy hy0
      cases h : BofZ p e hp he y <;> rw [h] at h₂ <;> first | rfl | contradiction
  by_cases hy0 : y = 0
  · subst y; have hs := BofZ_nonzero hp he hx hx0
    rw [BofZ_zero,add_zero]; cases h : BofZ p e hp he x <;> rw [h] at hs <;> first | rfl | contradiction
  have h₁ := BofZ_nonzero hp he hx hx0
  have h₂ := BofZ_nonzero hp he hy hy0
  have hq₁ := BofZ_Q hp he hx
  have hq₂ := BofZ_Q hp he hy
  cases h₁' : BofZ p e hp he x <;> rw [h₁'] at h₁ hq₁ <;> try contradiction
  cases h₂' : BofZ p e hp he y <;> rw [h₂'] at h₂ hq₂ <;> try contradiction
  simp [Bplus,hq₁,hq₂,BofZ,binary_normalize]

theorem BofZ_mult : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (x y : Int),
    integer_representable p e x → integer_representable p e y → 0 < y → Bmult p e hp he nan
    .mode_NE (BofZ p e hp he x) (BofZ p e hp he y) = BofZ p e hp he (x * y) := by
  intro p e hp he nan x y hx hy hypos
  have h₂ := BofZ_nonzero hp he hy hypos.ne'
  have hs := (BofZ_representable _ _ hp he y hy).2.2
  by_cases hx0 : x = 0
  · subst x; rw [zero_mul,BofZ_zero]
    cases h : BofZ p e hp he y <;> rw [h] at h₂ hs <;> try contradiction
    simp only [Bsign,decide_eq_false hypos.not_gt] at hs
    simp [Bmult,Bsign,hs]
  have h₁ := BofZ_nonzero hp he hx hx0
  have hq₁ := BofZ_Q hp he hx
  have hq₂ := BofZ_Q hp he hy
  cases h₁' : BofZ p e hp he x <;> rw [h₁'] at h₁ hq₁ <;> try contradiction
  cases h₂' : BofZ p e hp he y <;> rw [h₂'] at h₂ hq₂ <;> try contradiction
  simp only [Bmult,hq₁,hq₂,BofZ,binary_normalize,zpow_zero,mul_one,Int.cast_mul]
  apply ofRat_sign_irrel; intro h; exfalso
  exact (mul_ne_zero (by exact_mod_cast hx0) (by exact_mod_cast hypos.ne')) h

theorem Bconv_BofZ : ∀ (p₁ e₁ p₂ e₂ : Int) (h₁ : 0 < p₁) (h₂ : 0 < p₂) (l₁ : p₁ < e₁) (l₂ : p₂ < e₂)
    (nan : ConvNaN p₁ e₁ p₂ e₂) (n : Int), integer_representable p₁ e₁ n → Bconv p₁ e₁ p₂ e₂ h₂
    l₂ nan .mode_NE (BofZ p₁ e₁ h₁ l₁ n) = BofZ p₂ e₂ h₂ l₂ n := by
  intro p₁ e₁ p₂ e₂ h₁ h₂ l₁ l₂ nan n hn
  by_cases h0 : n = 0
  · subst n; rw [BofZ_zero,BofZ_zero]; rfl
  have hb := BofZ_nonzero h₁ l₁ hn h0
  have hq := BofZ_Q h₁ l₁ hn
  cases h : BofZ p₁ e₁ h₁ l₁ n <;> rw [h] at hq hb <;> try contradiction
  simp only [Bconv,hq,BofZ,binary_normalize,zpow_zero,mul_one]
  apply ofRat_sign_irrel; intro h; exact False.elim (h0 (by exact_mod_cast h))

theorem Bconv_narrow_widen : ∀ (p₁ e₁ p₂ e₂ : Int) (h₁ : 0 < p₁) (h₂ : 0 < p₂) (l₁ : p₁ < e₁) (l₂ : p₂ <
    e₂), p₁ ≤ p₂ → e₁ ≤ e₂ → ∀ (a : ConvNaN p₂ e₂ p₁ e₁) (b : ConvNaN p₁ e₁ p₂ e₂) (m : Mode) (f
    : binary_float p₁ e₁), is_nan f = false → Bconv p₂ e₂ p₁ e₁ h₁ l₁ a m (Bconv p₁ e₁ p₂ e₂ h₂
    l₂ b m f) = f := by
  intro p₁ e₁ p₂ e₂ h₁ h₂ l₁ l₂ hw he a b md f hn
  by_cases hf : is_finite f = true
  · obtain ⟨hr,hg,hs⟩ := Bconv_widen_exact _ _ _ _ h₁ h₂ l₂ hw he b md f hf
    have ha := Bconv_correct _ _ _ _ h₁ l₁ a md _ hg
    simp only [hr,format_round (bounds_format h₁ le_rfl le_rfl f),if_pos (finite_lt f),hs] at ha
    exact finite_inj ha.2.1 hf ha.1 ha.2.2
  · cases f <;> first | rfl | contradiction

private def positiveParseSpec {p e} (md : Mode) (q : ℚ) (f : binary_float p e) : Prop :=
  let r := Flocq.round (fexp p e) (round_mode md) (q : ℝ)
  if |r| < (2 : ℝ)^e then B2R f = r ∧ is_finite f = true ∧ Bsign f = false
  else B2FF f = binary_overflow p e md false

private theorem positiveParse {p e} (hp : 0 < p) (he : p < e) (q : ℚ) (hq : 0 < q) :
    positiveParseSpec .mode_NE q (ofRat p e hp he .mode_NE q false) := by
  simpa only [positiveParseSpec,if_neg hq.ne', decide_eq_false hq.not_gt] using ofRat_correct p e hp he .mode_NE q false

theorem Bparse_correct (p e : Int) (hp : 0 < p) (he : p < e) (b m : Positive) (i : Int)
    (hb : 2 ≤ (b.val : Int)) :
    let base : Radix := ⟨(b.val : Int), hb⟩
    let r := Flocq.round (fexp p e) (round_mode .mode_NE) ((m.val : ℝ) * (base.val : ℝ)^i)
    if |r| < (2 : ℝ)^e then B2R (Bparse p e hp he b m i) = r ∧
      is_finite (Bparse p e hp he b m i) = true ∧ Bsign (Bparse p e hp he b m i) = false
    else B2FF (Bparse p e hp he b m i) = .F754_infinity false := by
  let base : Radix := ⟨(b.val : Int), hb⟩
  dsimp only
  by_cases h0 : i = 0
  · subst i; simpa [Bparse,binary_overflow,overflow_to_inf,(Int.natCast_nonneg m.val).not_gt]
      using BofZ_correct p e hp he m.val
  · by_cases hi : 0 < i
    · by_cases hl : i * log2 b.val < e
      · simp only [Bparse,if_neg h0,if_pos hi,if_pos hl]
        lift i to Nat using hi.le
        simpa [BofZ,binary_normalize,positiveParseSpec,binary_overflow,overflow_to_inf] using
          positiveParse hp he ((m.val : ℚ) * (b.val : ℚ)^i) (mul_pos (Nat.cast_pos.mpr m.property) (pow_pos (Nat.cast_pos.mpr b.property) _))
      · have H := round_integer_overflow p e hp he base i m hi (le_of_not_gt hl)
        have F := H.trans (le_abs_self _)
        simp only [base,Int.cast_natCast] at F
        simp only [Bparse,if_neg h0,if_pos hi,if_neg hl,Int.cast_natCast, if_neg (not_lt.mpr F),B2FF]
    · have hn : i < 0 := by omega
      by_cases hl : i * log2 b.val + log2up m.val < emin p e
      · have H := round_integer_underflow p e hp base i m hn hl
        simp only [base,Int.cast_natCast] at H
        simp [Bparse,h0,hi,hl,H,B2R,B2F,Bsign,is_finite,zpow_pos (by norm_num : (0:ℝ)<2) e]
      · have hn' : (b.val : ℝ)^i = ((b.val : ℝ)^i.natAbs)⁻¹ := by
          conv_lhs => rw [show i = -(i.natAbs : Int) by omega, zpow_neg,zpow_natCast]
        simp only [Bparse,if_neg h0,if_neg hi,if_neg hl,Int.cast_natCast,hn']
        have hb' : (0 : ℚ) < b.val := Nat.cast_pos.mpr b.property
        have hm' : (0 : ℚ) < m.val := Nat.cast_pos.mpr m.property
        have H := positiveParse hp he ((m.val : ℚ) / (b.val : ℚ)^i.natAbs) (div_pos hm' (pow_pos hb' _))
        simpa only [positiveParseSpec,roundQuotient,signed,if_false,Bool.false_eq_true,sub_zero,zpow_zero,
          mul_one,Nat.cast_pow,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,binary_overflow,overflow_to_inf,if_true,
          Int.cast_natCast,div_eq_mul_inv,Rat.cast_mul,Rat.cast_inv] using H

private theorem B2Q_neg {p e} (f : binary_float p e) : B2Q (Flocq.neg f) = - B2Q f := by
  cases f with
  | B754_finite s m i h => cases s <;> simp [Flocq.neg,B2Q,B2F,signed]
  | _ => simp [Flocq.neg,B2Q,B2F]

private theorem neg_repr {p e} (hp : 0 < p) (he : p < e) {n : Int} (hn : integer_representable p e n)
    (h0 : n ≠ 0) : Flocq.neg (BofZ p e hp he n) = BofZ p e hp he (-n) := by
  have ⟨hr,hf,hs⟩ := BofZ_representable _ _ hp he n hn
  have ⟨hr',hf',hs'⟩ := BofZ_representable _ _ hp he (-n) (integer_representable_opp _ _ _ hn)
  refine finite_inj ?_ hf' ?_ ?_
  · cases h : BofZ p e hp he n <;> rw [h] at hf <;> first | rfl | contradiction
  · have h := congrArg (fun x : ℚ ↦ (x : ℝ)) (B2Q_neg (BofZ p e hp he n))
    simpa only [Flocq.cast_B2Q,Rat.cast_neg,hr,hr',Int.cast_neg] using h
  · rw [hs']
    have hh : Bsign (Flocq.neg (BofZ p e hp he n)) = !Bsign (BofZ p e hp he n) := by cases BofZ p e hp he n <;> rfl
    rw [hh,hs]; by_cases h : n < 0 <;> simp [h] <;> omega

theorem BofZ_minus : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (x y : Int),
    integer_representable p e x → integer_representable p e y → Bminus p e hp he nan .mode_NE
    (BofZ p e hp he x) (BofZ p e hp he y) = BofZ p e hp he (x - y) := by
  intro p e hp he nan x y hx hy
  by_cases hy0 : y = 0
  · subst y; rw [sub_zero,BofZ_zero]
    by_cases hx0 : x = 0
    · subst x; rw [BofZ_zero]; rfl
    · have H := BofZ_nonzero hp he hx hx0
      cases h : BofZ p e hp he x <;> rw [h] at H <;> first | rfl | contradiction
  have h₂ := BofZ_nonzero hp he hy hy0
  by_cases hx0 : x = 0
  · subst x; rw [zero_sub,BofZ_zero, ← neg_repr hp he hy hy0]
    cases h : BofZ p e hp he y <;> rw [h] at h₂ <;> first | rfl | contradiction
  have h₁ := BofZ_nonzero hp he hx hx0
  have h₃ := BofZ_Q hp he hx
  have h₄ := B2Q_neg (BofZ p e hp he y)
  rw [BofZ_Q hp he hy] at h₄
  cases h₁' : BofZ p e hp he x <;> rw [h₁'] at h₁ h₃ <;> try contradiction
  cases h₂' : BofZ p e hp he y <;> rw [h₂'] at h₂ h₄ <;> try contradiction
  simp only [Flocq.neg] at h₄
  simp [Bminus,Bplus,Flocq.neg,h₃,h₄,BofZ,binary_normalize,sub_eq_add_neg]

theorem Bmult2_Bplus : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (a b : Nan₂ p e) (m : Mode) (f :
    binary_float p e), (∀ x y, is_nan x = true → is_finite y = true → a x x = b x y) → Bplus p e
    hp he a m f f = Bmult p e hp he b m f (BofZ p e hp he 2) := by
  intro p e hp he a b md f hn
  have h₂ := integer_representable_2p p e hp he 1 (by omega)
  change integer_representable p e 2 at h₂
  have hq := BofZ_Q hp he h₂
  have hs := (BofZ_representable _ _ hp he _ h₂).2.2
  have hf := BofZ_nonzero hp he h₂ (by decide)
  cases h : BofZ p e hp he 2 <;> rw [h] at hf hq hs <;> try contradiction
  rename_i s m i hm
  change s = false at hs; subst s
  cases f with
  | B754_zero s => cases s <;> simp [Bplus,Bmult,Bsign]
  | B754_infinity s => cases s <;> simp [Bplus,Bmult,Bsign]
  | B754_nan => exact congrArg Subtype.val (hn _ _ rfl rfl)
  | B754_finite s n j h =>
    let f : binary_float p e := .B754_finite s n j h
    have hnz : B2Q f ≠ 0 := by cases s <;> simp [f,B2Q,B2F,signed,n.property.ne',zpow_ne_zero _ (by norm_num : (2:ℚ) ≠ 0)]
    simp only [Bplus,Bmult,hq,Bsign,Bool.xor_false,Int.cast_ofNat]
    change ofRat p e hp he md (B2Q f+B2Q f) _ = ofRat p e hp he md (B2Q f*2) _
    rw [show B2Q f+B2Q f = B2Q f*2 by ring]
    apply ofRat_sign_irrel; intro hh; exact False.elim (hnz (by linarith))

theorem ZofB_minus : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (m : Mode) (f :
    binary_float p e) (a b : Int), ZofB p e f = some a → (0 ≤ a ∧ a < 2 * b) → b ≤ pow2 p → (b :
    ℝ) ≤ B2R f → ZofB p e (Bminus p e hp he nan m f (BofZ p e hp he b)) = some (a - b) := by
  intro p e hp he nan md f a b ha hab hb hba
  have hbpos : 0 < b := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hbr := integer_representable_n p e hp he b (by have := pow2_pos hp.le; omega)
  have hbf := BofZ_nonzero hp he hbr hbpos.ne'
  have hq := B2Q_neg (BofZ p e hp he b)
  rw [BofZ_Q hp he hbr] at hq
  have hff : is_finite_strict f = true := by cases f <;> first | rfl | (change (b:ℝ) ≤ 0 at hba; linarith)
  have hua := (ZofB_range_nonneg p e hp he f a ha hab.1).2
  have hu : B2R f ≤ 2 * (b : ℝ) := by
    apply hua.le.trans; exact_mod_cast (show a+1 ≤ 2*b by omega)
  have hformat := sterbenz hp (bounds_format hp le_rfl le_rfl f) hbr.2 hbR.le hba hu
  have hround := format_round hformat md
  have hbound : |B2R f - b| < (2:ℝ)^e := by
    rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    have hb' : (b:ℝ) ≤ (2:ℝ)^p := by rw [← pow2_cast hp.le]; exact_mod_cast hb
    exact lt_of_le_of_lt (by linarith : B2R f - b ≤ (2:ℝ)^p) (zpow_lt_zpow_right₀ (by norm_num) he)
  have hr := ofRat_correct p e hp he md (B2Q f - (b:ℚ)) (decide (md = .mode_DN))
  simp only [Rat.cast_sub,Rat.cast_intCast,Flocq.cast_B2Q,hround,if_pos hbound] at hr
  have hid : Bminus p e hp he nan md f (BofZ p e hp he b) = ofRat p e hp he md (B2Q f - (b:ℚ)) (decide (md = .mode_DN)) := by
    cases f <;> try contradiction
    cases h : BofZ p e hp he b <;> rw [h] at hbf hq <;> try contradiction
    simp only [Flocq.neg] at hq
    simp [Bminus,Bplus,Flocq.neg,hq,sub_eq_add_neg]
  have ht := trunc_of_some ha
  rw [hid,ZofB_correct,hr.2.1,hr.1]
  simp only [if_true,Option.some.injEq,Ztrunc,if_neg (not_lt.mpr (sub_nonneg.mpr hba)),Int.floor_sub_intCast]
  simp only [Ztrunc,if_neg (not_lt.mpr (hbR.le.trans hba))] at ht
  rw [ht]

theorem ZofB_range_minus : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (m : Mode) (f :
    binary_float p e) (a b : Int), ZofB_range p e f 0 (2 * b - 1) = some a → b ≤ pow2 p → (b :
    ℝ) ≤ B2R f → ZofB_range p e (Bminus p e hp he nan m f (BofZ p e hp he b)) (-b) (b - 1) =
    some (a - b) := by
  intro p e hp he nan md f a b h hb hf
  obtain ⟨hl,hu,ha⟩ := ZofB_range_inversion _ _ _ _ _ _ h
  have H := ZofB_minus _ _ hp he nan md f a b ha ⟨hl,by omega⟩ hb hf
  simp [ZofB_range,H,show -b ≤ a-b by omega,show a-b < b by omega]

private theorem compare_cases {p e} (x y : binary_float p e) : Bcompare x y =
    (if is_nan x || is_nan y then none else if !is_finite x then
      if !is_finite y then some (compare (Bsign y) (Bsign x))
      else some (if Bsign x then .lt else .gt)
    else if !is_finite y then some (if Bsign y then .gt else .lt)
    else some (compare (B2Q x) (B2Q y))) := by cases x <;> cases y <;> rfl

theorem Bcompare_Bconv_widen : ∀ (p₁ e₁ p₂ e₂ : Int) (h₁ : 0 < p₁) (h₂ : 0 < p₂) (l₂ : p₂ < e₂), p₁ ≤ p₂
    → e₁ ≤ e₂ → ∀ (nan : ConvNaN p₁ e₁ p₂ e₂) (m : Mode) (x y : binary_float p₁ e₁), Bcompare
    (Bconv p₁ e₁ p₂ e₂ h₂ l₂ nan m x) (Bconv p₁ e₁ p₂ e₂ h₂ l₂ nan m y) = Bcompare x y := by
  intro p₁ e₁ p₂ e₂ h₁ h₂ l₂ hw he nan md x y
  let cv := Bconv p₁ e₁ p₂ e₂ h₂ l₂ nan md
  have desc (f : binary_float p₁ e₁) : is_nan (cv f) = is_nan f ∧ (is_nan f = false →
      is_finite (cv f) = is_finite f ∧ Bsign (cv f) = Bsign f ∧ B2Q (cv f) = B2Q f) := by
    by_cases hf : is_finite f = true
    · obtain ⟨hr,hg,hs⟩ := Bconv_widen_exact _ _ _ _ h₁ h₂ l₂ hw he nan md f hf
      have hq : B2Q (cv f) = B2Q f := by exact_mod_cast (show ((B2Q (cv f) : ℚ) : ℝ) = ((B2Q f : ℚ) : ℝ) by simpa only [cast_B2Q] using hr)
      exact ⟨(is_finite_not_is_nan _ _ _ hg).trans (is_finite_not_is_nan _ _ _ hf).symm,fun _ ↦ ⟨hg.trans hf.symm,hs,hq⟩⟩
    · cases f with
      | B754_infinity => exact ⟨rfl,fun _ ↦ ⟨rfl,rfl,rfl⟩⟩
      | B754_nan => exact ⟨(nan _).property,nofun⟩
      | _ => contradiction
  change Bcompare (cv x) (cv y) = Bcompare x y
  rw [compare_cases,compare_cases _ y,(desc x).1,(desc y).1]
  cases hx : is_nan x <;> cases hy : is_nan y <;> simp only [Bool.false_or,Bool.or_true, Bool.true_or,if_true,if_false]
  obtain ⟨h₁,h₂,h₃⟩ := (desc x).2 hx
  obtain ⟨h₄,h₅,h₆⟩ := (desc y).2 hy
  rw [h₁,h₂,h₃,h₄,h₅,h₆]

theorem Zrnd_odd_int : ∀ n k : Int, 0 ≤ k → Zrnd_odd ((n : ℝ) * (2 : ℝ) ^ (-k)) * pow2 k = int_round_odd
    n k := by
  exact odd_scaled_int

theorem int_round_odd_shifts : ∀ x k : Int, 0 ≤ k → int_round_odd x k = shiftl (if x % pow2 k = 0 then
    shiftr x k else Int.lor (shiftr x k) 1) k := by
  exact odd_shifts

theorem int_round_odd_bits : ∀ x y k : Int, 0 ≤ k → (∀ i, (0 ≤ i ∧ i < k) → testbit y i = false) →
    testbit y k = (if x % pow2 k = 0 then testbit x k else true) → (∀ i, k < i → testbit y i =
    testbit x i) → int_round_odd x k = y := by
  exact odd_bits

theorem round_odd_flt : ∀ (p e : Int) (hp : 0 < p) (p' emin' : Int) (x : ℝ) (c : Int → Bool), 1 < p → 1
    < p' → p + 2 ≤ p' → emin' ≤ emin p e - 2 → round (fexp p e) (Znearest c) (round (FLT_exp
    emin' p') Zrnd_odd x) = round (fexp p e) (Znearest c) x := by
  exact odd_flt

theorem round_odd_fix : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (x : ℝ) (k : Int) (c : Int → Bool), 1 <
    p → 0 ≤ k → (2 : ℝ) ^ (p + k + 1) ≤ |x| → round (fexp p e) (Znearest c) (round (fun _ ↦ k)
    Zrnd_odd x) = round (fexp p e) (Znearest c) x := by
  exact odd_fix

theorem BofZ_round_odd : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (x k : Int), 1 < p → |x| ≤ (pow2 e -
    pow2 (e - p)) → (0 ≤ k ∧ k ≤ e - p) → pow2 (p + k + 1) ≤ |x| → (BofZ p e hp he x) = BofZ p e
    hp he (int_round_odd x k) := by
  intro p e hp he x k hp' hx hk hbig
  let u := pow2 e - pow2 (e-p)
  have hd : pow2 k ∣ u := by
    unfold u; rw [int_upper_bound_eq _ _ hp he]
    apply dvd_mul_of_dvd_right
    refine ⟨pow2 (e-p-k), ?_⟩
    rw [← pow2_add hk.1 (by omega)]; congr 1; omega
  have hy : |int_round_odd x k| ≤ u := by
    obtain ⟨a,b⟩ := abs_le.mp hx
    apply abs_le.mpr
    constructor
    · rw [← int_round_odd_exact k (-u) hk.1 (dvd_neg.mpr hd)]
      exact int_round_odd_le _ _ _ hk.1 a
    · rw [← int_round_odd_exact k u hk.1 hd]
      exact int_round_odd_le _ _ _ hk.1 b
  apply BofZ_finite_equal p e hp he _ _ hx hy
  rw [(BofZ_finite p e hp he x hx).1, (BofZ_finite p e hp he _ hy).1]
  have hodd : (int_round_odd x k : ℝ) = Flocq.round (fun _ ↦ k) Zrnd_odd (x : ℝ) := by
    rw [← Zrnd_odd_int x k hk.1,Int.cast_mul,pow2_cast hk.1]
    simp only [Flocq.round,cexp,zpow_neg,div_eq_mul_inv]
  rw [hodd]
  apply Eq.symm
  simp only [round_mode]
  apply round_odd_fix p e hp he (x : ℝ) k _ hp' hk.1
  rw [← pow2_cast (by omega : 0 ≤ p+k+1)]; exact_mod_cast hbig

private theorem ofRat_eq_round {p e} (hp : 0 < p) (he : p < e) (md : Mode)
    {x y : ℚ} {a b : Bool}
    (h : Flocq.round (fexp p e) (round_mode md) (x : ℝ) = Flocq.round (fexp p e) (round_mode md) (y : ℝ))
    (hs : (if x = 0 then a else decide (x < 0)) = (if y = 0 then b else decide (y < 0))) :
    ofRat p e hp he md x a = ofRat p e hp he md y b := by
  have hx := ofRat_correct p e hp he md x a
  have hy := ofRat_correct p e hp he md y b
  dsimp only at hx hy
  rw [h,hs] at hx
  split at hx <;> rename_i hc
  · rw [if_pos hc] at hy
    exact finite_inj hx.2.1 hy.2.1 (hx.1.trans hy.1.symm) (hx.2.2.trans hy.2.2.symm)
  · rw [if_neg hc] at hy; exact FF_inj (hx.trans hy.symm)

theorem BofZ_mult_2p : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (x k : Int), |x| ≤ (pow2
    e - pow2 (e - p)) → pow2 p ≤ |x| → (0 ≤ k ∧ k ≤ e - 1) → Bmult p e hp he nan .mode_NE (BofZ
    p e hp he x) (BofZ p e hp he (pow2 k)) = BofZ p e hp he (x * pow2 k) := by
  intro p e hp he nan x k hx hbig hk
  let f := BofZ p e hp he x
  let g := BofZ p e hp he (pow2 k)
  let b := pow2 k
  have hb : 0 < b := pow2_pos hk.1
  have hx0 : x ≠ 0 := by have := pow2_pos hp.le; intro h; simp [h] at hbig; omega
  have hrepr := integer_representable_2p p e hp he k hk
  have hgf := BofZ_nonzero hp he hrepr hb.ne'
  have hq : B2Q g = (b : ℚ) := BofZ_Q hp he hrepr
  have ⟨hr,hf,hs⟩ := BofZ_finite p e hp he x hx
  change B2R f = _ at hr
  have hmag : (2:ℝ)^p ≤ |(x : ℝ)| := by rw [← pow2_cast hp.le]; exact_mod_cast hbig
  have hsign : (if B2Q f*b = 0 then xor (Bsign f) (Bsign g) else decide (B2Q f*b < 0)) =
      (if ((x*b : Int) : ℚ) = 0 then false else decide (((x*b : Int) : ℚ) < 0)) := by
    have hbr : (0 : ℚ) < b := by exact_mod_cast hb
    rcases lt_or_gt_of_ne hx0 with hn | hn
    · have H := round_le_neg_pow (e := e) hp .mode_NE (x:ℝ) 0 (by unfold emin; omega) (by simpa using (show (x:ℝ) ≤ -1 by exact_mod_cast (show x ≤ -1 by omega)))
      rw [← hr] at H
      have hqf : B2Q f < 0 := by exact_mod_cast (show ((B2Q f : ℚ):ℝ) < 0 by rw [Flocq.cast_B2Q]; norm_num at H; linarith)
      have hq' : (x : ℚ) < 0 := by exact_mod_cast hn
      simp [Int.cast_mul,(mul_neg_of_neg_of_pos hqf hbr).ne,(mul_neg_of_neg_of_pos hq' hbr).ne,mul_neg_of_neg_of_pos hqf hbr,mul_neg_of_neg_of_pos hq' hbr]
    · have H := round_ge_pow (e := e) hp .mode_NE (x:ℝ) 0 (by unfold emin; omega) (by simpa using (show (1:ℝ) ≤ x by exact_mod_cast (show 1 ≤ x by omega)))
      rw [← hr] at H
      have hqf : 0 < B2Q f := by exact_mod_cast (show (0:ℝ) < ((B2Q f : ℚ):ℝ) by rw [Flocq.cast_B2Q]; norm_num at H; linarith)
      have hq' : (0 : ℚ) < x := by exact_mod_cast hn
      simp [Int.cast_mul,(mul_pos hqf hbr).ne',(mul_pos hq' hbr).ne',(mul_pos hqf hbr).not_gt,(mul_pos hq' hbr).not_gt]
  have hround : Flocq.round (fexp p e) (round_mode .mode_NE) ((B2Q f * b : ℚ) : ℝ) =
      Flocq.round (fexp p e) (round_mode .mode_NE) ((x*b : Int) : ℝ) := by
    simp only [Rat.cast_mul,Rat.cast_intCast,Flocq.cast_B2Q,Int.cast_mul]
    rw [show (b:ℝ) = 2^k from pow2_cast hk.1,round_scale_large hp he _ hmag hk.1]
    rw [format_round (format_scale (bounds_format hp le_rfl le_rfl f) hk.1), hr]
  have hspec := ofRat_eq_round hp he .mode_NE (x := B2Q f * b) (y := (x*b : Int)) (by simpa only [Rat.cast_intCast] using hround) hsign
  have hfs : is_finite_strict f = true := by
    cases H : f with
    | B754_finite => rfl
    | B754_zero s =>
      rw [H] at hr
      rcases lt_or_gt_of_ne hx0 with hn | hn
      · have H' := round_le_neg_pow (e := e) hp .mode_NE (x:ℝ) 0 (by unfold emin; omega) (by simpa using (show (x:ℝ) ≤ -1 by exact_mod_cast (show x ≤ -1 by omega)))
        rw [← hr] at H'; norm_num [B2R,B2F] at H'
      · have H' := round_ge_pow (e := e) hp .mode_NE (x:ℝ) 0 (by unfold emin; omega) (by simpa using (show (1:ℝ) ≤ x by exact_mod_cast (show 1 ≤ x by omega)))
        rw [← hr] at H'; norm_num [B2R,B2F] at H'
    | _ => change is_finite f = true at hf; rw [H] at hf; contradiction
  change Bmult p e hp he nan .mode_NE f g = BofZ p e hp he (x*b)
  change is_finite_strict g = true at hgf
  cases H : f <;> rw [H] at hfs hspec <;> try contradiction
  cases G : g <;> rw [G] at hgf hspec hq <;> try contradiction
  simpa only [Bmult,hq,BofZ,binary_normalize,zpow_zero,mul_one] using hspec

end Vellvm.Numeric.IEEE754_extra
