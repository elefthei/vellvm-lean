import PortChecks.SourceType
import Vellvm.Numeric.IEEE754_extra

open Vellvm Vellvm.Numeric.Flocq Vellvm.Numeric.IEEE754_extra

noncomputable section

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|is_finite_not_is_nan"
  is_finite_not_is_nan : ∀ (p e : Int) (f : binary_float p e), is_finite f = true → is_nan f =
    false

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|is_finite_strict_finite"
  is_finite_strict_finite : ∀ (p e : Int) (f : binary_float p e), is_finite_strict f = true →
    is_finite f = true

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bsign_pos0"
  Bsign_pos0 : ∀ (p e : Int) (x : binary_float p e), is_finite_pos0 p e x = true → Bsign x =
    decide (B2R x < 0)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|B2R_inj_pos0"
  B2R_inj_pos0 : ∀ (p e : Int) (x y : binary_float p e), is_finite_pos0 p e x = true →
    is_finite_pos0 p e y = true → B2R x = B2R y → x = y

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Beq_dec"
  Beq_dec : ∀ (p e : Int) (a b : binary_float p e), Decidable (a = b)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|int_upper_bound_eq"
  int_upper_bound_eq : ∀ (p e : Int) (hp : 0 < p) (he : p < e), (pow2 e - pow2 (e - p)) = (pow2 p
    - 1) * pow2 (e - p)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|integer_representable_n2p"
  integer_representable_n2p : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n k : Int), (-pow2 p < n ∧
    n < pow2 p) → 0 ≤ k → k ≤ e - p → integer_representable p e (n * pow2 k)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|integer_representable_2p"
  integer_representable_2p : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (k : Int), (0 ≤ k ∧ k ≤ e -
    1) → integer_representable p e (pow2 k)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|integer_representable_opp"
  integer_representable_opp : ∀ (p e : Int) (n : Int), integer_representable p e n →
    integer_representable p e (-n)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|integer_representable_n2p_wide"
  integer_representable_n2p_wide : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n k : Int), (-pow2 p ≤
    n ∧ n ≤ pow2 p) → 0 ≤ k → k < e - p → integer_representable p e (n * pow2 k)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|integer_representable_n"
  integer_representable_n : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int), (-pow2 p ≤ n ∧ n ≤
    pow2 p) → integer_representable p e n

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|round_int_no_overflow"
  round_int_no_overflow : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int), |n| ≤ (pow2 e - pow2
    (e - p)) → |round (fexp p e) (round_mode .mode_NE) (n : ℝ)| < (2 : ℝ) ^ e

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|BofZ_correct"
  BofZ_correct : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int), if |round (fexp p e)
    (round_mode .mode_NE) (n : ℝ)| < (2 : ℝ) ^ e then
    B2R (BofZ p e hp he n) = round (fexp p e) (round_mode .mode_NE) (n : ℝ) ∧ is_finite (BofZ p
    e hp he n) = true ∧ Bsign (BofZ p e hp he n) = decide (n < 0)
    else B2FF (BofZ p e hp he n) = binary_overflow p e .mode_NE (decide (n < 0))

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|BofZ_finite"
  BofZ_finite : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int), |n| ≤ (pow2 e - pow2 (e - p)) →
    B2R (BofZ p e hp he n) = round (fexp p e) (round_mode .mode_NE) (n : ℝ) ∧ is_finite (BofZ p
    e hp he n) = true ∧ Bsign (BofZ p e hp he n) = decide (n < 0)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|BofZ_representable"
  BofZ_representable : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int), integer_representable p
    e n → B2R (BofZ p e hp he n) = (n : ℝ) ∧ is_finite (BofZ p e hp he n) = true ∧ Bsign (BofZ p
    e hp he n) = decide (n < 0)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|BofZ_exact"
  BofZ_exact : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int), (-pow2 p ≤ n ∧ n ≤ pow2 p) → B2R
    (BofZ p e hp he n) = (n : ℝ) ∧ is_finite (BofZ p e hp he n) = true ∧ Bsign (BofZ p e hp he
    n) = decide (n < 0)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|BofZ_finite_pos0"
  BofZ_finite_pos0 : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int), |n| ≤ (pow2 e - pow2 (e -
    p)) → is_finite_pos0 p e (BofZ p e hp he n) = true

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|BofZ_finite_equal"
  BofZ_finite_equal : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (x y : Int), |x| ≤ (pow2 e - pow2 (e
    - p)) → |y| ≤ (pow2 e - pow2 (e - p)) → B2R (BofZ p e hp he x) = B2R (BofZ p e hp he y) →
    (BofZ p e hp he x) = (BofZ p e hp he y)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|BofZ_plus"
  BofZ_plus : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (x y : Int),
    integer_representable p e x → integer_representable p e y → Bplus p e hp he nan .mode_NE
    (BofZ p e hp he x) (BofZ p e hp he y) = BofZ p e hp he (x + y)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|BofZ_minus"
  BofZ_minus : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (x y : Int),
    integer_representable p e x → integer_representable p e y → Bminus p e hp he nan .mode_NE
    (BofZ p e hp he x) (BofZ p e hp he y) = BofZ p e hp he (x - y)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|BofZ_mult"
  BofZ_mult : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (x y : Int),
    integer_representable p e x → integer_representable p e y → 0 < y → Bmult p e hp he nan
    .mode_NE (BofZ p e hp he x) (BofZ p e hp he y) = BofZ p e hp he (x * y)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|BofZ_mult_2p"
  BofZ_mult_2p : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (x k : Int), |x| ≤ (pow2
    e - pow2 (e - p)) → pow2 p ≤ |x| → (0 ≤ k ∧ k ≤ e - 1) → Bmult p e hp he nan .mode_NE (BofZ
    p e hp he x) (BofZ p e hp he (pow2 k)) = BofZ p e hp he (x * pow2 k)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|round_odd_flt"
  round_odd_flt : ∀ (p e : Int) (hp : 0 < p) (p' emin' : Int) (x : ℝ) (c : Int → Bool), 1 < p → 1
    < p' → p + 2 ≤ p' → emin' ≤ emin p e - 2 → round (fexp p e) (Znearest c) (round (FLT_exp
    emin' p') Zrnd_odd x) = round (fexp p e) (Znearest c) x

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|round_odd_fix"
  round_odd_fix : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (x : ℝ) (k : Int) (c : Int → Bool), 1 <
    p → 0 ≤ k → (2 : ℝ) ^ (p + k + 1) ≤ |x| → round (fexp p e) (Znearest c) (round (fun _ ↦ k)
    Zrnd_odd x) = round (fexp p e) (Znearest c) x

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Zrnd_odd_int"
  Zrnd_odd_int : ∀ n k : Int, 0 ≤ k → Zrnd_odd ((n : ℝ) * (2 : ℝ) ^ (-k)) * pow2 k = int_round_odd
    n k

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|int_round_odd_le"
  int_round_odd_le : ∀ k x y : Int, 0 ≤ k → x ≤ y → int_round_odd x k ≤ int_round_odd y k

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|int_round_odd_exact"
  int_round_odd_exact : ∀ k x : Int, 0 ≤ k → pow2 k ∣ x → int_round_odd x k = x

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|BofZ_round_odd"
  BofZ_round_odd : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (x k : Int), 1 < p → |x| ≤ (pow2 e -
    pow2 (e - p)) → (0 ≤ k ∧ k ≤ e - p) → pow2 (p + k + 1) ≤ |x| → (BofZ p e hp he x) = BofZ p e
    hp he (int_round_odd x k)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|int_round_odd_shifts"
  int_round_odd_shifts : ∀ x k : Int, 0 ≤ k → int_round_odd x k = shiftl (if x % pow2 k = 0 then
    shiftr x k else Int.lor (shiftr x k) 1) k

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|int_round_odd_bits"
  int_round_odd_bits : ∀ x y k : Int, 0 ≤ k → (∀ i, (0 ≤ i ∧ i < k) → testbit y i = false) →
    testbit y k = (if x % pow2 k = 0 then testbit x k else true) → (∀ i, k < i → testbit y i =
    testbit x i) → int_round_odd x k = y

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|ZofB_correct"
  ZofB_correct : ∀ (p e : Int) (f : binary_float p e), ZofB p e f = if is_finite f then some
    (Ztrunc (B2R f)) else none

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Ztrunc_range_pos"
  Ztrunc_range_pos : ∀ x : ℝ, 0 < Ztrunc x → (Ztrunc x : ℝ) ≤ x ∧ x < ((Ztrunc x + 1 : Int) : ℝ)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Ztrunc_range_zero"
  Ztrunc_range_zero : ∀ x : ℝ, Ztrunc x = 0 → -1 < x ∧ x < 1

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|ZofB_range_pos"
  ZofB_range_pos : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (f : binary_float p e) (n : Int), ZofB
    p e f = some n → 0 < n → (n : ℝ) ≤ B2R f ∧ B2R f < ((n + 1 : Int) : ℝ)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|ZofB_range_neg"
  ZofB_range_neg : ∀ (p e : Int) (f : binary_float p e) (n : Int), ZofB p e f = some n → n < 0 →
    ((n - 1 : Int) : ℝ) < B2R f ∧ B2R f ≤ (n : ℝ)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|ZofB_range_zero"
  ZofB_range_zero : ∀ (p e : Int) (f : binary_float p e), ZofB p e f = some 0 → -1 < B2R f ∧ B2R f
    < 1

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|ZofB_range_nonneg"
  ZofB_range_nonneg : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (f : binary_float p e) (n : Int),
    ZofB p e f = some n → 0 ≤ n → -1 < B2R f ∧ B2R f < ((n + 1 : Int) : ℝ)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|ZofBofZ_exact"
  ZofBofZ_exact : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (n : Int), integer_representable p e n →
    ZofB p e (BofZ p e hp he n) = some n

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Zfloor_minus"
  Zfloor_minus : ∀ (x : ℝ) (n : Int), ⌊x - n⌋ = ⌊x⌋ - n

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|ZofB_minus"
  ZofB_minus : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (m : Mode) (f :
    binary_float p e) (a b : Int), ZofB p e f = some a → (0 ≤ a ∧ a < 2 * b) → b ≤ pow2 p → (b :
    ℝ) ≤ B2R f → ZofB p e (Bminus p e hp he nan m f (BofZ p e hp he b)) = some (a - b)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|ZofB_range_correct"
  ZofB_range_correct : ∀ (p e : Int) (f : binary_float p e) (l u : Int), let n := Ztrunc (B2R f);
    ZofB_range p e f l u = if is_finite f && decide (l ≤ n) && decide (n ≤ u) then some n else
    none

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|ZofB_range_inversion"
  ZofB_range_inversion : ∀ (p e : Int) (f : binary_float p e) (l u n : Int), ZofB_range p e f l u
    = some n → l ≤ n ∧ n ≤ u ∧ ZofB p e f = some n

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|ZofB_range_minus"
  ZofB_range_minus : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (m : Mode) (f :
    binary_float p e) (a b : Int), ZofB_range p e f 0 (2 * b - 1) = some a → b ≤ pow2 p → (b :
    ℝ) ≤ B2R f → ZofB_range p e (Bminus p e hp he nan m f (BofZ p e hp he b)) (-b) (b - 1) =
    some (a - b)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bplus_commut"
  Bplus_commut : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (m : Mode) (x y :
    binary_float p e), nan x y = nan y x → Bplus p e hp he nan m x y = Bplus p e hp he nan m y x

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bmult_commut"
  Bmult_commut : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (m : Mode) (x y :
    binary_float p e), nan x y = nan y x → Bmult p e hp he nan m x y = Bmult p e hp he nan m y x

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bmult2_Bplus"
  Bmult2_Bplus : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (a b : Nan₂ p e) (m : Mode) (f :
    binary_float p e), (∀ x y, is_nan x = true → is_finite y = true → a x x = b x y) → Bplus p e
    hp he a m f f = Bmult p e hp he b m f (BofZ p e hp he 2)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bexact_inverse_mantissa_value"
  Bexact_inverse_mantissa_value : ∀ (p : Int), 0 < p → (((Bexact_inverse_mantissa p).val : Nat) :
    Int) = pow2 (p - 1)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bexact_inverse_mantissa_digits2_pos"
  Bexact_inverse_mantissa_digits2_pos : ∀ (p e : Int) (hp : 0 < p) (he : p < e), ((digits2_pos
    (Bexact_inverse_mantissa p)).val : Int) = p

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|bounded_Bexact_inverse"
  bounded_Bexact_inverse : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (i : Int), (emin p e ≤ i ∧ i ≤
    e - p) ↔ bounded p e (Bexact_inverse_mantissa p) i = true

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bexact_inverse_obligation_1"
  Bexact_inverse_obligation_1 : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (f : binary_float p e) (s
    : Bool) (m : Positive) (i : Int) (h : bounded p e m i = true), binary_float.B754_finite s m
    i h = f → m = (Bexact_inverse_mantissa p) → let j := -i - (p - 1) * 2; emin p e ≤ j →
    bounded p e m j = true

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bexact_inverse_obligation_2"
  Bexact_inverse_obligation_2 : ∀ (p e : Int) (b : Bool),
    let w : binary_float p e := .B754_zero b
    ∀ (s : Bool) (m : Positive) (i : Int) (h : bounded p e m i = true),
      binary_float.B754_finite s m i h ≠ w

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bexact_inverse_obligation_3"
  Bexact_inverse_obligation_3 : ∀ (p e : Int) (b : Bool),
    let w : binary_float p e := .B754_infinity b
    ∀ (s : Bool) (m : Positive) (i : Int) (h : bounded p e m i = true),
      binary_float.B754_finite s m i h ≠ w

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bexact_inverse_obligation_4"
  Bexact_inverse_obligation_4 : ∀ (p e : Int) (b : Bool) (pl : Positive) (v : nan_pl p pl = true),
    let w : binary_float p e := .B754_nan b pl v; ∀ (s : Bool) (m : Positive) (i : Int) (h :
    bounded p e m i = true), binary_float.B754_finite s m i h ≠ w

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bexact_inverse_correct"
  Bexact_inverse_correct : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (f g : binary_float p e),
    Bexact_inverse p e hp he f = some g → is_finite_strict f = true ∧ is_finite_strict g = true
    ∧ B2R g = (B2R f)⁻¹ ∧ B2R f ≠ 0 ∧ Bsign g = Bsign f

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bdiv_mult_inverse"
  Bdiv_mult_inverse : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (a b : Nan₂ p e) (m : Mode) (x y z :
    binary_float p e), (∀ i j k, is_nan i = true → is_finite j = true → is_finite k = true → a i
    j = b i k) → Bexact_inverse p e hp he y = some z → Bdiv p e hp he a m x y = Bmult p e hp he
    b m x z

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|pos_pow_spec"
  pos_pow_spec : ∀ x y : Positive, ((pos_pow x y).val : Int) = zpowNat (x.val : Int) (y.val : Int)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bparse_obligation_1"
  Bparse_obligation_1 : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (b m k : Positive), is_nan
    (roundQuotient p e hp he .mode_NE false m 0 (pos_pow b k) 0) = false

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Zpower_log"
  Zpower_log : ∀ (b : Radix) (n : Int), 0 < n → pow2 (n * log2 b.val) ≤ zpowNat b.val n ∧ zpowNat
    b.val n ≤ pow2 (n * log2up b.val)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|bpow_log_pos"
  bpow_log_pos : ∀ (b : Radix) (n : Int), 0 < n → (2 : ℝ) ^ (n * log2 b.val) ≤ (b.val : ℝ) ^ n

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|bpow_log_neg"
  bpow_log_neg : ∀ (b : Radix) (n : Int), n < 0 → (b.val : ℝ) ^ n ≤ (2 : ℝ) ^ (n * log2 b.val)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|round_integer_overflow"
  round_integer_overflow : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (b : Radix) (i : Int) (m :
    Positive), 0 < i → e ≤ i * log2 b.val → (2 : ℝ) ^ e ≤ round (fexp p e) (round_mode .mode_NE)
    ((m.val : ℝ) * (b.val : ℝ) ^ i)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|round_NE_underflows"
  round_NE_underflows : ∀ (p e : Int) (hp : 0 < p) (x : ℝ), (0 ≤ x ∧ x ≤ (2 : ℝ) ^ (emin p e - 1))
    → round (fexp p e) (round_mode .mode_NE) x = 0

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|round_integer_underflow"
  round_integer_underflow : ∀ (p e : Int) (hp : 0 < p) (b : Radix) (i : Int) (m : Positive), i < 0
    → i * log2 b.val + log2up m.val < emin p e → round (fexp p e) (round_mode .mode_NE) ((m.val
    : ℝ) * (b.val : ℝ) ^ i) = 0

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bparse_correct"
  Bparse_correct : ∀ (p e : Int) (hp : 0 < p) (he : p < e) (b m : Positive) (i : Int)
    (hb : 2 ≤ (b.val : Int)),
    let base : Radix := ⟨(b.val : Int), hb⟩
    let r := round (fexp p e) (round_mode .mode_NE) ((m.val : ℝ) * (base.val : ℝ) ^ i)
    if |r| < (2 : ℝ) ^ e then
      B2R (Bparse p e hp he b m i) = r ∧ is_finite (Bparse p e hp he b m i) = true ∧
      Bsign (Bparse p e hp he b m i) = false
    else B2FF (Bparse p e hp he b m i) = .F754_infinity false

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bconv_correct"
  Bconv_correct : ∀ (p₁ e₁ p₂ e₂ : Int) (h₂ : 0 < p₂) (l₂ : p₂ < e₂) (nan : ConvNaN p₁ e₁ p₂ e₂)
    (m : Mode) (f : binary_float p₁ e₁), is_finite f = true → if |round (fexp p₂ e₂) (round_mode
    m) (B2R f)| < (2 : ℝ) ^ e₂ then B2R (Bconv p₁ e₁ p₂ e₂ h₂ l₂ nan m f) = round (fexp p₂ e₂)
    (round_mode m) (B2R f) ∧ is_finite (Bconv p₁ e₁ p₂ e₂ h₂ l₂ nan m f) = true ∧ Bsign (Bconv
    p₁ e₁ p₂ e₂ h₂ l₂ nan m f) = Bsign f else B2FF (Bconv p₁ e₁ p₂ e₂ h₂ l₂ nan m f) =
    binary_overflow p₂ e₂ m (Bsign f)

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bconv_widen_exact"
  Bconv_widen_exact : ∀ (p₁ e₁ p₂ e₂ : Int) (h₁ : 0 < p₁) (h₂ : 0 < p₂) (l₂ : p₂ < e₂), p₁ ≤ p₂ →
    e₁ ≤ e₂ → ∀ (nan : ConvNaN p₁ e₁ p₂ e₂) (m : Mode) (f : binary_float p₁ e₁), is_finite f =
    true → B2R (Bconv p₁ e₁ p₂ e₂ h₂ l₂ nan m f) = B2R f ∧ is_finite (Bconv p₁ e₁ p₂ e₂ h₂ l₂
    nan m f) = true ∧ Bsign (Bconv p₁ e₁ p₂ e₂ h₂ l₂ nan m f) = Bsign f

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bconv_BofZ"
  Bconv_BofZ : ∀ (p₁ e₁ p₂ e₂ : Int) (h₁ : 0 < p₁) (h₂ : 0 < p₂) (l₁ : p₁ < e₁) (l₂ : p₂ < e₂)
    (nan : ConvNaN p₁ e₁ p₂ e₂) (n : Int), integer_representable p₁ e₁ n → Bconv p₁ e₁ p₂ e₂ h₂
    l₂ nan .mode_NE (BofZ p₁ e₁ h₁ l₁ n) = BofZ p₂ e₂ h₂ l₂ n

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|ZofB_Bconv"
  ZofB_Bconv : ∀ (p₁ e₁ p₂ e₂ : Int) (h₁ : 0 < p₁) (h₂ : 0 < p₂) (l₂ : p₂ < e₂), p₁ ≤ p₂ → e₁ ≤ e₂
    → ∀ (nan : ConvNaN p₁ e₁ p₂ e₂) (m : Mode) (f : binary_float p₁ e₁) (n : Int), ZofB p₁ e₁ f
    = some n → ZofB p₂ e₂ (Bconv p₁ e₁ p₂ e₂ h₂ l₂ nan m f) = some n

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|ZofB_range_Bconv"
  ZofB_range_Bconv : ∀ (p₁ e₁ p₂ e₂ : Int) (h₁ : 0 < p₁) (h₂ : 0 < p₂) (l₂ : p₂ < e₂) (a b c d :
    Int), p₁ ≤ p₂ → e₁ ≤ e₂ → c ≤ a → b ≤ d → ∀ (nan : ConvNaN p₁ e₁ p₂ e₂) (m : Mode) (f :
    binary_float p₁ e₁) (n : Int), ZofB_range p₁ e₁ f a b = some n → ZofB_range p₂ e₂ (Bconv p₁
    e₁ p₂ e₂ h₂ l₂ nan m f) c d = some n

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bcompare_Bconv_widen"
  Bcompare_Bconv_widen : ∀ (p₁ e₁ p₂ e₂ : Int) (h₁ : 0 < p₁) (h₂ : 0 < p₂) (l₂ : p₂ < e₂), p₁ ≤ p₂
    → e₁ ≤ e₂ → ∀ (nan : ConvNaN p₁ e₁ p₂ e₂) (m : Mode) (x y : binary_float p₁ e₁), Bcompare
    (Bconv p₁ e₁ p₂ e₂ h₂ l₂ nan m x) (Bconv p₁ e₁ p₂ e₂ h₂ l₂ nan m y) = Bcompare x y

#source_check "src/rocq/Numeric/IEEE754_extra.v|Vellvm.Numeric.IEEE754_extra|Bconv_narrow_widen"
  Bconv_narrow_widen : ∀ (p₁ e₁ p₂ e₂ : Int) (h₁ : 0 < p₁) (h₂ : 0 < p₂) (l₁ : p₁ < e₁) (l₂ : p₂ <
    e₂), p₁ ≤ p₂ → e₁ ≤ e₂ → ∀ (a : ConvNaN p₂ e₂ p₁ e₁) (b : ConvNaN p₁ e₁ p₂ e₂) (m : Mode) (f
    : binary_float p₁ e₁), is_nan f = false → Bconv p₂ e₂ p₁ e₁ h₁ l₁ a m (Bconv p₁ e₁ p₂ e₂ h₂
    l₂ b m f) = f
