import PortChecks.SourceType
import Vellvm.Utils.ParserHelper

open Vellvm Vellvm.Utils.ParserHelper
open Vellvm.Numeric.Flocq
universe u

#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|Zlog2_log_inf"
  Zlog2_log_inf : ∀ p : Positive, (p.val.log2 : Int) = log_inf p

#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|digits2_pos_digits"
  digits2_pos_digits : ∀ m : Positive, ((digits2_pos m).val : Int) = (m.val.log2 : Int) + 1

#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|bounded_closed_form"
  bounded_closed_form : ∀ p e : Int, 0 < p → p < e → ∀ (m : Positive) (i : Int),
    bounded p e m i = true ↔
      ((m.val.log2 : Int) + 1 < p ∧ i = 3 - e - p) ∨
      ((m.val.log2 : Int) + 1 = p ∧ 3 - e - p ≤ i ∧ i ≤ e - p)

#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|float_eq_refl"
  float_eq_refl : ∀ x : bfloat, float_eq x x
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|float_eq_sym"
  float_eq_sym : ∀ {x y : bfloat}, float_eq x y → float_eq y x
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|Zpow_divide"
  Zpow_divide : ∀ b a c : Int, 0 < b → (0 ≤ a ∧ a ≤ c) → zpowNat b a ∣ zpowNat b c
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|float_eq_trans"
  float_eq_trans : ∀ {x y z : bfloat}, float_eq x y → float_eq y z → float_eq x z
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|float_eq_equivalence"
  float_eq_equivalence : Equivalence float_eq

#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|not_zero_Zpos"
  not_zero_Zpos : ∀ (m : Positive) (e : Int), not_zero (BFloat (m.val : Int) e)
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|not_zero_eq"
  not_zero_eq : ∀ f g : bfloat, not_zero f → float_eq f g → not_zero g

#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|inc_e_correct"
  inc_e_correct : ∀ (f : bfloat) (d : Positive) {g : bfloat}, inc_e f d = some g →
    g.Fexp = f.Fexp + (d.val : Int)
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|dec_e_correct"
  dec_e_correct : ∀ (f : bfloat) (d : Positive), (dec_e f d).Fexp = f.Fexp - (d.val : Int)
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|shift_e_correct"
  shift_e_correct : ∀ (f : bfloat) (d : Int) {g : bfloat}, shift_e f d = some g →
    g.Fexp = f.Fexp + d
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|set_e_correct"
  set_e_correct : ∀ (f : bfloat) (e : Int) {g : bfloat}, set_e f e = some g → g.Fexp = e

#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|inc_e_eq"
  inc_e_eq : ∀ (f : bfloat) (d : Positive) {g : bfloat}, inc_e f d = some g → float_eq f g
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|dec_e_eq"
  dec_e_eq : ∀ (f : bfloat) (d : Positive), float_eq f (dec_e f d)
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|shift_e_eq"
  shift_e_eq : ∀ (f : bfloat) (d : Int) {g : bfloat}, shift_e f d = some g → float_eq f g
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|set_e_eq"
  set_e_eq : ∀ (f : bfloat) (e : Int) {g : bfloat}, set_e f e = some g → float_eq f g

#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|Zdigits_mul_pow2"
  Zdigits_mul_pow2 : ∀ (m : Int) (d : Positive), m ≠ 0 →
    Zdigits (m * (2 : Int) ^ d.val) = Zdigits m + (d.val : Int)
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|Zabs_div_exact"
  Zabs_div_exact : ∀ a b : Int, b ≠ 0 → a % b = 0 → |a / b| = |a| / |b|
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|Zdigits_div_pow2"
  Zdigits_div_pow2 : ∀ (m : Int) (d : Positive), m ≠ 0 → m % (2 : Int) ^ d.val = 0 →
    Zdigits (m / (2 : Int) ^ d.val) = Zdigits m - (d.val : Int)

#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|inc_digits_m_correct"
  inc_digits_m_correct : ∀ (f : bfloat) (d : Positive), not_zero f →
    Zdigits (inc_digits_m f d).Fnum = Zdigits f.Fnum + (d.val : Int)
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|dec_digits_m_correct"
  dec_digits_m_correct : ∀ (f : bfloat) (d : Positive) {g : bfloat}, not_zero f →
    dec_digits_m f d = some g → Zdigits g.Fnum = Zdigits f.Fnum - (d.val : Int)
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|shift_digits_m_correct"
  shift_digits_m_correct : ∀ (f : bfloat) (d : Int) {g : bfloat}, f.Fnum ≠ 0 →
    shift_digits_m f d = some g → Zdigits g.Fnum = Zdigits f.Fnum + d
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|set_digits_m_correct"
  set_digits_m_correct : ∀ (f : bfloat) (d : Int) {g : bfloat}, not_zero f →
    set_digits_m f d = some g → Zdigits g.Fnum = d

#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|inc_digits_m_eq"
  inc_digits_m_eq : ∀ (f : bfloat) (d : Positive), float_eq f (inc_digits_m f d)
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|dec_digits_m_eq"
  dec_digits_m_eq : ∀ (f : bfloat) (d : Positive) {g : bfloat},
    dec_digits_m f d = some g → float_eq f g
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|shift_digits_m_eq"
  shift_digits_m_eq : ∀ (f : bfloat) (d : Int) {g : bfloat},
    shift_digits_m f d = some g → float_eq f g
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|set_digits_m_eq"
  set_digits_m_eq : ∀ (f : bfloat) (d : Int) {g : bfloat},
    set_digits_m f d = some g → float_eq f g

#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|exponent_unique_fnum"
  exponent_unique_fnum : ∀ f g : bfloat, float_eq f g → f.Fexp = g.Fexp → f.Fnum = g.Fnum
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|exponent_unique"
  exponent_unique : ∀ f g : bfloat, float_eq f g → f.Fexp = g.Fexp → f = g
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|Zdigits_m_unique_fexp"
  Zdigits_m_unique_fexp : ∀ f g : bfloat, not_zero f → float_eq f g →
    Zdigits f.Fnum = Zdigits g.Fnum → f.Fexp = g.Fexp
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|Zdigits_m_unique"
  Zdigits_m_unique : ∀ f g : bfloat, not_zero f → float_eq f g →
    Zdigits f.Fnum = Zdigits g.Fnum → f = g
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|Zdigits_Zpos_log_inf"
  Zdigits_Zpos_log_inf : ∀ p : Positive, Zdigits (p.val : Int) = (p.val.log2 : Int) + 1
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|Zdigits_Zneg_log_inf"
  Zdigits_Zneg_log_inf : ∀ p : Positive, Zdigits (-(p.val : Int)) = (p.val.log2 : Int) + 1

#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|valid_float_closed_form"
  valid_float_closed_form : ∀ (p e : Int) (f : bfloat), not_zero f → 0 < p → p < e →
    (valid_float p e f = true ↔
      (Zdigits f.Fnum < p ∧ f.Fexp = 3 - e - p) ∨
      (Zdigits f.Fnum = p ∧ 3 - e - p ≤ f.Fexp ∧ f.Fexp ≤ e - p))
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|not_None_iff_exists_Some"
  not_None_iff_exists_Some : ∀ {A : Type u} {x : Option A}, x ≠ none ↔ ∃ y, x = some y
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|float_eq_trans_l"
  float_eq_trans_l : ∀ f g k : bfloat, float_eq f g → float_eq f k → float_eq g k
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|float_eq_set_e"
  float_eq_set_e : ∀ f g : bfloat, float_eq f g → set_e f g.Fexp = some g
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|float_eq_set_digits_m"
  float_eq_set_digits_m : ∀ f g : bfloat, not_zero f → float_eq f g →
    set_digits_m f (Zdigits g.Fnum) = some g
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|set_e_definition"
  set_e_definition : ∀ (f : bfloat) (e : Int) {g : bfloat},
    set_e f e = some g ↔ float_eq f g ∧ g.Fexp = e
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|set_digits_m_definition"
  set_digits_m_definition : ∀ (f : bfloat) (d : Int) {g : bfloat}, not_zero f →
    (set_digits_m f d = some g ↔ float_eq f g ∧ Zdigits g.Fnum = d)
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|normalize_correct'"
  normalize_correct' : ∀ (p e : Int) (f : bfloat), not_zero f → 0 < p → p < e →
    match normalize_float p e f with
    | some nf => float_eq f nf ∧ valid_float p e nf = true
    | none => ∀ xf : bfloat, float_eq f xf → valid_float p e xf = false
#source_check "src/rocq/Utils/ParserHelper.v|Vellvm.Utils.ParserHelper|normalize_correct"
  normalize_correct : ∀ (p e : Int) (f : bfloat), not_zero f → 0 < p → p < e →
    ∀ {nf : bfloat}, normalize_float p e f = some nf ↔ float_eq f nf ∧ valid_float p e nf = true
