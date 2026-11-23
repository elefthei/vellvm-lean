import PortChecks.SourceType
import Vellvm.Numeric.Floats.Basic

open Vellvm Vellvm.Numeric Vellvm.Numeric.Flocq Vellvm.Numeric.Floats Vellvm.Numeric.Integers

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats|integer_representable_n"
  Floats.integer_representable_n : ∀ n : Int, -(2^53) ≤ n ∧ n ≤ 2^53 → IEEE754_extra.integer_representable 53 1024 n

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats|cmp_of_comparison_swap"
  cmp_of_comparison_swap : ∀ c x, cmp_of_comparison (swap_comparison c) x = cmp_of_comparison c (x.map Ordering.swap)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats|cmp_of_comparison_ne_eq"
  cmp_of_comparison_ne_eq : ∀ x, cmp_of_comparison Cne x = !cmp_of_comparison Ceq x

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats|cmp_of_comparison_lt_eq_false"
  cmp_of_comparison_lt_eq_false : ∀ x, cmp_of_comparison Clt x = true → cmp_of_comparison Ceq x = true → False

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats|cmp_of_comparison_le_lt_eq"
  cmp_of_comparison_le_lt_eq : ∀ x, cmp_of_comparison Cle x = (cmp_of_comparison Clt x || cmp_of_comparison Ceq x)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats|cmp_of_comparison_gt_eq_false"
  cmp_of_comparison_gt_eq_false : ∀ x, cmp_of_comparison Cgt x = true → cmp_of_comparison Ceq x = true → False

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats|cmp_of_comparison_ge_gt_eq"
  cmp_of_comparison_ge_gt_eq : ∀ x, cmp_of_comparison Cge x = (cmp_of_comparison Cgt x || cmp_of_comparison Ceq x)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats|cmp_of_comparison_lt_gt_false"
  cmp_of_comparison_lt_gt_false : ∀ x, cmp_of_comparison Clt x = true → cmp_of_comparison Cgt x = true → False

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats|normalized_nan"
  normalized_nan : ∀ (prec : Int) (n : Nat) (p : Positive), (n : Int) = prec - 1 → 1 < prec →
    nan_pl prec (toPositive (P_mod_two_p p n)) = true

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats|quiet_nan_64_proof"
  quiet_nan_64_proof : ∀ p, nan_pl 53 (quiet_nan_64_payload p) = true

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats|quiet_nan_32_proof"
  quiet_nan_32_proof : ∀ p, nan_pl 24 (quiet_nan_32_payload p) = true

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats|narrow_nan_32_proof"
  narrow_nan_32_proof : ∀ p, nan_pl 24 (narrow_nan_32_payload p) = true

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|expand_nan_proof"
  Floats.Float.expand_nan_proof : ∀ p, nan_pl 24 p = true → nan_pl 53 (Floats.Float.expand_nan_payload p) = true

namespace PortChecks.Numeric.Floats
open Vellvm.Numeric.Floats

-- The literal cast retains the signaling bit; a floating-point instruction quiets it.
example : (float_to_float32 (b64_of_bits 0xfff0000020000000)).map bits_of_b32 =
    some 0xff800001 := by decide
example : float_to_float32 (b64_of_bits 0x7ff0000000000001) = none := by decide
example : bits_of_b32 (Float.to_single (b64_of_bits 0xfff0000020000000)) =
    0xffc00001 := by decide
example : bits_of_b32 (Vellvm.Numeric.Floats.Float32.sqrt (b32_of_bits 0x80000000)) =
    0x80000000 := by decide
example : bits_of_b32 (Vellvm.Numeric.Floats.Float32.sqrt (b32_of_bits 0x40000000)) =
    0x3fb504f3 := by decide +kernel

-- The product rounds to one if evaluated separately. Fusing leaves exactly -2⁻⁴⁶.
example : bits_of_b32 (Vellvm.Numeric.Floats.Float32.fma (b32_of_bits 0x3f800001)
    (b32_of_bits 0x3f7ffffe) (b32_of_bits 0xbf800000)) = 0xa8800000 := by decide +kernel

end PortChecks.Numeric.Floats
