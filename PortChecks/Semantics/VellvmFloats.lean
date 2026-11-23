import PortChecks.SourceType
import Vellvm.Semantics.VellvmFloats

open Vellvm Vellvm.Numeric.Integers Vellvm.Semantics.VellvmFloats
open Vellvm.Numeric.Floats Vellvm.Syntax.LLVMAst

universe u

#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|VFloat"
  VFloat : Type u → Type u
#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|Build_VFloat"
  Build_VFloat : ∀ {FP : Type u}, (float_syntax → Option FP) → VFloat FP
#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|denote_fp_syntax"
  denote_fp_syntax : ∀ {FP : Type u} [VFloat FP], float_syntax → Option FP

#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|uint_is_zero"
  uint_is_zero : Decimal.uint → Bool
#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|xx"
  xx : Decimal.uint
#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|positive_decimal_decimal_signed_to_float32"
  positive_decimal_decimal_signed_to_float32 : Decimal.uint → Decimal.uint → Decimal.signed_int → float32
#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|positive_decimal_decimal_to_float32"
  positive_decimal_decimal_to_float32 : Decimal.uint → Decimal.uint → float32
#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|positive_decimal_decimal_signed_to_float"
  positive_decimal_decimal_signed_to_float : Decimal.uint → Decimal.uint → Decimal.signed_int → float
#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|positive_decimal_decimal_to_float"
  positive_decimal_decimal_to_float : Decimal.uint → Decimal.uint → float

#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|hexadecimal_uint_to_float32"
  hexadecimal_uint_to_float32 : Hexadecimal.uint → Option float32
#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|float32_of_float_syntax"
  float32_of_float_syntax : float_syntax → Option float32
#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|hexadecimal_uint_to_bit_int"
  hexadecimal_uint_to_bit_int : ∀ {b : Positive}, Hexadecimal.uint → Option (bit_int b)

#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|hexadecimal_uint_to_bit_int_obligation_1"
  hexadecimal_uint_to_bit_int_obligation_1 : ∀ (b : Positive) (h : Hexadecimal.uint),
    let z : Int := h.toNat
    (h.toNat : Int) < @modulus b → -1 < z ∧ z < @modulus b

#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|hexadecimal_uint_to_float"
  hexadecimal_uint_to_float : Hexadecimal.uint → Option float
#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|h"
  h : Hexadecimal.uint
#source_check "src/rocq/Semantics/VellvmFloats.v|Vellvm.Semantics.VellvmFloats|float_of_float_syntax"
  float_of_float_syntax : float_syntax → Option float
