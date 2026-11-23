/-
The Compcert verified compiler. Xavier Leroy and Jacques-Henri Jourdan, INRIA Paris-Rocquencourt.
Copyright Institut National de Recherche en Informatique et en Automatique. All rights reserved.
Distributed under the GNU Lesser General Public License, version 2.1 or (at your option) any later
version, and under the INRIA Non-Commercial License Agreement.
-/
import PortChecks.SourceType
import Vellvm.Numeric.Floats.ConversionFacts

open Vellvm.Numeric Vellvm.Numeric.Floats Vellvm.Numeric.Integers

namespace Vellvm.Numeric.Floats.Float

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|of_intu_of_int_1"
  of_intu_of_int_1 : ∀ x : bit_int w32, ltu x ox8000_0000 = true → of_intu x = of_int x

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|of_intu_of_int_2"
  of_intu_of_int_2 : ∀ x : bit_int w32, ltu x ox8000_0000 = false →
    of_intu x = add (of_int (Integers.sub x ox8000_0000)) (of_intu ox8000_0000)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|of_intu_of_int_3"
  of_intu_of_int_3 : ∀ x : bit_int w32, of_intu x =
    sub (of_int (Integers.and x ox7FFF_FFFF)) (of_int (Integers.and x ox8000_0000))

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|to_intu_to_int_1"
  to_intu_to_int_1 : ∀ (x : float) (n : bit_int w32), cmp Clt x (of_intu ox8000_0000) = true →
    to_intu x = some n → to_int x = some n

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|to_intu_to_int_2"
  to_intu_to_int_2 : ∀ (x : float) (n : bit_int w32), cmp Clt x (of_intu ox8000_0000) = false →
    to_intu x = some n → to_int (sub x (of_intu ox8000_0000)) = some (Integers.sub n ox8000_0000)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|of_longu_of_long_1"
  of_longu_of_long_1 : ∀ x : bit_int w64, ltu x (Integers.repr (@half_modulus w64)) = true →
    of_longu x = of_long x

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|of_longu_of_long_2"
  of_longu_of_long_2 : ∀ x : bit_int w64, ltu x (Integers.repr (@half_modulus w64)) = false →
    of_longu x = mul (of_long (Integers.or (shru x one) (Integers.and x one))) (of_int (Integers.repr 2))

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|ZofB_range_widen"
  ZofB_range_widen : ∀ (f : float) (n min₁ max₁ min₂ max₂ : Int),
    IEEE754_extra.ZofB_range 53 1024 f min₁ max₁ = some n → min₂ ≤ min₁ → max₁ ≤ max₂ →
    IEEE754_extra.ZofB_range 53 1024 f min₂ max₂ = some n

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|to_int_to_long"
  to_int_to_long : ∀ (f : float) (n : bit_int w32), to_int f = some n →
    to_long f = some (@Integers.repr w64 (signed n))

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|to_intu_to_longu"
  to_intu_to_longu : ∀ (f : float) (n : bit_int w32), to_intu f = some n →
    to_longu f = some (@Integers.repr w64 (unsigned n))

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|to_intu_to_long"
  to_intu_to_long : ∀ (f : float) (n : bit_int w32), to_intu f = some n →
    to_long f = some (@Integers.repr w64 (unsigned n))

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|of_int_of_long"
  of_int_of_long : ∀ n : bit_int w32, of_int n = of_long (@Integers.repr w64 (signed n))

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|of_intu_of_longu"
  of_intu_of_longu : ∀ n : bit_int w32, of_intu n = of_longu (@Integers.repr w64 (unsigned n))

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|of_intu_of_long"
  of_intu_of_long : ∀ n : bit_int w32, of_intu n = of_long (@Integers.repr w64 (unsigned n))

end Vellvm.Numeric.Floats.Float

namespace Vellvm.Numeric.Floats.Float32

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|of_int_double"
  of_int_double : ∀ n : bit_int w32, of_int n = of_double (Float.of_int n)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|of_intu_double"
  of_intu_double : ∀ n : bit_int w32, of_intu n = of_double (Float.of_intu n)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|to_int_double"
  to_int_double : ∀ (f : float32) (n : bit_int w32), to_int f = some n → Float.to_int (to_double f) = some n

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|to_intu_double"
  to_intu_double : ∀ (f : float32) (n : bit_int w32), to_intu f = some n → Float.to_intu (to_double f) = some n

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|to_long_double"
  to_long_double : ∀ (f : float32) (n : bit_int w64), to_long f = some n → Float.to_long (to_double f) = some n

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|to_longu_double"
  to_longu_double : ∀ (f : float32) (n : bit_int w64), to_longu f = some n → Float.to_longu (to_double f) = some n

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|of_longu_double_1"
  of_longu_double_1 : ∀ n : bit_int w64, unsigned n ≤ (2 : Int)^53 → of_longu n = of_double (Float.of_longu n)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|of_long_double_1"
  of_long_double_1 : ∀ n : bit_int w64, |signed n| ≤ (2 : Int)^53 → of_long n = of_double (Float.of_long n)

end Vellvm.Numeric.Floats.Float32
