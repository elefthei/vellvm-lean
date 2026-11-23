/-
The Compcert verified compiler. Xavier Leroy and Jacques-Henri Jourdan, INRIA Paris-Rocquencourt.
Copyright Institut National de Recherche en Informatique et en Automatique. All rights reserved.
Distributed under the GNU Lesser General Public License, version 2.1 or (at your option) any later
version, and under the INRIA Non-Commercial License Agreement.
-/
import PortChecks.SourceType
import Vellvm.Numeric.Floats.OddFacts

open Vellvm.Numeric Vellvm.Numeric.Flocq Vellvm.Numeric.IEEE754_extra Vellvm.Numeric.Floats

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|int_round_odd_plus"
  Float32.int_round_odd_plus : ∀ p n : Int, 0 ≤ p → int_round_odd n p =
    Int.land (Int.lor n (Int.land n (pow2 p - 1) + (pow2 p - 1))) (-pow2 p)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|of_long_round_odd"
  Float32.of_long_round_odd : ∀ (n : Int) (conv_nan : ConvNaN 53 1024 24 128),
    (2 ^ 36 ≤ |n| ∧ |n| < 2 ^ 64) → BofZ 24 128 (by decide) (by decide) n =
    Bconv 53 1024 24 128 (by decide) (by decide) conv_nan .mode_NE
      (BofZ 53 1024 (by decide) (by decide) (Int.land (Int.lor n (Int.land n 2047 + 2047)) (-2048)))

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|of_longu_double_2"
  Float32.of_longu_double_2 : ∀ n : Integers.bit_int Integers.w64,
    2 ^ 36 ≤ Integers.unsigned n → Float32.of_longu n = Float32.of_double (Float.of_longu
      (Integers.and (Integers.or n (Integers.add (Integers.and n (Integers.repr 2047))
        (Integers.repr 2047))) (Integers.repr (-2048))))

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|of_long_double_2"
  Float32.of_long_double_2 : ∀ n : Integers.bit_int Integers.w64,
    2 ^ 36 ≤ |Integers.signed n| → Float32.of_long n = Float32.of_double (Float.of_long
      (Integers.and (Integers.or n (Integers.add (Integers.and n (Integers.repr 2047))
        (Integers.repr 2047))) (Integers.repr (-2048))))
