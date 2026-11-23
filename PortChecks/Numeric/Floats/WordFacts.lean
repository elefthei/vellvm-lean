/-
The Compcert verified compiler.
Xavier Leroy and Jacques-Henri Jourdan, INRIA Paris-Rocquencourt.
Copyright Institut National de Recherche en Informatique et en Automatique. All rights
reserved. This file is distributed under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation, either version 2.1 of the License,
or (at your option) any later version. This file is also distributed under the terms
of the INRIA Non-Commercial License Agreement.
-/
import PortChecks.SourceType
import Vellvm.Numeric.Floats.WordFacts

namespace Vellvm.Numeric.Floats.Float
open Flocq IEEE754_extra Rocqlib
open Integers (bit_int w32 w64 unsigned hiword loword ofwords)

noncomputable section

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|split_bits_or"
  split_bits_or : ∀ x : bit_int w32,
    split_bits 52 11 (unsigned (ofwords ox4330_0000 x)) = ((false, unsigned x), 1075)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|from_words_value"
  from_words_value : ∀ x : bit_int w32,
    B2R (from_words ox4330_0000 x) = (2 : ℝ) ^ (52 : Int) + (unsigned x : ℝ) ∧
    is_finite (from_words ox4330_0000 x) = true ∧ Bsign (from_words ox4330_0000 x) = false

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|from_words_eq"
  from_words_eq : ∀ x : bit_int w32, from_words ox4330_0000 x =
    BofZ 53 1024 (by decide) (by decide) (2^52 + unsigned x)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|of_intu_from_words"
  of_intu_from_words : ∀ x : bit_int w32,
    of_intu x = sub (from_words ox4330_0000 x) (from_words ox4330_0000 (@Integers.zero w32))

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|ox8000_0000_signed_unsigned"
  ox8000_0000_signed_unsigned : ∀ x : bit_int w32,
    unsigned (Integers.add x ox8000_0000) = Integers.signed x + @Integers.half_modulus w32

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|of_int_from_words"
  of_int_from_words : ∀ x : bit_int w32,
    of_int x = sub (from_words ox4330_0000 (Integers.add x ox8000_0000))
      (from_words ox4330_0000 ox8000_0000)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|split_bits_or'"
  split_bits_or' : ∀ x : bit_int w32,
    split_bits 52 11 (unsigned (ofwords ox4530_0000 x)) = ((false, unsigned x), 1107)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|from_words_value'"
  from_words_value' : ∀ x : bit_int w32,
    B2R (from_words ox4530_0000 x) = (2 : ℝ) ^ (84 : Int) + ((unsigned x * two_p 32 : Int) : ℝ) ∧
    is_finite (from_words ox4530_0000 x) = true ∧ Bsign (from_words ox4530_0000 x) = false

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|from_words_eq'"
  from_words_eq' : ∀ x : bit_int w32, from_words ox4530_0000 x =
    BofZ 53 1024 (by decide) (by decide) (2^84 + unsigned x * 2^32)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|of_longu_from_words"
  of_longu_from_words : ∀ l : bit_int w64, of_longu l =
    add (sub (from_words ox4530_0000 (hiword l))
             (from_words ox4530_0000 (@Integers.repr w32 (two_p 20))))
        (from_words ox4330_0000 (loword l))

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|of_long_from_words"
  of_long_from_words : ∀ l : bit_int w64, of_long l =
    add (sub (from_words ox4530_0000 (Integers.add (hiword l) ox8000_0000))
             (from_words ox4530_0000 (@Integers.repr w32 (two_p 20 + two_p 31))))
        (from_words ox4330_0000 (loword l))

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|of_longu_decomp"
  of_longu_decomp : ∀ l : bit_int w64, of_longu l =
    add (mul (of_intu (hiword l)) (BofZ 53 1024 (by decide) (by decide) (2^32)))
        (of_intu (loword l))

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|of_long_decomp"
  of_long_decomp : ∀ l : bit_int w64, of_long l =
    add (mul (of_int (hiword l)) (BofZ 53 1024 (by decide) (by decide) (2^32)))
        (of_intu (loword l))

end
end Vellvm.Numeric.Floats.Float
