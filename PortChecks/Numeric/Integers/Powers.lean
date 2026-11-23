/-
The Compcert verified compiler
Xavier Leroy, INRIA Paris-Rocquencourt

Copyright Institut National de Recherche en Informatique et en Automatique.
All rights reserved. This file is distributed under the terms of the GNU
Lesser General Public License as published by the Free Software Foundation,
either version 2.1 of the License, or (at your option) any later version.
This file is also distributed under the terms of the INRIA Non-Commercial License Agreement.
-/
import PortChecks.SourceType
import Vellvm.Numeric.Integers.Powers

open Vellvm Vellvm.Numeric Vellvm.Numeric.Rocqlib Vellvm.Numeric.Integers

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Z_one_bits_powerserie"
  Z_one_bits_powerserie : ∀ {w : Positive} (x : Int), 0 ≤ x ∧ x < @modulus w →
    x = powerserie (Z_one_bits (@natwordsize w) x 0)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Z_one_bits_range"
  Z_one_bits_range : ∀ {w : Positive} (x i : Int), i ∈ Z_one_bits (@natwordsize w) x 0 →
    0 ≤ i ∧ i < @zwordsize w

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|is_power2_rng"
  is_power2_rng : ∀ {w : Positive} (n logn : bit_int w), is_power2 n = some logn →
    0 ≤ unsigned logn ∧ unsigned logn < @zwordsize w

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|is_power2_range"
  is_power2_range : ∀ {w : Positive} (n logn : bit_int w), is_power2 n = some logn →
    ltu logn iwordsize = true

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|is_power2_correct"
  is_power2_correct : ∀ {w : Positive} (n logn : bit_int w), is_power2 n = some logn →
    unsigned n = two_p (unsigned logn)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|two_p_range"
  two_p_range : ∀ {w : Positive} (n : Int), 0 ≤ n ∧ n < @zwordsize w →
    0 ≤ two_p n ∧ two_p n ≤ @max_unsigned w

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Z_one_bits_zero"
  Z_one_bits_zero : ∀ (n : Nat) (i : Int), Z_one_bits n 0 i = []

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Z_one_bits_two_p"
  Z_one_bits_two_p : ∀ (n : Nat) (x i : Int), 0 ≤ x ∧ x < n → Z_one_bits n (two_p x) i = [i+x]

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|is_power2_two_p"
  is_power2_two_p : ∀ {w : Positive} (n : Int), 0 ≤ n ∧ n < @zwordsize w →
    @is_power2 w (Integers.repr (two_p n)) = some (Integers.repr n)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zshiftl_mul_two_p"
  Zshiftl_mul_two_p : ∀ x n : Int, 0 ≤ n → x <<< n = x * two_p n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shl_mul_two_p"
  shl_mul_two_p : ∀ {w : Positive} (x y : bit_int w),
    shl x y = mul x (Integers.repr (two_p (unsigned y)))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shl_mul"
  shl_mul : ∀ {w : Positive} (x y : bit_int w), shl x y = mul x (shl one y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|mul_pow2"
  mul_pow2 : ∀ {w : Positive} (x n logn : bit_int w), is_power2 n = some logn →
    mul x n = shl x logn

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shifted_or_is_add"
  shifted_or_is_add : ∀ {w : Positive} (x y : bit_int w) (n : Int), 0 ≤ n ∧ n < @zwordsize w →
    unsigned y < two_p n → Integers.or (shl x (Integers.repr n)) y =
      Integers.repr (unsigned x * two_p n + unsigned y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zshiftr_div_two_p"
  Zshiftr_div_two_p : ∀ x n : Int, 0 ≤ n → x >>> n = x.fdiv (two_p n)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shru_div_two_p"
  shru_div_two_p : ∀ {w : Positive} (x y : bit_int w),
    shru x y = Integers.repr ((unsigned x).fdiv (two_p (unsigned y)))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|divu_pow2"
  divu_pow2 : ∀ {w : Positive} (x n logn : bit_int w), is_power2 n = some logn →
    divu x n = shru x logn

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shr_div_two_p"
  shr_div_two_p : ∀ {w : Positive} (x y : bit_int w),
    shr x y = Integers.repr ((signed x).fdiv (two_p (unsigned y)))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|divs_pow2"
  divs_pow2 : ∀ {w : Positive} (x n logn : bit_int w), is_power2 n = some logn →
    divs x n = shrx x logn

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_mod_two_p"
  Ztestbit_mod_two_p : ∀ n x i, 0 ≤ n → 0 ≤ i → Zbits.testbit (Int.fmod x (two_p n)) i =
    chooseSide (zlt i n) (Zbits.testbit x i) false

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_two_p_m1"
  Ztestbit_two_p_m1 : ∀ n i, 0 ≤ n → 0 ≤ i → Zbits.testbit (two_p n - 1) i =
    chooseSide (zlt i n) true false

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|modu_and"
  modu_and : ∀ {w : Positive} (x n logn : bit_int w), is_power2 n = some logn →
    modu x n = Integers.and x (sub n one)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zquot_Zdiv"
  Zquot_Zdiv : ∀ x y : Int, 0 < y → x.tdiv y =
    chooseSide (zlt x 0) ((x+y-1).fdiv y) (x.fdiv y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shrx_zero"
  shrx_zero : ∀ {w : Positive} (x : bit_int w), 1 < @zwordsize w → shrx x zero = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shrx_shr"
  shrx_shr : ∀ {w : Positive} (x y : bit_int w), ltu y (Integers.repr (@zwordsize w-1)) = true →
    shrx x y = shr (if Integers.lt x zero then add x (sub (shl one y) one) else x) y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shrx_shr_2"
  shrx_shr_2 : ∀ {w : Positive} (x y : bit_int w), ltu y (Integers.repr (@zwordsize w-1)) = true →
    shrx x y = shr (add x (shru (shr x (Integers.repr (@zwordsize w-1))) (sub iwordsize y))) y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zdiv_shift"
  Zdiv_shift : ∀ x y : Int, 0 < y → (x+(y-1)).fdiv y =
    x.fdiv y + chooseSide (zeq (x.fmod y) 0) 0 1

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shrx_carry"
  shrx_carry : ∀ {w : Positive} (x y : bit_int w), ltu y (Integers.repr (@zwordsize w-1)) = true →
    shrx x y = add (shr x y) (shr_carry x y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shr_shru_positive"
  shr_shru_positive : ∀ {w : Positive} (x y : bit_int w), 0 ≤ signed x → shr x y = shru x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_positive"
  and_positive : ∀ {w : Positive} (x y : bit_int w), 0 ≤ signed y → 0 ≤ signed (Integers.and x y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shr_and_is_shru_and"
  shr_and_is_shru_and : ∀ {w : Positive} (x y z : bit_int w), Integers.lt y zero = false →
    shr (Integers.and x y) z = shru (Integers.and x y) z
