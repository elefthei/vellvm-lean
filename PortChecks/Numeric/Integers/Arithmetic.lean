/-
The Compcert verified compiler
Xavier Leroy, INRIA Paris-Rocquencourt

Copyright Institut National de Recherche en Informatique et en Automatique.
All rights reserved. This file is distributed under the terms of the GNU Lesser
General Public License as published by the Free Software Foundation, either
version 2.1 of the License, or (at your option) any later version.
This file is also distributed under the terms of the INRIA Non-Commercial
License Agreement.
-/
import PortChecks.SourceType
import Vellvm.Numeric.Integers.Arithmetic

namespace Vellvm.Numeric.Integers

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|add_unsigned"
  add_unsigned : ∀ {w : Positive} (x y : bit_int w), add x y = repr (unsigned x + unsigned y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|add_signed"
  add_signed : ∀ {w : Positive} (x y : bit_int w), add x y = repr (signed x + signed y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|add_commut"
  add_commut : ∀ {w : Positive} (x y : bit_int w), add x y = add y x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|add_zero"
  add_zero : ∀ {w : Positive} (x : bit_int w), add x zero = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|add_zero_l"
  add_zero_l : ∀ {w : Positive} (x : bit_int w), add zero x = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|add_assoc"
  add_assoc : ∀ {w : Positive} (x y z : bit_int w), add (add x y) z = add x (add y z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|add_permut"
  add_permut : ∀ {w : Positive} (x y z : bit_int w), add x (add y z) = add y (add x z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|add_neg_zero"
  add_neg_zero : ∀ {w : Positive} (x : bit_int w), add x (neg x) = zero

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|unsigned_add_carry"
  unsigned_add_carry : ∀ {w : Positive} (x y : bit_int w),
    unsigned (add x y) = unsigned x + unsigned y - unsigned (add_carry x y zero) * @modulus w

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|unsigned_add_either"
  unsigned_add_either : ∀ {w : Positive} (x y : bit_int w),
    unsigned (add x y) = unsigned x + unsigned y ∨
    unsigned (add x y) = unsigned x + unsigned y - @modulus w

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|neg_repr"
  neg_repr : ∀ {w : Positive}, ∀ z : Int, neg (@repr w z) = repr (-z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|neg_zero"
  neg_zero : ∀ {w : Positive}, neg (@zero w) = zero

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|neg_involutive"
  neg_involutive : ∀ {w : Positive} (x : bit_int w), neg (neg x) = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|neg_add_distr"
  neg_add_distr : ∀ {w : Positive} (x y : bit_int w), neg (add x y) = add (neg x) (neg y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sub_zero_l"
  sub_zero_l : ∀ {w : Positive} (x : bit_int w), sub x zero = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sub_zero_r"
  sub_zero_r : ∀ {w : Positive} (x : bit_int w), sub zero x = neg x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sub_add_opp"
  sub_add_opp : ∀ {w : Positive} (x y : bit_int w), sub x y = add x (neg y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sub_idem"
  sub_idem : ∀ {w : Positive} (x : bit_int w), sub x x = zero

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sub_add_l"
  sub_add_l : ∀ {w : Positive} (x y z : bit_int w), sub (add x y) z = add (sub x z) y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sub_add_r"
  sub_add_r : ∀ {w : Positive} (x y z : bit_int w), sub x (add y z) = add (sub x z) (neg y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sub_shifted"
  sub_shifted : ∀ {w : Positive} (x y z : bit_int w), sub (add x z) (add y z) = sub x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sub_signed"
  sub_signed : ∀ {w : Positive} (x y : bit_int w), sub x y = repr (signed x - signed y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|unsigned_sub_borrow"
  unsigned_sub_borrow : ∀ {w : Positive} (x y : bit_int w),
    unsigned (sub x y) = unsigned x - unsigned y + unsigned (sub_borrow x y zero) * @modulus w

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|mul_commut"
  mul_commut : ∀ {w : Positive} (x y : bit_int w), mul x y = mul y x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|mul_zero"
  mul_zero : ∀ {w : Positive} (x : bit_int w), mul x zero = zero

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|mul_one"
  mul_one : ∀ {w : Positive} (x : bit_int w), mul x one = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|mul_mone"
  mul_mone : ∀ {w : Positive} (x : bit_int w), mul x mone = neg x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|mul_assoc"
  mul_assoc : ∀ {w : Positive} (x y z : bit_int w), mul (mul x y) z = mul x (mul y z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|mul_add_distr_l"
  mul_add_distr_l : ∀ {w : Positive} (x y z : bit_int w), mul (add x y) z = add (mul x z) (mul y z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|mul_add_distr_r"
  mul_add_distr_r : ∀ {w : Positive} (x y z : bit_int w), mul x (add y z) = add (mul x y) (mul x z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|neg_mul_distr_l"
  neg_mul_distr_l : ∀ {w : Positive} (x y : bit_int w), neg (mul x y) = mul (neg x) y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|neg_mul_distr_r"
  neg_mul_distr_r : ∀ {w : Positive} (x y : bit_int w), neg (mul x y) = mul x (neg y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|mul_signed"
  mul_signed : ∀ {w : Positive} (x y : bit_int w), mul x y = repr (signed x * signed y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|modu_divu_Euclid"
  modu_divu_Euclid : ∀ {w : Positive} (x y : bit_int w),
    y ≠ zero → x = add (mul (divu x y) y) (modu x y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|modu_divu"
  modu_divu : ∀ {w : Positive} (x y : bit_int w), y ≠ zero → modu x y = sub x (mul (divu x y) y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|mods_divs_Euclid"
  mods_divs_Euclid : ∀ {w : Positive} (x y : bit_int w), x = add (mul (divs x y) y) (mods x y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|mods_divs"
  mods_divs : ∀ {w : Positive} (x y : bit_int w), mods x y = sub x (mul (divs x y) y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|divu_one"
  divu_one : ∀ {w : Positive} (x : bit_int w), divu x one = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|divs_one"
  divs_one : ∀ {w : Positive} (x : bit_int w), 1 < @zwordsize w → divs x one = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|modu_one"
  modu_one : ∀ {w : Positive} (x : bit_int w), modu x one = zero

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|divs_mone"
  divs_mone : ∀ {w : Positive} (x : bit_int w), divs x mone = neg x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|mods_mone"
  mods_mone : ∀ {w : Positive} (x : bit_int w), mods x mone = zero

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|divmodu2_divu_modu"
  divmodu2_divu_modu : ∀ {w : Positive} (n d : bit_int w),
    d ≠ zero → divmodu2 zero n d = some (divu n d, modu n d)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|unsigned_signed"
  unsigned_signed : ∀ {w : Positive} (n : bit_int w),
    unsigned n = if lt n zero then signed n + @modulus w else signed n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|divmods2_divs_mods"
  divmods2_divs_mods : ∀ {w : Positive} (n d : bit_int w),
    d ≠ zero → n ≠ repr (@min_signed w) ∨ d ≠ mone →
    divmods2 (if lt n zero then mone else zero) n d = some (divs n d, mods n d)

end Vellvm.Numeric.Integers
