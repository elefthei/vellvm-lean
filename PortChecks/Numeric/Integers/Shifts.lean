/-
The Compcert verified compiler
Xavier Leroy, INRIA Paris-Rocquencourt

Copyright Institut National de Recherche en Informatique et en Automatique.
All rights reserved. This file is distributed under the terms of the GNU Lesser General
Public License as published by the Free Software Foundation, either version 2.1 of the License,
or (at your option) any later version. This file is also distributed under the terms of the
INRIA Non-Commercial License Agreement.
-/
import PortChecks.SourceType
import Vellvm.Numeric.Integers.Shifts

open Vellvm Vellvm.Numeric.Rocqlib
namespace Vellvm.Numeric.Integers

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_shl"
  bits_shl : ∀ {w : Positive}, ∀ (x y : bit_int w) (i : Int), 0 ≤ i ∧ i < @zwordsize w →
    testbit (shl x y) i = chooseSide (zlt i (unsigned y)) false (testbit x (i - unsigned y))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_shru"
  bits_shru : ∀ {w : Positive}, ∀ (x y : bit_int w) (i : Int), 0 ≤ i ∧ i < @zwordsize w →
    testbit (shru x y) i = chooseSide (zlt (i + unsigned y) (@zwordsize w)) (testbit x (i + unsigned y)) false

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_shr"
  bits_shr : ∀ {w : Positive}, ∀ (x y : bit_int w) (i : Int), 0 ≤ i ∧ i < @zwordsize w →
    testbit (shr x y) i = testbit x (chooseSide (zlt (i + unsigned y) (@zwordsize w)) (i + unsigned y) (@zwordsize w - 1))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shl_zero"
  shl_zero : ∀ {w : Positive}, ∀ x : bit_int w, shl x zero = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bitwise_binop_shl"
  bitwise_binop_shl : ∀ {w : Positive}, ∀ (f : bit_int w → bit_int w → bit_int w) (g : Bool → Bool → Bool) (x y n : bit_int w),
    (∀ x y i, 0 ≤ i ∧ i < @zwordsize w → testbit (f x y) i = g (testbit x i) (testbit y i)) →
    g false false = false → f (shl x n) (shl y n) = shl (f x y) n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_shl"
  and_shl : ∀ {w : Positive}, ∀ x y n : bit_int w, and (shl x n) (shl y n) = shl (and x y) n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_shl"
  or_shl : ∀ {w : Positive}, ∀ x y n : bit_int w, or (shl x n) (shl y n) = shl (or x y) n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|xor_shl"
  xor_shl : ∀ {w : Positive}, ∀ x y n : bit_int w, xor (shl x n) (shl y n) = shl (xor x y) n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|ltu_inv"
  ltu_inv : ∀ {w : Positive}, ∀ x y : bit_int w, ltu x y = true → 0 ≤ unsigned x ∧ unsigned x < unsigned y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|ltu_iwordsize_inv"
  ltu_iwordsize_inv : ∀ {w : Positive}, ∀ x : bit_int w, ltu x iwordsize = true → 0 ≤ unsigned x ∧ unsigned x < @zwordsize w

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shl_shl"
  shl_shl : ∀ {w : Positive}, ∀ x y z : bit_int w, ltu y iwordsize = true → ltu z iwordsize = true →
    ltu (add y z) iwordsize = true → shl (shl x y) z = shl x (add y z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sub_ltu"
  sub_ltu : ∀ {w : Positive}, ∀ x y : bit_int w, ltu x y = true → 0 ≤ unsigned y - unsigned x ∧ unsigned y - unsigned x ≤ unsigned y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shru_zero"
  shru_zero : ∀ {w : Positive}, ∀ x : bit_int w, shru x zero = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bitwise_binop_shru"
  bitwise_binop_shru : ∀ {w : Positive}, ∀ (f : bit_int w → bit_int w → bit_int w) (g : Bool → Bool → Bool) (x y n : bit_int w),
    (∀ x y i, 0 ≤ i ∧ i < @zwordsize w → testbit (f x y) i = g (testbit x i) (testbit y i)) →
    g false false = false → f (shru x n) (shru y n) = shru (f x y) n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_shru"
  and_shru : ∀ {w : Positive}, ∀ x y n : bit_int w, and (shru x n) (shru y n) = shru (and x y) n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_shru"
  or_shru : ∀ {w : Positive}, ∀ x y n : bit_int w, or (shru x n) (shru y n) = shru (or x y) n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|xor_shru"
  xor_shru : ∀ {w : Positive}, ∀ x y n : bit_int w, xor (shru x n) (shru y n) = shru (xor x y) n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shru_shru"
  shru_shru : ∀ {w : Positive}, ∀ x y z : bit_int w, ltu y iwordsize = true → ltu z iwordsize = true →
    ltu (add y z) iwordsize = true → shru (shru x y) z = shru x (add y z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shr_zero"
  shr_zero : ∀ {w : Positive}, ∀ x : bit_int w, shr x zero = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bitwise_binop_shr"
  bitwise_binop_shr : ∀ {w : Positive}, ∀ (f : bit_int w → bit_int w → bit_int w) (g : Bool → Bool → Bool) (x y n : bit_int w),
    (∀ x y i, 0 ≤ i ∧ i < @zwordsize w → testbit (f x y) i = g (testbit x i) (testbit y i)) →
    f (shr x n) (shr y n) = shr (f x y) n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_shr"
  and_shr : ∀ {w : Positive}, ∀ x y n : bit_int w, and (shr x n) (shr y n) = shr (and x y) n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_shr"
  or_shr : ∀ {w : Positive}, ∀ x y n : bit_int w, or (shr x n) (shr y n) = shr (or x y) n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|xor_shr"
  xor_shr : ∀ {w : Positive}, ∀ x y n : bit_int w, xor (shr x n) (shr y n) = shr (xor x y) n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shr_shr"
  shr_shr : ∀ {w : Positive}, ∀ x y z : bit_int w, ltu y iwordsize = true → ltu z iwordsize = true →
    ltu (add y z) iwordsize = true → shr (shr x y) z = shr x (add y z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_shr_shru"
  and_shr_shru : ∀ {w : Positive}, ∀ x y z : bit_int w, and (shr x z) (shru y z) = shru (and x y) z

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shr_and_shru_and"
  shr_and_shru_and : ∀ {w : Positive}, ∀ x y z : bit_int w, shru (shl z y) y = z → and (shr x y) z = and (shru x y) z

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shru_lt_zero"
  shru_lt_zero : ∀ {w : Positive}, ∀ x : bit_int w, shru x (repr (@zwordsize w - 1)) = if lt x zero then one else zero

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shr_lt_zero"
  shr_lt_zero : ∀ {w : Positive}, ∀ x : bit_int w, shr x (repr (@zwordsize w - 1)) = if lt x zero then mone else zero

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_rol"
  bits_rol : ∀ {w : Positive}, ∀ (x y : bit_int w) (i : Int), 0 ≤ i ∧ i < @zwordsize w →
    testbit (rol x y) i = testbit x ((i - unsigned y).fmod (@zwordsize w))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_ror"
  bits_ror : ∀ {w : Positive}, ∀ (x y : bit_int w) (i : Int), 0 ≤ i ∧ i < @zwordsize w →
    testbit (ror x y) i = testbit x ((i + unsigned y).fmod (@zwordsize w))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shl_rolm"
  shl_rolm : ∀ {w : Positive}, ∀ x n : bit_int w, ltu n iwordsize = true → shl x n = rolm x n (shl mone n)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|shru_rolm"
  shru_rolm : ∀ {w : Positive}, ∀ x n : bit_int w, ltu n iwordsize = true →
    shru x n = rolm x (sub iwordsize n) (shru mone n)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|rol_zero"
  rol_zero : ∀ {w : Positive}, ∀ x : bit_int w, rol x zero = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bitwise_binop_rol"
  bitwise_binop_rol : ∀ {w : Positive}, ∀ (f : bit_int w → bit_int w → bit_int w) (g : Bool → Bool → Bool) (x y n : bit_int w),
    (∀ x y i, 0 ≤ i ∧ i < @zwordsize w → testbit (f x y) i = g (testbit x i) (testbit y i)) →
    rol (f x y) n = f (rol x n) (rol y n)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|rol_and"
  rol_and : ∀ {w : Positive}, ∀ x y n : bit_int w, rol (and x y) n = and (rol x n) (rol y n)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|rol_or"
  rol_or : ∀ {w : Positive}, ∀ x y n : bit_int w, rol (or x y) n = or (rol x n) (rol y n)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|rol_xor"
  rol_xor : ∀ {w : Positive}, ∀ x y n : bit_int w, rol (xor x y) n = xor (rol x n) (rol y n)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|rol_rol"
  rol_rol : ∀ {w : Positive}, ∀ x n m : bit_int w, @zwordsize w ∣ @modulus w →
    rol (rol x n) m = rol x (modu (add n m) iwordsize)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|rolm_zero"
  rolm_zero : ∀ {w : Positive}, ∀ x m : bit_int w, rolm x zero m = and x m

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|rolm_rolm"
  rolm_rolm : ∀ {w : Positive}, ∀ x n₁ m₁ n₂ m₂ : bit_int w, @zwordsize w ∣ @modulus w →
    rolm (rolm x n₁ m₁) n₂ m₂ = rolm x (modu (add n₁ n₂) iwordsize) (and (rol m₁ n₂) m₂)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_rolm"
  or_rolm : ∀ {w : Positive}, ∀ x n m₁ m₂ : bit_int w, or (rolm x n m₁) (rolm x n m₂) = rolm x n (or m₁ m₂)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|ror_rol"
  ror_rol : ∀ {w : Positive}, ∀ x y : bit_int w, ltu y iwordsize = true → ror x y = rol x (sub iwordsize y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|ror_rol_neg"
  ror_rol_neg : ∀ {w : Positive}, ∀ x y : bit_int w, @zwordsize w ∣ @modulus w → ror x y = rol x (neg y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_ror"
  or_ror : ∀ {w : Positive}, ∀ x y z : bit_int w, ltu y iwordsize = true → ltu z iwordsize = true →
    add y z = iwordsize → ror x z = or (shl x y) (shru x z)

end Vellvm.Numeric.Integers
