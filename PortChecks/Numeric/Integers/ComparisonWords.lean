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
import Vellvm.Numeric.Integers.ComparisonWords

namespace Vellvm.Numeric.Integers
open Rocqlib

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|negate_cmp"
  negate_cmp : ∀ {w : Positive} (c : comparison) (x y : bit_int w), cmp (negate_comparison c) x y = !(cmp c x y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|negate_cmpu"
  negate_cmpu : ∀ {w : Positive} (c : comparison) (x y : bit_int w), cmpu (negate_comparison c) x y = !(cmpu c x y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|swap_cmp"
  swap_cmp : ∀ {w : Positive} (c : comparison) (x y : bit_int w), cmp (swap_comparison c) x y = cmp c y x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|swap_cmpu"
  swap_cmpu : ∀ {w : Positive} (c : comparison) (x y : bit_int w), cmpu (swap_comparison c) x y = cmpu c y x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|translate_eq"
  translate_eq : ∀ {w : Positive} (x y d : bit_int w), eq (add x d) (add y d) = eq x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|translate_ltu"
  translate_ltu : ∀ {w : Positive} (x y d : bit_int w), 
    (0 ≤ unsigned x + unsigned d ∧ unsigned x + unsigned d ≤ @max_unsigned w) →
    (0 ≤ unsigned y + unsigned d ∧ unsigned y + unsigned d ≤ @max_unsigned w) →
    ltu (add x d) (add y d) = ltu x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|translate_cmpu"
  translate_cmpu : ∀ {w : Positive} (c : comparison) (x y d : bit_int w), 
    (0 ≤ unsigned x + unsigned d ∧ unsigned x + unsigned d ≤ @max_unsigned w) →
    (0 ≤ unsigned y + unsigned d ∧ unsigned y + unsigned d ≤ @max_unsigned w) →
    cmpu c (add x d) (add y d) = cmpu c x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|translate_lt"
  translate_lt : ∀ {w : Positive} (x y d : bit_int w), 
    (@min_signed w ≤ signed x + signed d ∧ signed x + signed d ≤ @max_signed w) →
    (@min_signed w ≤ signed y + signed d ∧ signed y + signed d ≤ @max_signed w) →
    lt (add x d) (add y d) = lt x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|translate_cmp"
  translate_cmp : ∀ {w : Positive} (c : comparison) (x y d : bit_int w), 
    (@min_signed w ≤ signed x + signed d ∧ signed x + signed d ≤ @max_signed w) →
    (@min_signed w ≤ signed y + signed d ∧ signed y + signed d ≤ @max_signed w) →
    cmp c (add x d) (add y d) = cmp c x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|notbool_isfalse_istrue"
  notbool_isfalse_istrue : ∀ {w : Positive} (x : bit_int w), is_false x → is_true (notbool x)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|notbool_istrue_isfalse"
  notbool_istrue_isfalse : ∀ {w : Positive} (x : bit_int w), is_true x → is_false (notbool x)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|ltu_range_test"
  ltu_range_test : ∀ {w : Positive} (x y : bit_int w), ltu x y = true → unsigned y ≤ @max_signed w →
    0 ≤ signed x ∧ signed x < unsigned y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|lt_sub_overflow"
  lt_sub_overflow : ∀ {w : Positive} (x y : bit_int w), 
    xor (sub_overflow x y zero) (negative (sub x y)) = (if lt x y then one else zero)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|signed_eq"
  signed_eq : ∀ {w : Positive} (x y : bit_int w), eq x y = proj_sumbool (zeq (signed x) (signed y))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|not_lt"
  not_lt : ∀ {w : Positive} (x y : bit_int w), Bool.not (lt y x) = (lt x y || eq x y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|lt_not"
  lt_not : ∀ {w : Positive} (x y : bit_int w), lt y x = (Bool.not (lt x y) && Bool.not (eq x y))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|not_ltu"
  not_ltu : ∀ {w : Positive} (x y : bit_int w), Bool.not (ltu y x) = (ltu x y || eq x y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|ltu_not"
  ltu_not : ∀ {w : Positive} (x y : bit_int w), ltu y x = (Bool.not (ltu x y) && Bool.not (eq x y))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|no_overlap_sound"
  no_overlap_sound : ∀ {w : Positive} (ofs1 : bit_int w) (sz1 : Int) (ofs2 : bit_int w) (sz2 : Int) (base : bit_int w), 
    sz1 > 0 → sz2 > 0 → no_overlap ofs1 sz1 ofs2 sz2 = true →
    unsigned (add base ofs1) + sz1 ≤ unsigned (add base ofs2) ∨
    unsigned (add base ofs2) + sz2 ≤ unsigned (add base ofs1)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zsize_pos"
  Zsize_pos : ∀ (x : Int), 0 ≤ Zsize x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zsize_pos'"
  Zsize_pos' : ∀ (x : Int), 0 < x → 0 < Zsize x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zsize_shiftin"
  Zsize_shiftin : ∀ (b : Bool) (x : Int), 0 < x → Zsize (Zshiftin b x) = Zsize x + 1

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_size_1"
  Ztestbit_size_1 : ∀ (x : Int), 0 < x → Zbits.testbit x (Zsize x - 1) = true

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_size_2"
  Ztestbit_size_2 : ∀ (x : Int), 0 ≤ x → ∀ i : Int, i ≥ Zsize x → Zbits.testbit x i = false

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zsize_interval_1"
  Zsize_interval_1 : ∀ (x : Int), 0 ≤ x → 0 ≤ x ∧ x < two_p (Zsize x)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zsize_interval_2"
  Zsize_interval_2 : ∀ (x n : Int), 0 ≤ n → (0 ≤ x ∧ x < two_p n) → n ≥ Zsize x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zsize_monotone"
  Zsize_monotone : ∀ (x y : Int), (0 ≤ x ∧ x ≤ y) → Zsize x ≤ Zsize y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|size_zero"
  size_zero : ∀ {w : Positive}, size (@zero w) = 0

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_size_1"
  bits_size_1 : ∀ {w : Positive} (x : bit_int w), x = zero ∨ testbit x (size x - 1) = true

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_size_2"
  bits_size_2 : ∀ {w : Positive} (x : bit_int w), ∀ i : Int, size x ≤ i → testbit x i = false

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|size_range"
  size_range : ∀ {w : Positive} (x : bit_int w), 0 ≤ size x ∧ size x ≤ @zwordsize w

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_size_3"
  bits_size_3 : ∀ {w : Positive} (x : bit_int w) (n : Int), 0 ≤ n →
    (∀ i : Int, (n ≤ i ∧ i < @zwordsize w) → testbit x i = false) → size x ≤ n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_size_4"
  bits_size_4 : ∀ {w : Positive} (x : bit_int w) (n : Int), 0 ≤ n →
    testbit x (n - 1) = true →
    (∀ i : Int, (n ≤ i ∧ i < @zwordsize w) → testbit x i = false) → size x = n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|size_interval_1"
  size_interval_1 : ∀ {w : Positive} (x : bit_int w), 0 ≤ unsigned x ∧ unsigned x < two_p (size x)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|size_interval_2"
  size_interval_2 : ∀ {w : Positive} (x : bit_int w), ∀ n : Int, 0 ≤ n → (0 ≤ unsigned x ∧ unsigned x < two_p n) → n ≥ size x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|size_and"
  size_and : ∀ {w : Positive} (a b : bit_int w), size (and a b) ≤ min (size a) (size b)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_interval"
  and_interval : ∀ {w : Positive} (a b : bit_int w), 
    0 ≤ unsigned (and a b) ∧ unsigned (and a b) < two_p (min (size a) (size b))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|size_or"
  size_or : ∀ {w : Positive} (a b : bit_int w), size (or a b) = max (size a) (size b)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_interval"
  or_interval : ∀ {w : Positive} (a b : bit_int w), 
    0 ≤ unsigned (or a b) ∧ unsigned (or a b) < two_p (max (size a) (size b))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|size_xor"
  size_xor : ∀ {w : Positive} (a b : bit_int w), size (xor a b) ≤ max (size a) (size b)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|xor_interval"
  xor_interval : ∀ {w : Positive} (a b : bit_int w), 
    0 ≤ unsigned (xor a b) ∧ unsigned (xor a b) < two_p (max (size a) (size b))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_loword"
  bits_loword : ∀ (n : bit_int w64) (i : Int), (0 ≤ i ∧ i < 32) → testbit (loword n) i = testbit n i

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_hiword"
  bits_hiword : ∀ (n : bit_int w64) (i : Int), (0 ≤ i ∧ i < 32) → testbit (hiword n) i = testbit n (i + 32)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_ofwords"
  bits_ofwords : ∀ (hi lo : bit_int w32) (i : Int), (0 ≤ i ∧ i < 64) →
    testbit (ofwords hi lo) i = chooseSide (zlt i 32) (testbit lo i) (testbit hi (i - 32))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|lo_ofwords"
  lo_ofwords : ∀ (hi lo : bit_int w32), loword (ofwords hi lo) = lo

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|hi_ofwords"
  hi_ofwords : ∀ (hi lo : bit_int w32), hiword (ofwords hi lo) = hi

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|ofwords_recompose"
  ofwords_recompose : ∀ (n : bit_int w64), ofwords (hiword n) (loword n) = n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|ofwords_add"
  ofwords_add : ∀ (lo hi : bit_int w32), ofwords hi lo = repr (unsigned hi * two_p 32 + unsigned lo)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|ofwords_add'"
  ofwords_add' : ∀ (lo hi : bit_int w32), unsigned (ofwords hi lo) = unsigned hi * two_p 32 + unsigned lo

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_mul_2p32"
  eqm_mul_2p32 : ∀ (x y : Int), @eqm w32 x y → @eqm w64 (x * two_p 32) (y * two_p 32)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|ofwords_add''"
  ofwords_add'' : ∀ (lo hi : bit_int w32), signed (ofwords hi lo) = signed hi * two_p 32 + unsigned lo

end Vellvm.Numeric.Integers
