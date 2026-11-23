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
import Vellvm.Numeric.Integers.Extensions

namespace Vellvm.Numeric.Integers
open Rocqlib
universe u

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ziter_base"
  Ziter_base : ∀ (A : Type u) (n : Int) (f : A → A) (x : A), n ≤ 0 → Zbits.Ziter n f x = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ziter_succ"
  Ziter_succ : ∀ (A : Type u) (n : Int) (f : A → A) (x : A), 0 ≤ n →
    Zbits.Ziter (n+1) f x = f (Zbits.Ziter n f x)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Znatlike_ind"
  Znatlike_ind : ∀ P : Int → Prop, (∀ n, n ≤ 0 → P n) → (∀ n, 0 ≤ n → P n → P (n+1)) → ∀ n, P n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zzero_ext_spec"
  Zzero_ext_spec : ∀ n x i, 0 ≤ i → Zbits.testbit (Zzero_ext n x) i =
    chooseSide (zlt i n) (Zbits.testbit x i) false

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_zero_ext"
  bits_zero_ext : ∀ {w : Positive} n (x : bit_int w) i, 0 ≤ i →
    testbit (zero_ext n x) i = chooseSide (zlt i n) (testbit x i) false

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zsign_ext_spec"
  Zsign_ext_spec : ∀ n x i, 0 ≤ i → 0 < n → Zbits.testbit (Zsign_ext n x) i =
    Zbits.testbit x (chooseSide (zlt i n) i (n-1))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_sign_ext"
  bits_sign_ext : ∀ {w : Positive} n (x : bit_int w) i, 0 ≤ i ∧ i < @zwordsize w → 0 < n →
    testbit (sign_ext n x) i = testbit x (chooseSide (zlt i n) i (n-1))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|zero_ext_above"
  zero_ext_above : ∀ {w : Positive} n (x : bit_int w), @zwordsize w ≤ n → zero_ext n x = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sign_ext_above"
  sign_ext_above : ∀ {w : Positive} n (x : bit_int w), @zwordsize w ≤ n → sign_ext n x = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|zero_ext_and"
  zero_ext_and : ∀ {w : Positive} n (x : bit_int w), 0 ≤ n → zero_ext n x = and x (repr (two_p n - 1))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|zero_ext_mod"
  zero_ext_mod : ∀ {w : Positive} n (x : bit_int w), 0 ≤ n ∧ n < @zwordsize w →
    unsigned (zero_ext n x) = (unsigned x).fmod (two_p n)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|zero_ext_widen"
  zero_ext_widen : ∀ {w : Positive} (x : bit_int w) n m, 0 ≤ n ∧ n ≤ m →
    zero_ext m (zero_ext n x) = zero_ext n x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sign_ext_widen"
  sign_ext_widen : ∀ {w : Positive} (x : bit_int w) n m, 0 < n ∧ n ≤ m →
    sign_ext m (sign_ext n x) = sign_ext n x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sign_zero_ext_widen"
  sign_zero_ext_widen : ∀ {w : Positive} (x : bit_int w) n m, 0 ≤ n ∧ n < m →
    sign_ext m (zero_ext n x) = zero_ext n x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|zero_ext_narrow"
  zero_ext_narrow : ∀ {w : Positive} (x : bit_int w) n m, 0 ≤ n ∧ n ≤ m →
    zero_ext n (zero_ext m x) = zero_ext n x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sign_ext_narrow"
  sign_ext_narrow : ∀ {w : Positive} (x : bit_int w) n m, 0 < n ∧ n ≤ m →
    sign_ext n (sign_ext m x) = sign_ext n x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|zero_sign_ext_narrow"
  zero_sign_ext_narrow : ∀ {w : Positive} (x : bit_int w) n m, 0 < n ∧ n ≤ m →
    zero_ext n (sign_ext m x) = zero_ext n x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|zero_ext_idem"
  zero_ext_idem : ∀ {w : Positive} n (x : bit_int w), 0 ≤ n → zero_ext n (zero_ext n x) = zero_ext n x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sign_ext_idem"
  sign_ext_idem : ∀ {w : Positive} n (x : bit_int w), 0 < n → sign_ext n (sign_ext n x) = sign_ext n x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sign_ext_zero_ext"
  sign_ext_zero_ext : ∀ {w : Positive} n (x : bit_int w), 0 < n → sign_ext n (zero_ext n x) = sign_ext n x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|zero_ext_sign_ext"
  zero_ext_sign_ext : ∀ {w : Positive} n (x : bit_int w), 0 < n → zero_ext n (sign_ext n x) = zero_ext n x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sign_ext_equal_if_zero_equal"
  sign_ext_equal_if_zero_equal : ∀ {w : Positive} n (x y : bit_int w), 0 < n →
    zero_ext n x = zero_ext n y → sign_ext n x = sign_ext n y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|zero_ext_shru_shl"
  zero_ext_shru_shl : ∀ {w : Positive} n (x : bit_int w), 0 < n ∧ n < @zwordsize w →
    let y := @repr w (@zwordsize w - n); zero_ext n x = shru (shl x y) y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sign_ext_shr_shl"
  sign_ext_shr_shl : ∀ {w : Positive} n (x : bit_int w), 0 < n ∧ n < @zwordsize w →
    let y := @repr w (@zwordsize w - n); sign_ext n x = shr (shl x y) y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|zero_ext_range"
  zero_ext_range : ∀ {w : Positive} n (x : bit_int w), 0 ≤ n ∧ n < @zwordsize w →
    0 ≤ unsigned (zero_ext n x) ∧ unsigned (zero_ext n x) < two_p n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_zero_ext"
  eqmod_zero_ext : ∀ {w : Positive} n (x : bit_int w), 0 ≤ n ∧ n < @zwordsize w →
    eqmod (two_p n) (unsigned (zero_ext n x)) (unsigned x)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sign_ext_range"
  sign_ext_range : ∀ {w : Positive} n (x : bit_int w), 0 < n ∧ n < @zwordsize w →
    -two_p (n-1) ≤ signed (sign_ext n x) ∧ signed (sign_ext n x) < two_p (n-1)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_sign_ext'"
  eqmod_sign_ext' : ∀ {w : Positive} n (x : bit_int w), 0 < n ∧ n < @zwordsize w →
    eqmod (two_p n) (unsigned (sign_ext n x)) (unsigned x)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_sign_ext"
  eqmod_sign_ext : ∀ {w : Positive} n (x : bit_int w), 0 < n ∧ n < @zwordsize w →
    eqmod (two_p n) (signed (sign_ext n x)) (unsigned x)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|one_bits_range"
  one_bits_range : ∀ {w : Positive} (x i : bit_int w), i ∈ one_bits x → ltu i iwordsize = true

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|one_bits_decomp"
  one_bits_decomp : ∀ {w : Positive} (x : bit_int w), x = int_of_one_bits (one_bits x)

end Vellvm.Numeric.Integers
