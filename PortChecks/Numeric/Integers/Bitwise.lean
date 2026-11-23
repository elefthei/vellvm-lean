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
import Vellvm.Numeric.Integers.Bitwise

namespace Vellvm.Numeric.Integers
open Rocqlib

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_0"
  Ztestbit_0 : ∀ n, Zbits.testbit 0 n = false

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_1"
  Ztestbit_1 : ∀ n, Zbits.testbit 1 n = proj_sumbool (zeq n 0)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_m1"
  Ztestbit_m1 : ∀ n, 0 ≤ n → Zbits.testbit (-1) n = true

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zshiftin_spec"
  Zshiftin_spec : ∀ b x, Zshiftin b x = 2 * x + (if b then 1 else 0)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zshiftin_inj"
  Zshiftin_inj : ∀ b₁ x₁ b₂ x₂, Zshiftin b₁ x₁ = Zshiftin b₂ x₂ → b₁ = b₂ ∧ x₁ = x₂

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zdecomp"
  Zdecomp : ∀ x, x = Zshiftin (Int.bodd x) (Int.div2 x)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_shiftin"
  Ztestbit_shiftin : ∀ b x n, 0 ≤ n → Zbits.testbit (Zshiftin b x) n = chooseSide (zeq n 0) b (Zbits.testbit x
    (n - 1))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_shiftin_base"
  Ztestbit_shiftin_base : ∀ b x, Zbits.testbit (Zshiftin b x) 0 = b

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_shiftin_succ"
  Ztestbit_shiftin_succ : ∀ b x n, 0 ≤ n → Zbits.testbit (Zshiftin b x) (n + 1) = Zbits.testbit x n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_eq"
  Ztestbit_eq : ∀ n x, 0 ≤ n → Zbits.testbit x n = chooseSide (zeq n 0) (Int.bodd x) (Zbits.testbit (Int.div2 x)
    (n - 1))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_base"
  Ztestbit_base : ∀ x, Zbits.testbit x 0 = Int.bodd x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_succ"
  Ztestbit_succ : ∀ n x, 0 ≤ n → Zbits.testbit x (n + 1) = Zbits.testbit (Int.div2 x) n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_same_bits"
  eqmod_same_bits : ∀ (n : Nat) (x y : Int), (∀ i : Int, 0 ≤ i ∧ i < (n : Int) → Zbits.testbit x i =
    Zbits.testbit y i) → eqmod (two_power_nat n) x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_same_bits"
  eqm_same_bits : ∀ {w : Positive}, ∀ x y, (∀ i, 0 ≤ i ∧ i < (@zwordsize w) →
    Zbits.testbit x i = Zbits.testbit y i) → @eqm w x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|same_bits_eqmod"
  same_bits_eqmod : ∀ (n : Nat) (x y i : Int), eqmod (two_power_nat n) x y → 0 ≤ i ∧ i < (n : Int) →
    Zbits.testbit x i = Zbits.testbit y i

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|same_bits_eqm"
  same_bits_eqm : ∀ {w : Positive}, ∀ x y i, @eqm w x y → 0 ≤ i ∧ i < (@zwordsize w) →
    Zbits.testbit x i = Zbits.testbit y i

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|two_power_nat_infinity"
  two_power_nat_infinity : ∀ x : Int, 0 ≤ x → ∃ n, x < two_power_nat n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|equal_same_bits"
  equal_same_bits : ∀ x y, (∀ i, 0 ≤ i → Zbits.testbit x i = Zbits.testbit y i) → x = y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Z_one_complement"
  Z_one_complement : ∀ i, 0 ≤ i → ∀ x, Zbits.testbit (-x - 1) i = !(Zbits.testbit x i)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_above"
  Ztestbit_above : ∀ (n : Nat) (x i : Int), 0 ≤ x ∧ x < two_power_nat n → (n : Int) ≤ i → Zbits.testbit x
    i = false

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_above_neg"
  Ztestbit_above_neg : ∀ (n : Nat) (x i : Int), -two_power_nat n ≤ x ∧ x < 0 → (n : Int) ≤ i →
    Zbits.testbit x i = true

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zsign_bit"
  Zsign_bit : ∀ n x, 0 ≤ x ∧ x < two_power_nat (n+1) → Zbits.testbit x (Int.ofNat n) = chooseSide (zlt x
    (two_power_nat n)) false true

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zshiftin_ind"
  Zshiftin_ind : ∀ P : Int → Prop, P 0 → (∀ b x, 0 ≤ x → P x → P (Zshiftin b x)) → ∀ x, 0 ≤ x → P x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Zshiftin_pos_ind"
  Zshiftin_pos_ind : ∀ P : Int → Prop, P 1 → (∀ b x, 0 < x → P x → P (Zshiftin b x)) → ∀ x, 0 < x →
    P x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Ztestbit_le"
  Ztestbit_le : ∀ x y, 0 ≤ y → (∀ i, 0 ≤ i → Zbits.testbit x i = true → Zbits.testbit y i = true) → x ≤ y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|testbit_repr"
  testbit_repr : ∀ {w : Positive}, ∀ x i, 0 ≤ i ∧ i < (@zwordsize w) →
    testbit (@repr w x) i = Zbits.testbit x i

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|same_bits_eq"
  same_bits_eq : ∀ {w : Positive}, ∀ x y : bit_int w, (∀ i, 0 ≤ i ∧ i < (@zwordsize w) →
    testbit x i = testbit y i) → x = y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_above"
  bits_above : ∀ {w : Positive}, ∀ (x : bit_int w) i, (@zwordsize w) ≤ i → testbit x i = false

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_zero"
  bits_zero : ∀ {w : Positive}, ∀ i, testbit (@zero w) i = false

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_one"
  bits_one : ∀ {w : Positive}, ∀ n, testbit (@one w) n = proj_sumbool (zeq n 0)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_mone"
  bits_mone : ∀ {w : Positive}, ∀ i, 0 ≤ i ∧ i < (@zwordsize w) → testbit (@mone w) i = true

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sign_bit_of_unsigned"
  sign_bit_of_unsigned : ∀ {w : Positive}, ∀ x : bit_int w, testbit x ((@zwordsize w) - 1) =
    chooseSide (zlt (unsigned x) (@half_modulus w)) false true

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_signed"
  bits_signed : ∀ {w : Positive}, ∀ (x : bit_int w) i, 0 ≤ i → Zbits.testbit (signed x) i =
    testbit x (chooseSide (zlt i (@zwordsize w)) i ((@zwordsize w) - 1))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_le"
  bits_le : ∀ {w : Positive}, ∀ x y : bit_int w,
    (∀ i, 0 ≤ i ∧ i < (@zwordsize w) → testbit x i = true → testbit y i = true) →
    unsigned x ≤ unsigned y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_and"
  bits_and : ∀ {w : Positive}, ∀ (x y : bit_int w) i, 0 ≤ i ∧ i < (@zwordsize w) →
    testbit (and x y) i = (testbit x i && testbit y i)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_or"
  bits_or : ∀ {w : Positive}, ∀ (x y : bit_int w) i, 0 ≤ i ∧ i < (@zwordsize w) →
    testbit (or x y) i = (testbit x i || testbit y i)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_xor"
  bits_xor : ∀ {w : Positive}, ∀ (x y : bit_int w) i, 0 ≤ i ∧ i < (@zwordsize w) →
    testbit (xor x y) i = Bool.xor (testbit x i) (testbit y i)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|bits_not"
  bits_not : ∀ {w : Positive}, ∀ (x : bit_int w) i, 0 ≤ i ∧ i < (@zwordsize w) →
    testbit (not x) i = !(testbit x i)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_commut"
  and_commut : ∀ {w : Positive}, ∀ x y : bit_int w, and x y = and y x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_assoc"
  and_assoc : ∀ {w : Positive}, ∀ x y z : bit_int w, and (and x y) z = and x (and y z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_zero"
  and_zero : ∀ {w : Positive}, ∀ x : bit_int w, and x zero = zero

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_zero_l"
  and_zero_l : ∀ {w : Positive}, ∀ x : bit_int w, and zero x = zero

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_mone"
  and_mone : ∀ {w : Positive}, ∀ x : bit_int w, and x mone = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_mone_l"
  and_mone_l : ∀ {w : Positive}, ∀ x : bit_int w, and mone x = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_idem"
  and_idem : ∀ {w : Positive}, ∀ x : bit_int w, and x x = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_commut"
  or_commut : ∀ {w : Positive}, ∀ x y : bit_int w, or x y = or y x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_assoc"
  or_assoc : ∀ {w : Positive}, ∀ x y z : bit_int w, or (or x y) z = or x (or y z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_zero"
  or_zero : ∀ {w : Positive}, ∀ x : bit_int w, or x zero = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_zero_l"
  or_zero_l : ∀ {w : Positive}, ∀ x : bit_int w, or zero x = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_mone"
  or_mone : ∀ {w : Positive}, ∀ x : bit_int w, or x mone = mone

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_idem"
  or_idem : ∀ {w : Positive}, ∀ x : bit_int w, or x x = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_or_distrib"
  and_or_distrib : ∀ {w : Positive}, ∀ x y z : bit_int w, and x (or y z) = or (and x y) (and x z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_or_distrib_l"
  and_or_distrib_l : ∀ {w : Positive}, ∀ x y z : bit_int w, and (or x y) z = or (and x z) (and y z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_and_distrib"
  or_and_distrib : ∀ {w : Positive}, ∀ x y z : bit_int w, or x (and y z) = and (or x y) (or x z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_and_distrib_l"
  or_and_distrib_l : ∀ {w : Positive}, ∀ x y z : bit_int w, or (and x y) z = and (or x z) (or y z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_or_absorb"
  and_or_absorb : ∀ {w : Positive}, ∀ x y : bit_int w, and x (or x y) = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_and_absorb"
  or_and_absorb : ∀ {w : Positive}, ∀ x y : bit_int w, or x (and x y) = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|xor_commut"
  xor_commut : ∀ {w : Positive}, ∀ x y : bit_int w, xor x y = xor y x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|xor_assoc"
  xor_assoc : ∀ {w : Positive}, ∀ x y z : bit_int w, xor (xor x y) z = xor x (xor y z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|xor_zero"
  xor_zero : ∀ {w : Positive}, ∀ x : bit_int w, xor x zero = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|xor_zero_l"
  xor_zero_l : ∀ {w : Positive}, ∀ x : bit_int w, xor zero x = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|xor_idem"
  xor_idem : ∀ {w : Positive}, ∀ x : bit_int w, xor x x = zero

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|xor_zero_one"
  xor_zero_one : ∀ {w : Positive}, xor (@zero w) one = one

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|xor_one_one"
  xor_one_one : ∀ {w : Positive}, xor (@one w) one = zero

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|xor_zero_equal"
  xor_zero_equal : ∀ {w : Positive}, ∀ x y : bit_int w, xor x y = zero → x = y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|xor_is_zero"
  xor_is_zero : ∀ {w : Positive}, ∀ x y : bit_int w, eq (xor x y) zero = eq x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_xor_distrib"
  and_xor_distrib : ∀ {w : Positive}, ∀ x y z : bit_int w, and x (xor y z) = xor (and x y) (and x z)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_le"
  and_le : ∀ {w : Positive}, ∀ x y : bit_int w, unsigned (and x y) ≤ unsigned x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_le"
  or_le : ∀ {w : Positive}, ∀ x y : bit_int w, unsigned x ≤ unsigned (or x y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|not_involutive"
  not_involutive : ∀ {w : Positive}, ∀ x : bit_int w, not (not x) = x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|not_zero"
  not_zero : ∀ {w : Positive}, not (@zero w) = mone

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|not_mone"
  not_mone : ∀ {w : Positive}, not (@mone w) = zero

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|not_or_and_not"
  not_or_and_not : ∀ {w : Positive}, ∀ x y : bit_int w, not (or x y) = and (not x) (not y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|not_and_or_not"
  not_and_or_not : ∀ {w : Positive}, ∀ x y : bit_int w, not (and x y) = or (not x) (not y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|and_not_self"
  and_not_self : ∀ {w : Positive}, ∀ x : bit_int w, and x (not x) = zero

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|or_not_self"
  or_not_self : ∀ {w : Positive}, ∀ x : bit_int w, or x (not x) = mone

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|xor_not_self"
  xor_not_self : ∀ {w : Positive}, ∀ x : bit_int w, xor x (not x) = mone

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|unsigned_not"
  unsigned_not : ∀ {w : Positive}, ∀ x : bit_int w, unsigned (not x) = (@max_unsigned w) - unsigned x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|not_neg"
  not_neg : ∀ {w : Positive}, ∀ x : bit_int w, not x = add (neg x) mone

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|neg_not"
  neg_not : ∀ {w : Positive}, ∀ x : bit_int w, neg x = add (not x) one

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sub_add_not"
  sub_add_not : ∀ {w : Positive}, ∀ x y : bit_int w, sub x y = add (add x (not y)) one

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sub_add_not_3"
  sub_add_not_3 : ∀ {w : Positive}, ∀ x y b : bit_int w, b = zero ∨ b = one → sub (sub x y) b = add (add x (not y)) (xor b one)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|sub_borrow_add_carry"
  sub_borrow_add_carry : ∀ {w : Positive}, ∀ x y b : bit_int w, b = zero ∨ b = one → sub_borrow x y b = xor (add_carry x (not y) (xor b one)) one

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Z_add_is_or"
  Z_add_is_or : ∀ i, 0 ≤ i → ∀ x y, (∀ j, 0 ≤ j ∧ j ≤ i → (Zbits.testbit x j && Zbits.testbit y j) = false) →
    Zbits.testbit (x+y) i = (Zbits.testbit x i || Zbits.testbit y i)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|add_is_or"
  add_is_or : ∀ {w : Positive}, ∀ x y : bit_int w, and x y = zero → add x y = or x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|xor_is_or"
  xor_is_or : ∀ {w : Positive}, ∀ x y : bit_int w, and x y = zero → xor x y = or x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|add_is_xor"
  add_is_xor : ∀ {w : Positive}, ∀ x y : bit_int w, and x y = zero → add x y = xor x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|add_and"
  add_and : ∀ {w : Positive}, ∀ x y z : bit_int w, and y z = zero → add (and x y) (and x z) = and x (or y z)

end Vellvm.Numeric.Integers
