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
import Vellvm.Numeric.Integers.Basic

open Vellvm Vellvm.Numeric.Rocqlib
namespace Vellvm.Numeric.Integers

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|comparison_ind"
  comparison_ind : ∀ (P : comparison → Prop), P Ceq → P Cne → P Clt → P Cle → P Cgt → P Cge →
    ∀ c, P c

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|comparison_sind"
  comparison_sind : ∀ (P : comparison → Prop), P Ceq → P Cne → P Clt → P Cle → P Cgt → P Cge →
    ∀ c, P c

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|pos_to_nat_memo_eq"
  pos_to_nat_memo_eq : ∀ w, pos_to_nat_memo w = w.val

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|two_power_pos_memo_eq"
  two_power_pos_memo_eq : ∀ w, two_power_pos_memo w = two_power_pos w

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|half_two_power_pos_memo_eq"
  half_two_power_pos_memo_eq : ∀ w, half_two_power_pos_memo w = (two_power_pos w).fdiv 2

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|natwordsize_def"
  natwordsize_def : ∀ {w : Positive}, @natwordsize w = w.val

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|modulus_def"
  modulus_def : ∀ {w : Positive}, (@modulus w) = two_power_pos w

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|half_modulus_def"
  half_modulus_def : ∀ {w : Positive}, (@half_modulus w) = (@modulus w).fdiv 2

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|modulus_two_power_nat"
  modulus_two_power_nat : ∀ {w : Positive}, (@modulus w) = two_power_nat (@natwordsize w)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|wordsize_pos"
  wordsize_pos : ∀ {w : Positive}, (@zwordsize w) > 0

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|modulus_power"
  modulus_power : ∀ {w : Positive}, (@modulus w) = two_p (@zwordsize w)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|modulus_pos"
  modulus_pos : ∀ {w : Positive}, (@modulus w) > 0

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|P_mod_two_p_range"
  P_mod_two_p_range : ∀ n p, 0 ≤ P_mod_two_p p n ∧ P_mod_two_p p n < two_power_nat n

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|P_mod_two_p_eq"
  P_mod_two_p_eq : ∀ n p, P_mod_two_p p n = (Int.ofNat p.val).fmod (two_power_nat n)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Z_mod_modulus_range"
  Z_mod_modulus_range : ∀ {w : Positive}, ∀ x, 0 ≤ @Z_mod_modulus w x ∧ @Z_mod_modulus w x < (@modulus w)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Z_mod_modulus_range'"
  Z_mod_modulus_range' : ∀ {w : Positive}, ∀ x, -1 < @Z_mod_modulus w x ∧ @Z_mod_modulus w x < (@modulus w)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|Z_mod_modulus_eq"
  Z_mod_modulus_eq : ∀ {w : Positive}, ∀ x, @Z_mod_modulus w x = x.fmod (@modulus w)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|mkint_eq"
  mkint_eq : ∀ {w : Positive}, ∀ x y Px Py, x = y → @mkint w x Px = mkint y Py

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eq_dec"
  eq_dec : ∀ {w : Positive}, ∀ x y : bit_int w, PSum (x = y) (x ≠ y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|half_modulus_power"
  half_modulus_power : ∀ {w : Positive}, (@half_modulus w) = two_p ((@zwordsize w) - 1)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|half_modulus_modulus"
  half_modulus_modulus : ∀ {w : Positive}, (@modulus w) = 2 * (@half_modulus w)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|half_modulus_pos"
  half_modulus_pos : ∀ {w : Positive}, (@half_modulus w) > 0

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|min_signed_neg"
  min_signed_neg : ∀ {w : Positive}, (@min_signed w) < 0

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|max_signed_pos"
  max_signed_pos : ∀ {w : Positive}, (@max_signed w) ≥ 0

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|wordsize_max_unsigned"
  wordsize_max_unsigned : ∀ {w : Positive}, (@zwordsize w) ≤ (@max_unsigned w)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|two_wordsize_max_unsigned"
  two_wordsize_max_unsigned : ∀ {w : Positive}, 2 * (@zwordsize w) - 1 ≤ (@max_unsigned w)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|max_signed_unsigned"
  max_signed_unsigned : ∀ {w : Positive}, (@max_signed w) < (@max_unsigned w)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|unsigned_repr_eq"
  unsigned_repr_eq : ∀ {w : Positive}, ∀ x, unsigned (@repr w x) = x.fmod (@modulus w)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|signed_repr_eq"
  signed_repr_eq : ∀ {w : Positive}, ∀ x, signed (@repr w x) = chooseSide (zlt (x.fmod (@modulus w)) (@half_modulus w)) (x.fmod (@modulus w)) (x.fmod (@modulus w) - (@modulus w))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_refl"
  eqmod_refl : ∀ m x, eqmod m x x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_refl2"
  eqmod_refl2 : ∀ m x y, x = y → eqmod m x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_sym"
  eqmod_sym : ∀ m x y, eqmod m x y → eqmod m y x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_trans"
  eqmod_trans : ∀ m x y z, eqmod m x y → eqmod m y z → eqmod m x z

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_small_eq"
  eqmod_small_eq : ∀ m x y, eqmod m x y → 0 ≤ x ∧ x < m → 0 ≤ y ∧ y < m → x = y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_mod_eq"
  eqmod_mod_eq : ∀ m : Int, m > 0 → ∀ x y, eqmod m x y → x.fmod m = y.fmod m

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_mod"
  eqmod_mod : ∀ m x, eqmod m x (x.fmod m)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_add"
  eqmod_add : ∀ m a b c d, eqmod m a b → eqmod m c d → eqmod m (a+c) (b+d)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_neg"
  eqmod_neg : ∀ m x y, eqmod m x y → eqmod m (-x) (-y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_sub"
  eqmod_sub : ∀ m a b c d, eqmod m a b → eqmod m c d → eqmod m (a-c) (b-d)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_mult"
  eqmod_mult : ∀ m a b c d, eqmod m a c → eqmod m b d → eqmod m (a*b) (c*d)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqmod_divides"
  eqmod_divides : ∀ n m x y, eqmod n x y → m ∣ n → eqmod m x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_refl"
  eqm_refl : ∀ {w : Positive}, ∀ x, @eqm w x x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_refl2"
  eqm_refl2 : ∀ {w : Positive}, ∀ x y, x = y → @eqm w x y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_sym"
  eqm_sym : ∀ {w : Positive}, ∀ x y, @eqm w x y → @eqm w y x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_trans"
  eqm_trans : ∀ {w : Positive}, ∀ x y z, @eqm w x y → @eqm w y z → @eqm w x z

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_small_eq"
  eqm_small_eq : ∀ {w : Positive}, ∀ x y, @eqm w x y → 0 ≤ x ∧ x < (@modulus w) → 0 ≤ y ∧ y < (@modulus w) → x = y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_add"
  eqm_add : ∀ {w : Positive}, ∀ a b c d, @eqm w a b → @eqm w c d → @eqm w (a+c) (b+d)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_neg"
  eqm_neg : ∀ {w : Positive}, ∀ x y, @eqm w x y → @eqm w (-x) (-y)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_sub"
  eqm_sub : ∀ {w : Positive}, ∀ a b c d, @eqm w a b → @eqm w c d → @eqm w (a-c) (b-d)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_mult"
  eqm_mult : ∀ {w : Positive}, ∀ a b c d, @eqm w a c → @eqm w b d → @eqm w (a*b) (c*d)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_samerepr"
  eqm_samerepr : ∀ {w : Positive}, ∀ x y, @eqm w x y → @repr w x = repr y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_unsigned_repr"
  eqm_unsigned_repr : ∀ {w : Positive}, ∀ z, @eqm w z (unsigned (@repr w z))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_unsigned_repr_l"
  eqm_unsigned_repr_l : ∀ {w : Positive}, ∀ a b, @eqm w a b → @eqm w (unsigned (@repr w a)) b

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_unsigned_repr_r"
  eqm_unsigned_repr_r : ∀ {w : Positive}, ∀ a b, @eqm w a b → @eqm w a (unsigned (@repr w b))

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_signed_unsigned"
  eqm_signed_unsigned : ∀ {w : Positive}, ∀ x : bit_int w, @eqm w (signed x) (unsigned x)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|unsigned_range"
  unsigned_range : ∀ {w : Positive}, ∀ i : bit_int w, 0 ≤ unsigned i ∧ unsigned i < (@modulus w)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|unsigned_range_2"
  unsigned_range_2 : ∀ {w : Positive}, ∀ i : bit_int w, 0 ≤ unsigned i ∧ unsigned i ≤ (@max_unsigned w)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|signed_range"
  signed_range : ∀ {w : Positive}, ∀ i : bit_int w, (@min_signed w) ≤ signed i ∧ signed i ≤ (@max_signed w)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|repr_unsigned"
  repr_unsigned : ∀ {w : Positive}, ∀ i : bit_int w, repr (unsigned i) = i

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|repr_signed"
  repr_signed : ∀ {w : Positive}, ∀ i : bit_int w, repr (signed i) = i

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eqm_repr_eq"
  eqm_repr_eq : ∀ {w : Positive}, ∀ x (y : bit_int w), @eqm w x (unsigned y) → repr x = y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|unsigned_repr"
  unsigned_repr : ∀ {w : Positive}, ∀ z, 0 ≤ z ∧ z ≤ (@max_unsigned w) → unsigned (@repr w z) = z

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|signed_repr"
  signed_repr : ∀ {w : Positive}, ∀ z, (@min_signed w) ≤ z ∧ z ≤ (@max_signed w) → signed (@repr w z) = z

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|signed_eq_unsigned"
  signed_eq_unsigned : ∀ {w : Positive}, ∀ x : bit_int w, unsigned x ≤ (@max_signed w) → signed x = unsigned x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|signed_positive"
  signed_positive : ∀ {w : Positive}, ∀ x : bit_int w, signed x ≥ 0 ↔ unsigned x ≤ (@max_signed w)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|unsigned_zero"
  unsigned_zero : ∀ {w : Positive}, unsigned (@zero w) = 0

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|unsigned_one"
  unsigned_one : ∀ {w : Positive}, unsigned (@one w) = 1

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|unsigned_mone"
  unsigned_mone : ∀ {w : Positive}, unsigned (@mone w) = (@modulus w) - 1

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|signed_zero"
  signed_zero : ∀ {w : Positive}, signed (@zero w) = 0

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|signed_one"
  signed_one : ∀ {w : Positive}, (@zwordsize w) > 1 → signed (@one w) = 1

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|signed_mone"
  signed_mone : ∀ {w : Positive}, signed (@mone w) = -1

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|one_not_zero"
  one_not_zero : ∀ {w : Positive}, @one w ≠ zero

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|unsigned_repr_wordsize"
  unsigned_repr_wordsize : ∀ {w : Positive}, unsigned (@iwordsize w) = (@zwordsize w)

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eq_sym"
  eq_sym : ∀ {w : Positive}, ∀ x y : bit_int w, eq x y = eq y x

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eq_spec"
  eq_spec : ∀ {w : Positive}, ∀ x y : bit_int w, if eq x y then x = y else x ≠ y

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eq_true"
  eq_true : ∀ {w : Positive}, ∀ x : bit_int w, eq x x = true

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eq_false"
  eq_false : ∀ {w : Positive}, ∀ x y : bit_int w, x ≠ y → eq x y = false

#source_check "src/rocq/Numeric/Integers.v|Vellvm.Numeric.Integers|eq_signed"
  eq_signed : ∀ {w : Positive}, ∀ x y : bit_int w, eq x y = chooseSide (zeq (signed x) (signed y)) true false

private abbrev i3 := @repr ⟨3, by decide⟩

example : signed (@one ⟨1, by decide⟩) = -1 := by decide
example : divs (i3 (-4)) mone = i3 (-4) ∧ mods (i3 (-4)) mone = zero := by decide
example : divu (i3 5) zero = zero ∧ modu (i3 5) zero = i3 5 ∧
    divs (i3 (-3)) zero = zero ∧ mods (i3 (-3)) zero = i3 (-3) := by decide
example : add_carry (i3 2) one mone = one ∧ add_overflow (i3 2) one mone = zero ∧
    sub_borrow (i3 1) (i3 2) mone = one ∧ sub_overflow (i3 1) (i3 2) mone = zero := by decide
example : divmodu2 (i3 1) mone (i3 2) = some (mone, one) ∧
    divmods2 (i3 1) mone (i3 2) = none := by decide
example : zero_ext 0 (i3 3) = zero ∧ sign_ext 0 (i3 3) = mone ∧ sign_ext (-2) (i3 2) = zero := by
  decide +kernel

end Vellvm.Numeric.Integers
