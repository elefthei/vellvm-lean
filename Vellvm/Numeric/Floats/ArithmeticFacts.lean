/-
The Compcert verified compiler
Xavier Leroy and Jacques-Henri Jourdan, INRIA Paris-Rocquencourt
Copyright Institut National de Recherche en Informatique et en Automatique. All rights reserved.
This file is distributed under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation, either version 2.1 of the License, or (at your option) any later
version. This file is also distributed under the terms of the INRIA Non-Commercial License Agreement.
-/
import Vellvm.Numeric.Floats.Basic

namespace Vellvm.Numeric.Floats
open Flocq IEEE754_extra

private theorem Bcompare_reverse {p e : Int} (x y : binary_float p e) :
    (Bcompare x y).map Ordering.swap = Bcompare y x := by
  cases x <;> cases y <;> simp only [Bcompare, Option.map_some, Option.map_none] <;> try rfl
  all_goals first
    | exact congrArg some (Std.OrientedCmp.eq_swap (cmp := compare) ..).symm
    | split <;> rfl

namespace Float

private theorem binop_nan_comm (x y : float) (h : is_nan x = false ∨ is_nan y = false) :
    binop_nan x y = binop_nan y x := by
  cases x <;> cases y <;> first | rfl | simp [is_nan] at h

theorem add_commut (x y : float) (h : is_nan x = false ∨ is_nan y = false) :
    add x y = add y x :=
  Bplus_commut 53 1024 (by decide) (by decide) binop_nan .mode_NE x y (binop_nan_comm x y h)

theorem mul_commut (x y : float) (h : is_nan x = false ∨ is_nan y = false) :
    mul x y = mul y x :=
  Bmult_commut 53 1024 (by decide) (by decide) binop_nan .mode_NE x y (binop_nan_comm x y h)

theorem mul2_add (f : float) : add f f = mul f (of_int (Integers.repr 2)) := by
  refine Bmult2_Bplus 53 1024 (by decide) (by decide) binop_nan binop_nan .mode_NE f ?_
  intro x y hx _
  cases x <;> first | rfl | simp [is_nan] at hx

theorem div_mul_inverse (x y z : float) (h : exact_inverse y = some z) : div x y = mul x z := by
  refine Bdiv_mult_inverse 53 1024 (by decide) (by decide) binop_nan binop_nan .mode_NE x y z ?_ h
  intro i j k hi _ _
  cases i <;> first | rfl | simp [is_nan] at hi

theorem cmp_swap (c : Integers.comparison) (x y : float) :
    cmp (Integers.swap_comparison c) x y = cmp c y x := by
  unfold cmp compare
  rw [cmp_of_comparison_swap, Bcompare_reverse]

theorem cmp_ne_eq (x y : float) : cmp .Cne x y = !cmp .Ceq x y :=
  cmp_of_comparison_ne_eq (compare x y)

theorem cmp_lt_eq_false (x y : float) : cmp .Clt x y = true → cmp .Ceq x y = true → False :=
  cmp_of_comparison_lt_eq_false (compare x y)

theorem cmp_le_lt_eq (x y : float) : cmp .Cle x y = (cmp .Clt x y || cmp .Ceq x y) :=
  cmp_of_comparison_le_lt_eq (compare x y)

theorem cmp_gt_eq_false (x y : float) : cmp .Cgt x y = true → cmp .Ceq x y = true → False :=
  cmp_of_comparison_gt_eq_false (compare x y)

theorem cmp_ge_gt_eq (x y : float) : cmp .Cge x y = (cmp .Cgt x y || cmp .Ceq x y) :=
  cmp_of_comparison_ge_gt_eq (compare x y)

theorem cmp_lt_gt_false (x y : float) : cmp .Clt x y = true → cmp .Cgt x y = true → False :=
  cmp_of_comparison_lt_gt_false (compare x y)

end Float

namespace Float32

private theorem binop_nan_comm (x y : float32) (h : is_nan x = false ∨ is_nan y = false) :
    binop_nan x y = binop_nan y x := by
  cases x <;> cases y <;> first | rfl | simp [is_nan] at h

theorem add_commut (x y : float32) (h : is_nan x = false ∨ is_nan y = false) :
    add x y = add y x :=
  Bplus_commut 24 128 (by decide) (by decide) binop_nan .mode_NE x y (binop_nan_comm x y h)

theorem mul_commut (x y : float32) (h : is_nan x = false ∨ is_nan y = false) :
    mul x y = mul y x :=
  Bmult_commut 24 128 (by decide) (by decide) binop_nan .mode_NE x y (binop_nan_comm x y h)

theorem mul2_add (f : float32) : add f f = mul f (of_int (Integers.repr 2)) := by
  refine Bmult2_Bplus 24 128 (by decide) (by decide) binop_nan binop_nan .mode_NE f ?_
  intro x y hx _
  cases x <;> first | rfl | simp [is_nan] at hx

theorem div_mul_inverse (x y z : float32) (h : exact_inverse y = some z) : div x y = mul x z := by
  refine Bdiv_mult_inverse 24 128 (by decide) (by decide) binop_nan binop_nan .mode_NE x y z ?_ h
  intro i j k hi _ _
  cases i <;> first | rfl | simp [is_nan] at hi

theorem cmp_swap (c : Integers.comparison) (x y : float32) :
    cmp (Integers.swap_comparison c) x y = cmp c y x := by
  unfold cmp compare
  rw [cmp_of_comparison_swap, Bcompare_reverse]

theorem cmp_ne_eq (x y : float32) : cmp .Cne x y = !cmp .Ceq x y :=
  cmp_of_comparison_ne_eq (compare x y)

theorem cmp_lt_eq_false (x y : float32) : cmp .Clt x y = true → cmp .Ceq x y = true → False :=
  cmp_of_comparison_lt_eq_false (compare x y)

theorem cmp_le_lt_eq (x y : float32) : cmp .Cle x y = (cmp .Clt x y || cmp .Ceq x y) :=
  cmp_of_comparison_le_lt_eq (compare x y)

theorem cmp_gt_eq_false (x y : float32) : cmp .Cgt x y = true → cmp .Ceq x y = true → False :=
  cmp_of_comparison_gt_eq_false (compare x y)

theorem cmp_ge_gt_eq (x y : float32) : cmp .Cge x y = (cmp .Cgt x y || cmp .Ceq x y) :=
  cmp_of_comparison_ge_gt_eq (compare x y)

theorem cmp_lt_gt_false (x y : float32) : cmp .Clt x y = true → cmp .Cgt x y = true → False :=
  cmp_of_comparison_lt_gt_false (compare x y)

theorem cmp_double (x y : float32) (c : Integers.comparison) :
    cmp c x y = Float.cmp c (to_double x) (to_double y) :=
  congrArg (cmp_of_comparison c)
    (Bcompare_Bconv_widen 24 128 53 1024 (by decide) (by decide) (by decide) (by decide)
      (by decide) Float.of_single_nan .mode_NE x y).symm

end Float32
end Vellvm.Numeric.Floats
