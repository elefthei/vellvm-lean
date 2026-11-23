/-
The Compcert verified compiler
Xavier Leroy and Jacques-Henri Jourdan, INRIA Paris-Rocquencourt
Copyright Institut National de Recherche en Informatique et en Automatique. All rights reserved.
This file is distributed under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation, either version 2.1 of the License, or (at your option) any later
version. This file is also distributed under the terms of the INRIA Non-Commercial License Agreement.
-/
import PortChecks.SourceType
import Vellvm.Numeric.Floats.ArithmeticFacts

namespace Vellvm.Numeric.Floats
open Flocq

namespace Float

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|add_commut"
  add_commut : ∀ (x y : binary_float 53 1024), (is_nan x = false ∨ is_nan y = false) →
    add x y = add y x

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|mul_commut"
  mul_commut : ∀ (x y : binary_float 53 1024), (is_nan x = false ∨ is_nan y = false) →
    mul x y = mul y x

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|mul2_add"
  mul2_add : ∀ f : float, add f f = mul f (of_int (@Integers.repr ⟨32, by decide⟩ 2))

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|div_mul_inverse"
  div_mul_inverse : ∀ x y z : float, exact_inverse y = some z → div x y = mul x z

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|cmp_swap"
  cmp_swap : ∀ (c : Integers.comparison) (x y : float), cmp (Integers.swap_comparison c) x y =
    cmp c y x

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|cmp_ne_eq"
  cmp_ne_eq : ∀ x y : float, cmp .Cne x y = !(cmp .Ceq x y)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|cmp_lt_eq_false"
  cmp_lt_eq_false : ∀ x y : float, cmp .Clt x y = true → cmp .Ceq x y = true → False

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|cmp_le_lt_eq"
  cmp_le_lt_eq : ∀ x y : float, cmp .Cle x y = (cmp .Clt x y || cmp .Ceq x y)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|cmp_gt_eq_false"
  cmp_gt_eq_false : ∀ x y : float, cmp .Cgt x y = true → cmp .Ceq x y = true → False

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|cmp_ge_gt_eq"
  cmp_ge_gt_eq : ∀ x y : float, cmp .Cge x y = (cmp .Cgt x y || cmp .Ceq x y)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|cmp_lt_gt_false"
  cmp_lt_gt_false : ∀ x y : float, cmp .Clt x y = true → cmp .Cgt x y = true → False

end Float

namespace Float32

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|add_commut"
  add_commut : ∀ (x y : binary_float 24 128), (is_nan x = false ∨ is_nan y = false) →
    add x y = add y x

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|mul_commut"
  mul_commut : ∀ (x y : binary_float 24 128), (is_nan x = false ∨ is_nan y = false) →
    mul x y = mul y x

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|mul2_add"
  mul2_add : ∀ f : float32, add f f = mul f (of_int (@Integers.repr ⟨32, by decide⟩ 2))

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|div_mul_inverse"
  div_mul_inverse : ∀ x y z : float32, exact_inverse y = some z → div x y = mul x z

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|cmp_swap"
  cmp_swap : ∀ (c : Integers.comparison) (x y : float32), cmp (Integers.swap_comparison c) x y =
    cmp c y x

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|cmp_ne_eq"
  cmp_ne_eq : ∀ x y : float32, cmp .Cne x y = !(cmp .Ceq x y)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|cmp_lt_eq_false"
  cmp_lt_eq_false : ∀ x y : float32, cmp .Clt x y = true → cmp .Ceq x y = true → False

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|cmp_le_lt_eq"
  cmp_le_lt_eq : ∀ x y : float32, cmp .Cle x y = (cmp .Clt x y || cmp .Ceq x y)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|cmp_gt_eq_false"
  cmp_gt_eq_false : ∀ x y : float32, cmp .Cgt x y = true → cmp .Ceq x y = true → False

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|cmp_ge_gt_eq"
  cmp_ge_gt_eq : ∀ x y : float32, cmp .Cge x y = (cmp .Cgt x y || cmp .Ceq x y)

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|cmp_lt_gt_false"
  cmp_lt_gt_false : ∀ x y : float32, cmp .Clt x y = true → cmp .Cgt x y = true → False

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|cmp_double"
  cmp_double : ∀ (x y : float32) (c : Integers.comparison), cmp c x y =
    Float.cmp c (to_double x) (to_double y)

end Float32
end Vellvm.Numeric.Floats
