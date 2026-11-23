import Vellvm.Theory.I2F.Refinement.Values
import Vellvm.Semantics.DynamicValues.Core

namespace Vellvm.Theory.I2F.I2F_exp
open Refinement Semantics.DynamicValues

theorem I2F_dvalue_base_int_unsigned {v : @dvalue_base PInf} {v' : @dvalue_base PFin} :
    I2F_dvalue_base v v' → @dvalue_base_int_unsigned PInf v = @dvalue_base_int_unsigned PFin v' := by
  intro h
  cases h <;> first | rfl | assumption

end Vellvm.Theory.I2F.I2F_exp
