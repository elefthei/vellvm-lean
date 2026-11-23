import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.Unsigned

open Vellvm.Semantics.DynamicValues Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_dvalue_base_int_unsigned"
  I2F_dvalue_base_int_unsigned : ∀ {v : @dvalue_base PInf} {v' : @dvalue_base PFin},
    I2F_dvalue_base v v' → @dvalue_base_int_unsigned PInf v = @dvalue_base_int_unsigned PFin v'
