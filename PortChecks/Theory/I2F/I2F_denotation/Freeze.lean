import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_denotation.Freeze

namespace PortChecks.I2FDenotationFreeze
open Vellvm.Semantics.Operations.Freeze Vellvm.Semantics.DynamicValues Vellvm.Syntax.DynamicTypes
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_denotation

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_freeze_base'"
  I2F_freeze_base' : ∀ (t : dtyp) {v : @dvalue_base PInf} {w : @dvalue_base PFin},
    I2F_dvalue_base v w → I2F_refine_CFG I2F_dvalue
      (freeze_base (Pa := PInf) t v) (freeze_base (Pa := PFin) t w)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_freeze'"
  I2F_freeze' : ∀ (t : dtyp) {v : @dvalue PInf} {w : @dvalue PFin},
    I2F_dvalue v w → I2F_refine_CFG I2F_dvalue (freeze (Pa := PInf) t v) (freeze (Pa := PFin) t w)

end PortChecks.I2FDenotationFreeze
