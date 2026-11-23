import Vellvm.Theory.I2F.I2F_denotation.Core
import Vellvm.Theory.I2F.I2F_exp.Freeze

namespace Vellvm.Theory.I2F.I2F_denotation
open Semantics.DynamicValues Semantics.Operations.Freeze Syntax.DynamicTypes Refinement I2F_exp

theorem I2F_freeze_base' (dt : dtyp) {a b} (h : I2F_dvalue_base a b) :
    I2F_refine_CFG I2F_dvalue (freeze_base (Pa := PInf) dt a) (freeze_base (Pa := PFin) dt b) :=
  I2F_freeze_base_gen I2F_draw_CFG dt h

theorem I2F_freeze' (dt : dtyp) {a b} (h : I2F_dvalue a b) :
    I2F_refine_CFG I2F_dvalue (freeze (Pa := PInf) dt a) (freeze (Pa := PFin) dt b) :=
  I2F_freeze_gen I2F_draw_CFG I2FE_CFG_Throw dt h

end Vellvm.Theory.I2F.I2F_denotation
