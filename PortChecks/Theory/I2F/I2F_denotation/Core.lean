import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_denotation.Core

namespace PortChecks.I2FDenotationCore
open Vellvm Vellvm.Semantics.DynamicValues Vellvm.Semantics.LLVMEvents Vellvm.Semantics.EOU
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_denotation Vellvm.Syntax.DynamicTypes
open Vellvm.Semantics.Denotation Vellvm.Utils.IntMaps Vellvm.Numeric.Rocqlib

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|refine_dvalue_base_map'"
  refine_dvalue_base_map' : ∀ {l : @CFGtop PInf (@dvalue_base PInf)} {r : @CFGtop PFin (@dvalue_base PFin)},
    I2F_refine_CFG I2F_dvalue_base l r → I2F_refine_CFG I2F_dvalue
      ((@DVALUE_Base PInf) <$> l) ((@DVALUE_Base PFin) <$> r)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_draw_CFG"
  I2F_draw_CFG : ∀ t : dtyp, I2F_refine_CFG I2F_dvalue (draw (Pa := PInf) t) (draw (Pa := PFin) t)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_refine_lift'"
  I2F_refine_lift' : ∀ {X Y : Type} (R : X → Y → Prop) (l : EOU X) (r : EOU Y), I2F_EOU R l r →
    I2F_refine_CFG R (EOU_to_itree l) (EOU_to_itree r)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_function_denotation"
  I2F_function_denotation : @function_denotation PInf → @function_denotation PFin → Prop

example (f : @function_denotation PInf) (g : @function_denotation PFin) :
    I2F_function_denotation f g =
      (∀ cc t xs ys, I2F_targs xs ys → I2F_refine_CFG (Sum.LiftRel I2F_dvalue I2F_dvalue)
        (f cc t xs) (g cc t ys)) := rfl

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_ctx"
  I2F_ctx : IntMap (@function_denotation PInf) → IntMap (@function_denotation PFin) → Prop

example (l : IntMap (@function_denotation PInf)) (r : IntMap (@function_denotation PFin)) :
    I2F_ctx l r = (∀ k, option_rel I2F_function_denotation (lookup k l) (lookup k r)) := rfl

end PortChecks.I2FDenotationCore
