import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_denotation.Mrec

namespace PortChecks.I2FDenotationMrec
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_denotation Vellvm.Semantics.Denotation
open Vellvm.Syntax.DynamicTypes
open Vellvm.Numeric.Rocqlib (option_rel)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_lookup_defn"
  I2F_lookup_defn : ∀ {l r fv fw}, I2F_ctx l r → I2F_dvalue fv fw →
    option_rel I2F_function_denotation (@lookup_defn PInf fv l) (@lookup_defn PFin fw r)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_denote_mcfg"
  I2F_denote_mcfg : ∀ (t : dtyp) {l r fv fw xs ys}, I2F_dvalue fv fw → I2F_targs xs ys →
    I2F_ctx l r → I2F_refine_MCFG (Sum.LiftRel I2F_dvalue I2F_dvalue)
      (@denote_mcfg PInf l t fv xs) (@denote_mcfg PFin r t fw ys)

end PortChecks.I2FDenotationMrec
