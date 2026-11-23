import PortChecks.Theory.I2F.I2F_denotation.Mrec
import Vellvm.Theory.I2F.I2F_denotation.Functions

namespace PortChecks.I2FDenotationFunctions
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_denotation Vellvm.Semantics.Denotation
open Vellvm.Syntax.DynamicTypes Vellvm.Syntax.LLVMAst Vellvm.Syntax.CFG

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_denote_function"
  I2F_denote_function : ∀ d : definition dtyp (cfg dtyp),
    I2F_function_denotation (@denote_function PInf d) (@denote_function PFin d)

end PortChecks.I2FDenotationFunctions
