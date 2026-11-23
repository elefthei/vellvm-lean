import PortChecks.SourceType
import Vellvm.Semantics.Handlers.Draw

open ITree (Effect)
open Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.LLVMEvents Vellvm.Semantics.Handlers.Draw

#source_check "src/rocq/Semantics/Handlers/Draw.v|Vellvm.Semantics.Handlers.Draw|handle_draw"
  handle_draw : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] [OOME -< E] [UBE -< E]
    (e : DrawE.I), CTree.CTree E B (DrawE.O e)
