import PortChecks.SourceType
import Vellvm.Semantics.InterpretationStack

open Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.InterpretationStack Vellvm.Semantics.LLVMEvents

#source_check "src/rocq/Semantics/InterpretationStack.v|Vellvm.Semantics.InterpretationStack|interp_mcfg"
  interp_mcfg : ∀ [Pa : Params] {X : Type}, MCFGtop X → FusedS → MCFGbot (X × FusedS)
