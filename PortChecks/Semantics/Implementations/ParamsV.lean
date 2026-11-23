import PortChecks.SourceType
import Vellvm.Semantics.Implementations.ParamsV

open Vellvm.Semantics.Interfaces.IPtr Vellvm.Semantics.Interfaces.Params
open Vellvm.Semantics.Implementations.ParamsV

#source_check "src/rocq/Semantics/Implementations/ParamsV.v|Vellvm.Semantics.Implementations.ParamsV|ParamsV"
  ParamsV : ∀ [IP : IPtr] [@IPtrTheory IP], Params
