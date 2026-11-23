import Vellvm.Semantics.Resolution
import Vellvm.Semantics.TopLevel.Interpreter

namespace Vellvm.Semantics
open CTree (CTree)
open Vellvm.Tree Interfaces.IPtr LLVMEvents DynamicValues InterpretationStack

variable [IP : IPtr] [T : IPtrTheory]

/-- Interpret the same open main program, exposing legal draw and memory choices as branches. -/
def model_param (argv : List IRString) (prog : TopLevel.ll_toplevel_entities) :
    CTree MCFGEbot (Choice (@Implementations.ParamsV.ParamsV IP T)) (Res dvalue) :=
  interp_mcfg_model (TopLevel.Worker.open_main argv prog) TopLevel.initialState

/-- The result and all fused state agree for every program, in either concrete pointer model. -/
theorem interpreter_param_is_resolution (argv : List IRString) (prog : TopLevel.ll_toplevel_entities) :
    eutt Eq (CTree.refine canonical (model_param argv prog)) (TopLevel.interpreter_param argv prog) :=
  interp_mcfg_is_resolution (TopLevel.Worker.open_main argv prog) TopLevel.initialState

end Vellvm.Semantics
