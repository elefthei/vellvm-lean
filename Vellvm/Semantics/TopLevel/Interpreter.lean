import Vellvm.Semantics.TopLevel.Program
import Vellvm.Semantics.InterpretationStack
import Vellvm.Semantics.Implementations.ParamsV
import Vellvm.Semantics.Implementations.IPtrInfinite

namespace Vellvm.Semantics.TopLevel
open ITree (Effect)
open Tree Interfaces.Params Instrumentation DynamicValues Syntax.LLVMAst Syntax.DynamicTypes
open LLVMEvents (MCFGEtop MCFGEbot MCFGtop MCFGbot)
open InterpretationStack (FusedS Res)

variable [Pa : Params]

def initialState : FusedS :=
  (Implementations.Memory.MemoryModelStateV.initial_state,
    (⟨Syntax.RawIdMaps.RM.empty dvalue, none, none⟩, []), Syntax.RawIdMaps.RM.empty dvalue)

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M] [Diagnostics M] [Snapshots M] [Catch M]

def interpreter_gen (ret_typ : dtyp) (entry : function_id)
    (arg_gen : M MCFGEtop NoChoice (List (dtyp × dvalue))) (prog : ll_toplevel_entities) :
    M MCFGEbot NoChoice (Res dvalue) :=
  InterpretationStack.Worker.interp_mcfg (open_program ret_typ entry arg_gen prog) initialState

def interpreter_param (argv : List IRString) (prog : ll_toplevel_entities) : M MCFGEbot NoChoice (Res dvalue) :=
  InterpretationStack.Worker.interp_mcfg (open_main argv prog) initialState

end Worker

def interpreter_gen (ret_typ : dtyp) (entry : function_id) (arg_gen : MCFGtop (List (dtyp × dvalue)))
    (prog : ll_toplevel_entities) : MCFGbot (Res dvalue) := Worker.interpreter_gen ret_typ entry arg_gen prog

def interpreter_param (argv : List IRString) (prog : ll_toplevel_entities) : MCFGbot (Res dvalue) :=
  Worker.interpreter_param argv prog

open Implementations.IPtrInfinite

def interpreter := @interpreter_param (@Implementations.ParamsV.ParamsV IPZ IPZTheory)
def dvalue_eqb := @DynamicValues.dvalue_eqb (@Implementations.ParamsV.ParamsV IPZ IPZTheory)
def dvalue_is_canonical := @DynamicValues.dvalue_is_canonical (@Implementations.ParamsV.ParamsV IPZ IPZTheory)

end Vellvm.Semantics.TopLevel
