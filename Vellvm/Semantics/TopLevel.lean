import Vellvm.Semantics.TopLevel.Interpreter
import Vellvm.Semantics.InterpretationStackFacts
import Vellvm.Semantics.InstrumentationFacts

namespace Vellvm.Semantics.TopLevel
open ITree (Effect)
open Tree Interfaces.Params Instrumentation DynamicValues Syntax.LLVMAst Syntax.DynamicTypes
open LLVMEvents (MCFGEtop MCFGEbot)

variable [Pa : Params]

namespace Worker
variable {M : Effect → Effect → Type → Type v} {N : Effect → Effect → Type → Type w}
variable [Runtime M] [Runtime N] [Diagnostics M] [Diagnostics N] [Snapshots M] [Snapshots N] [Catch M] [Catch N]
variable (sim : Simulation M N) (hc : Denotation.CatchCompatible sim)
include hc

theorem interpreter_gen_related (ret_typ : dtyp) (entry : function_id)
    {l : M MCFGEtop NoChoice (List (dtyp × dvalue))} {r : N MCFGEtop NoChoice (List (dtyp × dvalue))}
    (h : sim.R l r) (prog : ll_toplevel_entities) :
    sim.R (interpreter_gen ret_typ entry l prog) (interpreter_gen ret_typ entry r prog) :=
  InterpretationStack.Worker.interp_mcfg_related sim (open_program_related sim hc ret_typ entry h prog) initialState

theorem interpreter_param_related (argv : List IRString) (prog : ll_toplevel_entities) :
    sim.R (interpreter_param argv prog) (interpreter_param argv prog) :=
  interpreter_gen_related sim hc _ _ (build_main_args_related sim argv) prog

end Worker

/-- The executable, uninstrumented cursor denotes the public interpreter, including all LLVM state. -/
theorem interpreter_cursor_adequate (argv : List IRString) (prog : ll_toplevel_entities) :
    (Worker.interpreter_param (M := Producer) argv prog).meaning = interpreter_param argv prog :=
  Worker.interpreter_param_related producerSimulation (@producerCatchCompatible Pa) argv prog

/-- Erasing only the private debugger requests preserves the head-sensitive public semantics. -/
theorem instrumentation_erasure (argv : List IRString) (prog : ll_toplevel_entities) :
    eutt Eq (erase (Producer.meaning (Worker.interpreter_param (M := Logged (Pa := Pa)) argv prog)))
      (interpreter_param argv prog) :=
  Worker.interpreter_param_related loggedSimulation (@loggedCatchCompatible Pa) argv prog

/-- A debugger can keep arbitrary side state; forgetting it does not forget any LLVM state. -/
theorem tracked_instrumentation_erasure (argv : List IRString) (prog : ll_toplevel_entities)
    {S : Type} (update : S → TraceRequest → S) (s : S) :
    eutt Eq (erase (Producer.meaning (track update (Worker.interpreter_param argv prog) s)) >>=
      fun xs ↦ pure xs.1) (interpreter_param argv prog) :=
  agrees_tracked_cursor (Worker.interpreter_param_related loggedSimulation (@loggedCatchCompatible Pa) argv prog) update s

end Vellvm.Semantics.TopLevel
