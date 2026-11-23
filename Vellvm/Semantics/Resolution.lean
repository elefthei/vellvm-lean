import Vellvm.Semantics.Resolution.Environment
import Vellvm.Semantics.Resolution.Selection
import Vellvm.Semantics.Resolution.State

namespace Vellvm.Semantics
open CTree (CTree)
open ITree (Effect)
open Vellvm.Tree Interfaces.IPtr LLVMEvents InterpretationStack

namespace Resolution
variable [IP : IPtr] [T : IPtrTheory]

private theorem resolves_fused_trigger {F : Effect} [F -< MCFGEbot] (e : F.I) (s : FusedS) :
    Resolves (InterpretationStack.Worker.fused_trigger (F := F) e s)
      (InterpretationStack.Worker.fused_trigger (F := F) e s) :=
  resolves_bind (resolves_emit (E := F) e) (fun x ↦ resolves_pure (x, s))

theorem resolves_handler (e : MCFGEtop.I) (s : FusedS) :
    Resolves (InterpretationStack.Worker.interp_vellvm_hWith branchingChooser e s)
      (InterpretationStack.Worker.interp_vellvm_hWith referenceChooser e s) := by
  rcases e with e | e | e | (e | e) | e | e | e
  · exact resolves_fused_trigger (F := ExternalCallE) e s
  · exact resolves_fused_intrinsic e s
  · exact resolves_fused_global e s
  · exact resolves_fused_local e s
  · exact resolves_fused_stack e s
  · exact resolves_fused_memory e s
  · exact resolves_fused_draw e s
  · exact resolves_fused_trigger (F := OOME ⊕ₑ LLVMExcE ⊕ₑ UBE ⊕ₑ DebugE ⊕ₑ FailureE) e s

end Resolution

/-- Resolving the choices of the model recovers the reference interpreter on every open tree. -/
theorem interp_mcfg_is_resolution [IP : IPtr] [T : IPtrTheory] {X : Type}
    (t : MCFGtop X) (s : FusedS) :
    eutt Eq (CTree.refine canonical (interp_mcfg_model t s)) (interp_mcfg t s) :=
  Resolution.refine_state_handler canonical _ _ Resolution.resolves_handler
    (Handlers.Intrinsics.Worker.interp_intrinsics t) s

end Vellvm.Semantics
