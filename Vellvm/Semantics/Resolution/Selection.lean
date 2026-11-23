import Vellvm.Semantics.Resolution.Basic
import Vellvm.Semantics.InterpretationStack

namespace Vellvm.Semantics.Resolution
open Interfaces.IPtr LLVMEvents Handlers InterpretationStack

variable [IP : IPtr] [T : IPtrTheory] {X : Type}

private theorem resolves_eou (v : EOU.EOU X) :
    Resolves (LLVMEvents.Worker.EOU_to_itree v) (LLVMEvents.Worker.EOU_to_itree v) := by
  cases v with
  | raise_ret x => exact resolves_pure x
  | raise_error s => exact resolves_bind (resolves_pure ()) (fun _ ↦
      resolves_bind (resolves_emit (E := FailureE) (Throw ())) (fun a ↦ nomatch a))
  | raise_oom s => exact resolves_bind (resolves_pure ()) (fun _ ↦
      resolves_bind (resolves_emit (E := OOME) (ThrowOOM ())) (fun a ↦ nomatch a))
  | raise_ub s => exact resolves_bind (resolves_pure ()) (fun _ ↦
      resolves_bind (resolves_emit (E := UBE) (ThrowUB ())) (fun a ↦ nomatch a))

theorem resolves_memM_interpWith (m : Memory.ConcreteMem X) (s : Implementations.Memory.State) :
    Resolves (Memory.Worker.memM_interpWith branchingChooser m s)
      (Memory.Worker.memM_interpWith referenceChooser m s) := by
  induction m generalizing s with
  | Mret x => exact resolves_pure (x, s)
  | Moom msg => exact resolves_eou (.raise_oom msg)
  | Merr msg => exact resolves_eou (.raise_error msg)
  | Mub msg => exact resolves_eou (.raise_ub msg)
  | Mget k ih => exact ih s s
  | Mput s' k ih => exact ih () s'
  | Mchoose c k ih =>
    cases c with
    | Cnext_key size align => exact resolves_bind (resolves_choice _) (fun a ↦ ih a s)
    | Cfresh_prov =>
      exact resolves_bind (resolves_choice _) (fun p ↦ ih p { s with state_provenance := p })
    | Cexposed_prov => exact resolves_bind (resolves_choice _) (fun p ↦ ih p s)

private theorem resolves_mem_lift (m : Memory.ConcreteMem X) (s : FusedS) :
    Resolves (InterpretationStack.Worker.on_mem (Memory.Worker.memM_interpWith branchingChooser m) s)
      (InterpretationStack.Worker.on_mem (Memory.Worker.memM_interpWith referenceChooser m) s) := by
  obtain ⟨mem, rest⟩ := s
  exact resolves_bind (resolves_memM_interpWith m mem)
    (fun (x, mem') ↦ resolves_pure (x, mem', rest))

theorem resolves_fused_memory (e : MemoryE.I) (s : FusedS) :
    Resolves (InterpretationStack.Worker.fused_memory branchingChooser e s)
      (InterpretationStack.Worker.fused_memory referenceChooser e s) := resolves_mem_lift _ s

theorem resolves_fused_intrinsic (e : IntrinsicE.I) (s : FusedS) :
    Resolves (InterpretationStack.Worker.fused_intrinsic branchingChooser e s)
      (InterpretationStack.Worker.fused_intrinsic referenceChooser e s) := resolves_mem_lift _ s

private theorem resolves_draw (e : DrawE.I) :
    Resolves (Draw.Worker.handle_drawWith branchingChooser e)
      (Draw.Worker.handle_drawWith referenceChooser e) := by
  cases e with
  | Draw dt =>
    simp only [Draw.Worker.handle_drawWith]
    split
    · exact resolves_choice _
    · exact resolves_eou (.raise_error _)
    · exact resolves_eou (.raise_oom _)
    · exact resolves_eou (.raise_ub _)

theorem resolves_fused_draw (e : DrawE.I) (s : FusedS) :
    Resolves (InterpretationStack.Worker.fused_draw branchingChooser e s)
      (InterpretationStack.Worker.fused_draw referenceChooser e s) :=
  resolves_bind (resolves_draw e) (fun x ↦ resolves_pure (x, s))

end Vellvm.Semantics.Resolution
