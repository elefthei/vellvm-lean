import Vellvm.Semantics.Resolution.Basic
import Vellvm.Semantics.InterpretationStack

namespace Vellvm.Semantics.Resolution
open CTree (CTree)
open Vellvm.Tree (NoChoice)
open Interfaces.IPtr LLVMEvents Handlers InterpretationStack Syntax.RawIdMaps

variable [IP : IPtr] [T : IPtrTheory]

private theorem resolves_failure {X : Type} (msg : IRString) :
    Resolves (X := X) (LLVMEvents.Worker.«raise» msg) (LLVMEvents.Worker.«raise» msg) :=
  resolves_bind (resolves_pure ()) fun _ ↦
    resolves_bind (resolves_emit (E := FailureE) (Throw ())) fun a ↦ nomatch a

theorem resolves_fused_global (e : GlobalE.I) (s : FusedS) :
    Resolves (InterpretationStack.Worker.fused_global (M := CTree) (B := Choice _) e s)
      (InterpretationStack.Worker.fused_global (M := CTree) (B := NoChoice) e s) := by
  rcases s with ⟨mem, ls, g⟩
  unfold InterpretationStack.Worker.fused_global InterpretationStack.Worker.on_genv
  refine resolves_bind ?_ (fun (x, g') ↦ resolves_pure (x, mem, ls, g'))
  change Resolves (Global.handle_global_debug e g) (Global.handle_global_debug e g)
  simp only [Global.handle_global_debug_eq]
  cases e with
  | GlobalWrite _ _ => exact resolves_pure _
  | GlobalRead k =>
    simp only [Global.handle_global, Global.Worker.handle_global]
    cases RM.find k g with
    | none => exact resolves_failure _
    | some _ => exact resolves_pure _

theorem resolves_fused_local (e : LocalE.I) (s : FusedS) :
    Resolves (InterpretationStack.Worker.fused_local (M := CTree) (B := Choice _) e s)
      (InterpretationStack.Worker.fused_local (M := CTree) (B := NoChoice) e s) := by
  rcases s with ⟨mem, ⟨frame, stk⟩, g⟩
  unfold InterpretationStack.Worker.fused_local InterpretationStack.Worker.on_ls
  refine resolves_bind ?_ (fun (x, ls') ↦ resolves_pure (x, mem, ls', g))
  unfold Stack.Worker.handle_local_stack
  refine resolves_bind ?_ (fun (_, _) ↦ resolves_bind (resolves_pure ()) fun _ ↦ resolves_pure _)
  change Resolves (Local.handle_local_debug e frame.stack_vars)
    (Local.handle_local_debug e frame.stack_vars)
  simp only [Local.handle_local_debug_eq]
  cases e with
  | LocalWrite _ _ => exact resolves_pure _
  | LocalRead k =>
    simp only [Local.handle_local, Local.Worker.handle_local]
    cases RM.find k frame.stack_vars with
    | none => exact resolves_failure _
    | some _ => exact resolves_pure _

theorem resolves_fused_stack (e : StackE.I) (s : FusedS) :
    Resolves (InterpretationStack.Worker.fused_stack (M := CTree) (B := Choice _) e s)
      (InterpretationStack.Worker.fused_stack (M := CTree) (B := NoChoice) e s) := by
  rcases s with ⟨mem, ⟨frame, stk⟩, g⟩
  unfold InterpretationStack.Worker.fused_stack InterpretationStack.Worker.on_ls
  refine resolves_bind ?_ (fun (x, ls') ↦ resolves_pure (x, mem, ls', g))
  cases e with
  | StackPush _ => exact resolves_bind (resolves_pure ()) fun _ ↦ resolves_pure _
  | StackPop =>
    cases stk with
    | nil => exact resolves_failure _
    | cons _ _ => exact resolves_bind (resolves_pure ()) fun _ ↦ resolves_pure _
  | StackRaise _ => exact resolves_pure _
  | StackGetExc => exact resolves_pure _

end Vellvm.Semantics.Resolution
