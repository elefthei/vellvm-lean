import Vellvm.Semantics.Handlers

namespace Vellvm.Semantics.InterpretationStack
open ITree (Effect)
open CTree (CTree)
open Interfaces.Params LLVMEvents Tree Instrumentation Handlers

abbrev FusedS [Params] := Implementations.Memory.State × ((Stack.stack_frame × Stack.stack) × Global.global_env)
abbrev Res [Params] (X : Type) := X × FusedS

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M] [Pa : Params] {B : Effect} {X : Type}

abbrev Out (M : Effect → Effect → Type → Type v) (B : Effect) [Params] (X : Type) :=
  FusedS → M MCFGEbot B (Res X)

def on_mem (f : Implementations.Memory.State → M MCFGEbot B (X × Implementations.Memory.State)) :
    Out M B X := fun (mem, rest) ↦ do let (r, mem') ← f mem; pure (r, mem', rest)

def on_ls (f : Stack.State → M MCFGEbot B (X × Stack.State)) : Out M B X :=
  fun (mem, ls, g) ↦ do let (r, ls') ← f ls; pure (r, mem, ls', g)

def on_genv (f : Global.global_env → M MCFGEbot B (X × Global.global_env)) : Out M B X :=
  fun (mem, ls, g) ↦ do let (r, g') ← f g; pure (r, mem, ls, g')

def fused_trigger {F : Effect} [F -< MCFGEbot] (e : F.I) : Out M B (F.O e) := fun s ↦ do
  return (← Runtime.emit (E := F) e, s)

variable [Diagnostics M] [Snapshots M]

def fused_intrinsic (pick : Chooser Pa M MCFGEbot B) (e : IntrinsicE.I) : Out M B (IntrinsicE.O e) :=
  on_mem (Memory.Worker.handle_intrinsic (fun m s ↦ Memory.Worker.memM_interpWith pick m s) e)

def fused_memory (pick : Chooser Pa M MCFGEbot B) (e : MemoryE.I) : Out M B (MemoryE.O e) :=
  on_mem (Memory.Worker.handle_memory (fun m s ↦ Memory.Worker.memM_interpWith pick m s) e)

def fused_draw (pick : Chooser Pa M MCFGEbot B) (e : DrawE.I) : Out M B (DrawE.O e) := fun s ↦ do
  return (← Draw.Worker.handle_drawWith pick e, s)

def fused_global (e : GlobalE.I) : Out M B (GlobalE.O e) := on_genv (Global.Worker.handle_global_debug e)

def fused_local (e : LocalE.I) : Out M B (LocalE.O e) :=
  on_ls (Stack.Worker.handle_local_stack Local.Worker.handle_local_debug e)

def fused_stack (e : StackE.I) : Out M B (StackE.O e) := on_ls (Stack.Worker.handle_stack e)

def interp_vellvm_hWith (pick : Chooser Pa M MCFGEbot B) (e : MCFGEtop.I) : Out M B (MCFGEtop.O e) :=
  match e with
  | .inl ext => fused_trigger (F := ExternalCallE) ext
  | .inr (.inl intr) => fused_intrinsic pick intr
  | .inr (.inr (.inl g)) => fused_global g
  | .inr (.inr (.inr (.inl (.inl l)))) => fused_local l
  | .inr (.inr (.inr (.inl (.inr s)))) => fused_stack s
  | .inr (.inr (.inr (.inr (.inl m)))) => fused_memory pick m
  | .inr (.inr (.inr (.inr (.inr (.inl d))))) => fused_draw pick d
  | .inr (.inr (.inr (.inr (.inr (.inr r))))) =>
    fused_trigger (F := OOME ⊕ₑ LLVMExcE ⊕ₑ UBE ⊕ₑ DebugE ⊕ₑ FailureE) r

def interp_mcfgWith {C : Effect} [C -< B] (pick : Chooser Pa M MCFGEbot B) (t : M MCFGEtop C X)
    (s : FusedS) : M MCFGEbot B (Res X) :=
  Runtime.interp_state (interp_vellvm_hWith pick) (Intrinsics.Worker.interp_intrinsics t) s

def interp_mcfg (t : M MCFGEtop NoChoice X) (s : FusedS) : M MCFGEbot NoChoice (Res X) :=
  interp_mcfgWith referenceChooser t s

end Worker

variable [Pa : Params] {X : Type}

def on_mem (f : Implementations.Memory.State → MCFGbot (X × Implementations.Memory.State)) :=
  Worker.on_mem f
def on_ls (f : Stack.State → MCFGbot (X × Stack.State)) := Worker.on_ls f
def on_genv (f : Global.global_env → MCFGbot (X × Global.global_env)) := Worker.on_genv f

def fused_trigger {F : Effect} [F -< MCFGEbot] (e : F.I) := Worker.fused_trigger (M := CTree) (B := NoChoice) (F := F) e
def fused_intrinsic (e : IntrinsicE.I) := Worker.fused_intrinsic (M := CTree) (B := NoChoice) referenceChooser e
def fused_memory (e : MemoryE.I) := Worker.fused_memory (M := CTree) (B := NoChoice) referenceChooser e
def fused_draw (e : DrawE.I) := Worker.fused_draw (M := CTree) (B := NoChoice) referenceChooser e
def fused_global (e : GlobalE.I) := Worker.fused_global (M := CTree) (B := NoChoice) e
def fused_local (e : LocalE.I) := Worker.fused_local (M := CTree) (B := NoChoice) e
def fused_stack (e : StackE.I) := Worker.fused_stack (M := CTree) (B := NoChoice) e

def interp_vellvm_h := Worker.interp_vellvm_hWith (M := CTree) (Pa := Pa) (B := NoChoice) referenceChooser

def interp_mcfg (t : MCFGtop X) (s : FusedS) := Worker.interp_mcfg t s
def interp_mcfg' (t : MCFGtop X) (g : Global.global_env) (l : Stack.State) (m : Implementations.Memory.State) :=
  interp_mcfg t (m, l, g)

instance [Pa : Params] : NoChoice -< Choice Pa := ⟨fun (x : PEmpty) ↦ nomatch x⟩

def interp_mcfg_model (t : MCFGtop X) (s : FusedS) : CTree MCFGEbot (Choice Pa) (Res X) :=
  Worker.interp_mcfgWith branchingChooser t s

end Vellvm.Semantics.InterpretationStack
