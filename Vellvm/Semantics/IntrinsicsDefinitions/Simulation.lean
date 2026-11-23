module

public import Vellvm.Semantics.IntrinsicsDefinitions
public import Vellvm.Semantics.Simulation

@[expose] public section
namespace Vellvm.Semantics.IntrinsicsDefinitions.Worker
open ITree (Effect Subeffect)
open Vellvm.Tree Interfaces.Params DynamicValues Syntax.DynamicTypes LLVMEvents Instrumentation

variable {M : Effect → Effect → Type → Type v} {N : Effect → Effect → Type → Type w}
variable [Runtime M] [Runtime N] [Diagnostics M] [Diagnostics N] [Pa : Params]
variable [Snapshots M] [Snapshots N] (sim : Simulation M N) {E B : Effect}

theorem llvm_va_start_sim [MemoryE -< E] [UBE -< E] [FailureE -< E] (args : List dvalue)
    (va : Option Pa.PTR.ptr) : sim.R (E := E) (B := B) (llvm_va_start args va) (llvm_va_start args va) := by
  rcases args with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> cases va <;> try exact sim.«raise» _
  cases a with
  | DVALUE_Base b => cases b <;> first | exact sim.raiseUB _ | exact sim.bind (sim.store _ _ _) (fun _ ↦ sim.pure _)
  | _ => exact sim.bind (sim.store _ _ _) (fun _ ↦ sim.pure _)

theorem llvm_va_copy_sim [MemoryE -< E] [FailureE -< E] (args : List dvalue)
    (va : Option Pa.PTR.ptr) : sim.R (E := E) (B := B) (llvm_va_copy args va) (llvm_va_copy args va) := by
  rcases args with _ | ⟨d, _ | ⟨s, _ | ⟨_, _⟩⟩⟩ <;> try exact sim.«raise» _
  exact sim.bind (sim.load _ _) fun v ↦ sim.bind (sim.store _ _ v) fun _ ↦ sim.pure _

variable [FailureE -< E] [UBE -< E] [OOME -< E] [MemoryE -< E]

theorem intrinsic_semantics_sim (t : dtyp) (fam : intrinsic_family) :
    Option.Rel (fun (f : semantic_function M E B) (g : semantic_function N E B) ↦
      ∀ args va, sim.R (f args va) (g args va)) (intrinsic_semantics t fam) (intrinsic_semantics t fam) := by
  cases fam <;> first
    | exact .none
    | exact .some (fun _ _ ↦ sim.liftEOU _)
    | exact .some (llvm_va_start_sim sim)
    | exact .some (llvm_va_copy_sim sim)
    | exact .some (fun _ _ ↦ sim.pure _)

theorem named_intrinsic_semantics_sim (t : dtyp) (name : IRString) :
    Option.Rel (fun (f : semantic_function M E B) (g : semantic_function N E B) ↦
      ∀ args va, sim.R (f args va) (g args va)) (named_intrinsic_semantics t name) (named_intrinsic_semantics t name) := by
  unfold named_intrinsic_semantics
  cases lookup_intrinsic name with
  | none => exact .none
  | some fam => exact intrinsic_semantics_sim sim t fam

end Vellvm.Semantics.IntrinsicsDefinitions.Worker
