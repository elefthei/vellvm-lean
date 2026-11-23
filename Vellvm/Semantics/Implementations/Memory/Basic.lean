module

public import Vellvm.Semantics.Interfaces.Memory
public import Vellvm.Utils.IntMaps.Basic

@[expose] public section
namespace Vellvm.Semantics.Implementations.Memory
open Interfaces.Params Interfaces.Memory MemoryBytes Utils.IntMaps

variable [Pa : Params]

abbrev byte := memory_byte × Pa.PROV.allocationId
abbrev memory := IntMap (byte (Pa := Pa))
abbrev Frame := List Pa.PTR.ptr

inductive Framestack [Pa : Params] where
  | Singleton (f : Frame)
  | Snoc (s : Framestack) (f : Frame)
export Framestack (Singleton Snoc)

@[elab_as_elim] def Framestack_rect (P : Framestack → Type u)
    (one : ∀ f, P (Singleton f)) (snoc : ∀ s, P s → ∀ f, P (Snoc s f)) : ∀ s, P s
  | .Singleton f => one f
  | .Snoc s f => snoc s (Framestack_rect P one snoc s) f

@[elab_as_elim] abbrev Framestack_rec (P : Framestack → Type) := Framestack_rect P
@[elab_as_elim] theorem Framestack_ind (P : Framestack → Prop)
    (one : ∀ f, P (Singleton f)) (snoc : ∀ s, P s → ∀ f, P (Snoc s f)) : ∀ s, P s :=
  Framestack.rec (motive := P) one (fun s f ih ↦ snoc s ih f)
@[elab_as_elim] alias Framestack_sind := Framestack_ind

abbrev block := List Pa.PTR.ptr
abbrev Heap := IntMap (block (Pa := Pa))

structure Memory_stack [Pa : Params] where
  mkMemoryStack ::
  Memory_stack_memory : memory
  Memory_stack_frame_stack : Framestack
  Memory_stack_heap : Heap
export Memory_stack (mkMemoryStack Memory_stack_memory Memory_stack_frame_stack Memory_stack_heap)

def memory_empty : memory := Utils.IntMaps.empty
def frame_empty : Framestack := Singleton []
def heap_empty : Heap := Utils.IntMaps.empty
def empty_memory_stack : Memory_stack := mkMemoryStack memory_empty frame_empty heap_empty

structure State [Pa : Params] where
  mkState ::
  state_memory_stack : Memory_stack
  state_provenance : Pa.PROV.provenance
export State (mkState state_memory_stack state_provenance)

/-- Use the supplied primitives' state when typechecking generic memory code. -/
instance (priority := low) MemoryModelStateV : MemoryModelState where
  state := State
  memory_stack := Memory_stack
  frame := Frame
  framestack := Framestack
  heap := Heap
  state_get_memory := state_memory_stack
  state_get_provenance := state_provenance
  memory_stack_framestack := Memory_stack_frame_stack
  memory_stack_heap := Memory_stack_heap
  state_put_memory s m := { s with state_memory_stack := m }
  initial_state := mkState empty_memory_stack Pa.PROV.initial_provenance
  initial_frame := []
  initial_heap := heap_empty

end Vellvm.Semantics.Implementations.Memory
