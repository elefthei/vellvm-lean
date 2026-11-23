import Vellvm.Theory.I2F.I2F_exp.MemoryByte
import Vellvm.Semantics.Implementations.Memory.Basic
import Vellvm.Utils.IntMaps.Refinement

namespace Vellvm.Theory.I2F.I2F_memory
open Refinement I2F_exp Semantics.Implementations.Memory Utils.IntMaps

def I2F_byte (b : @byte PInf) (b' : @byte PFin) : Prop :=
  I2F_memory_byte b.1 b'.1 ∧ b.2 = b'.2

def I2F_memory : @memory PInf → @memory PFin → Prop := IM_Refine I2F_byte

def I2F_Frame : @Frame PInf → @Frame PFin → Prop := List.Forall₂ I2F_Addr

inductive I2F_Framestack : @Framestack PInf → @Framestack PFin → Prop where
  | I2F_FS_Singleton {f g} : I2F_Frame f g → I2F_Framestack (@Framestack.Singleton PInf f) (@Framestack.Singleton PFin g)
  | I2F_FS_Snoc {s t f g} : I2F_Framestack s t → I2F_Frame f g →
      I2F_Framestack (@Snoc PInf s f) (@Snoc PFin t g)

export I2F_Framestack (I2F_FS_Singleton I2F_FS_Snoc)

@[elab_as_elim] theorem I2F_Framestack_ind (Q : @Framestack PInf → @Framestack PFin → Prop)
    (one : ∀ f g, I2F_Frame f g → Q (@Framestack.Singleton PInf f) (@Framestack.Singleton PFin g))
    (snoc : ∀ s t f g, I2F_Framestack s t → Q s t → I2F_Frame f g → Q (@Snoc PInf s f) (@Snoc PFin t g))
    {s t} (h : I2F_Framestack s t) : Q s t := by
  induction h with
  | I2F_FS_Singleton hf => exact one _ _ hf
  | I2F_FS_Snoc hs hf ih => exact snoc _ _ _ _ hs ih hf

@[elab_as_elim] alias I2F_Framestack_sind := I2F_Framestack_ind

def I2F_Heap : @Heap PInf → @Heap PFin → Prop := IM_Refine (List.Forall₂ I2F_Addr)

structure I2F_Memory_stack (ms : @Memory_stack PInf) (ms' : @Memory_stack PFin) : Prop where
  Build_I2F_Memory_stack ::
  i2f_ms_memory : I2F_memory (@Memory_stack_memory PInf ms) (@Memory_stack_memory PFin ms')
  i2f_ms_fs : I2F_Framestack (@Memory_stack_frame_stack PInf ms) (@Memory_stack_frame_stack PFin ms')
  i2f_ms_heap : I2F_Heap (@Memory_stack_heap PInf ms) (@Memory_stack_heap PFin ms')

export I2F_Memory_stack (Build_I2F_Memory_stack i2f_ms_memory i2f_ms_fs i2f_ms_heap)

structure I2F_State (s : @State PInf) (t : @State PFin) : Prop where
  Build_I2F_State ::
  i2f_st_ms : I2F_Memory_stack (@state_memory_stack PInf s) (@state_memory_stack PFin t)
  i2f_st_prov : @state_provenance PInf s = @state_provenance PFin t

export I2F_State (Build_I2F_State i2f_st_ms i2f_st_prov)

end Vellvm.Theory.I2F.I2F_memory
