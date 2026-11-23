import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_memory.State

open Vellvm.Semantics.Implementations.Memory Vellvm.Theory.I2F.Refinement
open Vellvm.Theory.I2F.I2F_memory

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_byte"
  I2F_byte : @byte PInf → @byte PFin → Prop

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_memory"
  I2F_memory : @memory PInf → @memory PFin → Prop

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_Frame"
  I2F_Frame : @Frame PInf → @Frame PFin → Prop

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_Framestack"
  I2F_Framestack : @Framestack PInf → @Framestack PFin → Prop

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_Heap"
  I2F_Heap : @Heap PInf → @Heap PFin → Prop

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_Memory_stack"
  I2F_Memory_stack : @Memory_stack PInf → @Memory_stack PFin → Prop

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_State"
  I2F_State : @State PInf → @State PFin → Prop

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_FS_Singleton"
  I2F_FS_Singleton : ∀ {f g}, I2F_Frame f g → I2F_Framestack (@Framestack.Singleton PInf f) (@Framestack.Singleton PFin g)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_FS_Snoc"
  I2F_FS_Snoc : ∀ {s t f g}, I2F_Framestack s t → I2F_Frame f g → I2F_Framestack (@Snoc PInf s f) (@Snoc PFin t g)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_Framestack_ind"
  I2F_Framestack_ind : ∀ (Q : @Framestack PInf → @Framestack PFin → Prop),
    (∀ f g, I2F_Frame f g → Q (@Framestack.Singleton PInf f) (@Framestack.Singleton PFin g)) →
    (∀ s t f g, I2F_Framestack s t → Q s t → I2F_Frame f g → Q (@Snoc PInf s f) (@Snoc PFin t g)) →
    ∀ {s t}, I2F_Framestack s t → Q s t

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_Framestack_sind"
  I2F_Framestack_sind : ∀ (Q : @Framestack PInf → @Framestack PFin → Prop),
    (∀ f g, I2F_Frame f g → Q (@Framestack.Singleton PInf f) (@Framestack.Singleton PFin g)) →
    (∀ s t f g, I2F_Framestack s t → Q s t → I2F_Frame f g → Q (@Snoc PInf s f) (@Snoc PFin t g)) →
    ∀ {s t}, I2F_Framestack s t → Q s t

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|i2f_ms_memory"
  i2f_ms_memory : ∀ {s : @Memory_stack PInf} {t : @Memory_stack PFin}, I2F_Memory_stack s t → I2F_memory (@Memory_stack_memory PInf s) (@Memory_stack_memory PFin t)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|i2f_ms_fs"
  i2f_ms_fs : ∀ {s : @Memory_stack PInf} {t : @Memory_stack PFin}, I2F_Memory_stack s t → I2F_Framestack (@Memory_stack_frame_stack PInf s) (@Memory_stack_frame_stack PFin t)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|i2f_ms_heap"
  i2f_ms_heap : ∀ {s : @Memory_stack PInf} {t : @Memory_stack PFin}, I2F_Memory_stack s t → I2F_Heap (@Memory_stack_heap PInf s) (@Memory_stack_heap PFin t)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|Build_I2F_Memory_stack"
  Build_I2F_Memory_stack : ∀ (s : @Memory_stack PInf) (t : @Memory_stack PFin),
    I2F_memory (@Memory_stack_memory PInf s) (@Memory_stack_memory PFin t) →
    I2F_Framestack (@Memory_stack_frame_stack PInf s) (@Memory_stack_frame_stack PFin t) →
    I2F_Heap (@Memory_stack_heap PInf s) (@Memory_stack_heap PFin t) →
    I2F_Memory_stack s t

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|i2f_st_ms"
  i2f_st_ms : ∀ {s : @State PInf} {t : @State PFin}, I2F_State s t → I2F_Memory_stack (@state_memory_stack PInf s) (@state_memory_stack PFin t)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|i2f_st_prov"
  i2f_st_prov : ∀ {s : @State PInf} {t : @State PFin}, I2F_State s t → @state_provenance PInf s = @state_provenance PFin t

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|Build_I2F_State"
  Build_I2F_State : ∀ (s : @State PInf) (t : @State PFin),
    I2F_Memory_stack (@state_memory_stack PInf s) (@state_memory_stack PFin t) →
    @state_provenance PInf s = @state_provenance PFin t →
    I2F_State s t
