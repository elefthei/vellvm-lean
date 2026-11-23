import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_memory.Maps

open Vellvm.Semantics.Implementations.Memory Vellvm.Theory.I2F.Refinement
open Vellvm.Theory.I2F.I2F_memory Vellvm.Semantics.Handlers.Memory

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_next_key_with_alignment"
  I2F_next_key_with_alignment : ∀ m n, I2F_memory m n → ∀ align, next_key_with_alignment m align = next_key_with_alignment n align

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_free_frame_memory"
  I2F_free_frame_memory : ∀ f g, I2F_Frame f g → ∀ m n, I2F_memory m n →
    I2F_memory (@free_frame_memory PInf f m) (@free_frame_memory PFin g n)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_free_block_memory"
  I2F_free_block_memory : ∀ f g, List.Forall₂ I2F_Addr f g → ∀ m n, I2F_memory m n →
    I2F_memory (@free_block_memory PInf f m) (@free_block_memory PFin g n)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_add_to_frame"
  I2F_add_to_frame : ∀ m n, I2F_Memory_stack m n → ∀ p q, I2F_Addr p q →
    I2F_Memory_stack (@add_to_frame PInf m p) (@add_to_frame PFin n q)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_add_all_to_frame"
  I2F_add_all_to_frame : ∀ ps qs, List.Forall₂ I2F_Addr ps qs → ∀ m n, I2F_Memory_stack m n →
    I2F_Memory_stack (@add_all_to_frame PInf ps m) (@add_all_to_frame PFin qs n)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_add_to_heap"
  I2F_add_to_heap : ∀ m n, I2F_Memory_stack m n → ∀ r s, I2F_Addr r s → ∀ p q, I2F_Addr p q →
    I2F_Memory_stack (@add_to_heap PInf m r p) (@add_to_heap PFin n s q)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_add_all_to_heap'"
  I2F_add_all_to_heap' : ∀ m n, I2F_Memory_stack m n → ∀ r s, I2F_Addr r s →
    ∀ ps qs, List.Forall₂ I2F_Addr ps qs →
    I2F_Memory_stack (@add_all_to_heap' PInf m r ps) (@add_all_to_heap' PFin n s qs)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_add_all_to_heap"
  I2F_add_all_to_heap : ∀ ps qs, List.Forall₂ I2F_Addr ps qs → ∀ m n, I2F_Memory_stack m n →
    I2F_Memory_stack (@add_all_to_heap PInf ps m) (@add_all_to_heap PFin qs n)
