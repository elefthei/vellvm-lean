import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_memory.Primitives

open Vellvm Vellvm.Semantics.MemoryBytes Vellvm.Semantics.Interfaces.Memory
open Vellvm.Semantics.Implementations.Memory Vellvm.Utils.IntMaps Vellvm.Utils.RelationsUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_exp Vellvm.Theory.I2F.I2F_memS
open Vellvm.Theory.I2F.I2F_memory

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_get_mem"
  I2F_get_mem : I2F_memS I2F_State I2F_memory
    (get_mem (Pa := PInf)) (get_mem (Pa := PFin))

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_get_frame_stack"
  I2F_get_frame_stack : I2F_memS I2F_State I2F_Framestack
    (get_frame_stack (Pa := PInf)) (get_frame_stack (Pa := PFin))

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_get_framestack"
  I2F_get_framestack : I2F_memS I2F_State I2F_Framestack
    (get_framestack (Pa := PInf)) (get_framestack (Pa := PFin))

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_get_frame"
  I2F_get_frame : I2F_memS I2F_State I2F_Frame
    (get_frame (Pa := PInf)) (get_frame (Pa := PFin))

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_get_heap"
  I2F_get_heap : I2F_memS I2F_State I2F_Heap
    (get_heap (Pa := PInf)) (get_heap (Pa := PFin))

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_app_mem_stack"
  I2F_app_mem_stack : ∀ (f1 : @Memory_stack PInf → @Memory_stack PInf) (f2 : @Memory_stack PFin → @Memory_stack PFin),
    (∀ x y, I2F_Memory_stack x y → I2F_Memory_stack (f1 x) (f2 y)) →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (app_mem_stack (Pa := PInf) f1) (app_mem_stack (Pa := PFin) f2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_app_mem"
  I2F_app_mem : ∀ (f1 : @memory PInf → @memory PInf) (f2 : @memory PFin → @memory PFin),
    (∀ x y, I2F_memory x y → I2F_memory (f1 x) (f2 y)) →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (app_mem (Pa := PInf) f1) (app_mem (Pa := PFin) f2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_app_heap"
  I2F_app_heap : ∀ (f1 : @Heap PInf → @Heap PInf) (f2 : @Heap PFin → @Heap PFin),
    (∀ x y, I2F_Heap x y → I2F_Heap (f1 x) (f2 y)) →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (app_heap (Pa := PInf) f1) (app_heap (Pa := PFin) f2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_app_frame_stack"
  I2F_app_frame_stack : ∀ (f1 : @Framestack PInf → @Framestack PInf) (f2 : @Framestack PFin → @Framestack PFin),
    (∀ x y, I2F_Framestack x y → I2F_Framestack (f1 x) (f2 y)) →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (app_frame_stack (Pa := PInf) f1) (app_frame_stack (Pa := PFin) f2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_upd_mem"
  I2F_upd_mem : ∀ m1 m2, I2F_memory m1 m2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (upd_mem (Pa := PInf) m1) (upd_mem (Pa := PFin) m2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_upd_heap"
  I2F_upd_heap : ∀ h1 h2, I2F_Heap h1 h2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (upd_heap (Pa := PInf) h1) (upd_heap (Pa := PFin) h2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_upd_frame_stack"
  I2F_upd_frame_stack : ∀ fs1 fs2, I2F_Framestack fs1 fs2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (upd_frame_stack (Pa := PInf) fs1) (upd_frame_stack (Pa := PFin) fs2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_pop_frame_stack"
  I2F_pop_frame_stack : ∀ fs1 fs2, I2F_Framestack fs1 fs2 →
    I2F_EOU I2F_Framestack (pop_frame_stack (Pa := PInf) fs1) (pop_frame_stack (Pa := PFin) fs2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_app_frame_stack_eob"
  I2F_app_frame_stack_eob : I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (app_frame_stack_eob (Pa := PInf) (pop_frame_stack (Pa := PInf))) (app_frame_stack_eob (Pa := PFin) (pop_frame_stack (Pa := PFin)))

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_read_byte_raw"
  I2F_read_byte_raw : ∀ (msg : IRString) (addr : Int), I2F_memS I2F_State I2F_byte
    (read_byte_raw (Pa := PInf) msg addr) (read_byte_raw (Pa := PFin) msg addr)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_set_byte_raw"
  I2F_set_byte_raw : ∀ addr b1 b2, I2F_byte b1 b2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (set_byte_raw (Pa := PInf) addr b1) (set_byte_raw (Pa := PFin) addr b2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_Read_byte"
  I2F_Read_byte : ∀ (p1 : PInf.PTR.ptr) (p2 : PFin.PTR.ptr), I2F_Addr p1 p2 →
    I2F_memS I2F_State I2F_memory_byte
    (Read_byte (Pa := PInf) p1) (Read_byte (Pa := PFin) p2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_Write_byte"
  I2F_Write_byte : ∀ (p1 : PInf.PTR.ptr) (p2 : PFin.PTR.ptr), I2F_Addr p1 p2 →
    ∀ b1 b2, I2F_memory_byte b1 b2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (Write_byte (Pa := PInf) p1 b1) (Write_byte (Pa := PFin) p2 b2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_get_free_block"
  I2F_get_free_block : ∀ (size align : Nat) (pr : PInf.PROV.provenance),
    I2F_memS I2F_State (prod_rel I2F_Addr (List.Forall₂ I2F_Addr))
    (get_free_block (Pa := PInf) size align pr) (get_free_block (Pa := PFin) size align pr)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_memory_bytes_to_bytes"
  I2F_memory_bytes_to_bytes : ∀ (aid : PInf.PROV.allocationId) (bytes1 : List (@memory_byte PInf)) (bytes2 : List (@memory_byte PFin)),
    List.Forall₂ I2F_memory_byte bytes1 bytes2 → List.Forall₂ I2F_byte
    (memory_bytes_to_bytes (Pa := PInf) aid bytes1) (memory_bytes_to_bytes (Pa := PFin) aid bytes2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_add_block"
  I2F_add_block : ∀ (aid : PInf.PROV.allocationId) (p1 : PInf.PTR.ptr) (p2 : PFin.PTR.ptr), I2F_Addr p1 p2 →
    ∀ (ptrs1 : List PInf.PTR.ptr) (ptrs2 : List PFin.PTR.ptr)
      (bytes1 : List (@memory_byte PInf)) (bytes2 : List (@memory_byte PFin)), List.Forall₂ I2F_memory_byte bytes1 bytes2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (add_block (Pa := PInf) aid p1 ptrs1 bytes1) (add_block (Pa := PFin) aid p2 ptrs2 bytes2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_add_ptrs_to_frame"
  I2F_add_ptrs_to_frame : ∀ (ptrs1 : List PInf.PTR.ptr) (ptrs2 : List PFin.PTR.ptr),
    List.Forall₂ I2F_Addr ptrs1 ptrs2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (add_ptrs_to_frame (Pa := PInf) ptrs1) (add_ptrs_to_frame (Pa := PFin) ptrs2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_add_ptrs_to_heap"
  I2F_add_ptrs_to_heap : ∀ (ptrs1 : List PInf.PTR.ptr) (ptrs2 : List PFin.PTR.ptr),
    List.Forall₂ I2F_Addr ptrs1 ptrs2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (add_ptrs_to_heap (Pa := PInf) ptrs1) (add_ptrs_to_heap (Pa := PFin) ptrs2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_add_block_to_stack"
  I2F_add_block_to_stack : ∀ (aid : PInf.PROV.allocationId) (p1 : PInf.PTR.ptr) (p2 : PFin.PTR.ptr), I2F_Addr p1 p2 →
    ∀ (ptrs1 : List PInf.PTR.ptr) (ptrs2 : List PFin.PTR.ptr), List.Forall₂ I2F_Addr ptrs1 ptrs2 →
    ∀ (bytes1 : List (@memory_byte PInf)) (bytes2 : List (@memory_byte PFin)), List.Forall₂ I2F_memory_byte bytes1 bytes2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (add_block_to_stack (Pa := PInf) aid p1 ptrs1 bytes1) (add_block_to_stack (Pa := PFin) aid p2 ptrs2 bytes2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_add_block_to_heap"
  I2F_add_block_to_heap : ∀ (aid : PInf.PROV.allocationId) (p1 : PInf.PTR.ptr) (p2 : PFin.PTR.ptr), I2F_Addr p1 p2 →
    ∀ (ptrs1 : List PInf.PTR.ptr) (ptrs2 : List PFin.PTR.ptr), List.Forall₂ I2F_Addr ptrs1 ptrs2 →
    ∀ (bytes1 : List (@memory_byte PInf)) (bytes2 : List (@memory_byte PFin)), List.Forall₂ I2F_memory_byte bytes1 bytes2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (add_block_to_heap (Pa := PInf) aid p1 ptrs1 bytes1) (add_block_to_heap (Pa := PFin) aid p2 ptrs2 bytes2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_Allocate_bytes_with_pr"
  I2F_Allocate_bytes_with_pr : ∀ (bytes1 : List (@memory_byte PInf)) (bytes2 : List (@memory_byte PFin)),
    List.Forall₂ I2F_memory_byte bytes1 bytes2 → ∀ (align : Nat) (pr : PInf.PROV.provenance),
    I2F_memS I2F_State I2F_Addr
    (Allocate_bytes_with_pr (Pa := PInf) bytes1 align pr) (Allocate_bytes_with_pr (Pa := PFin) bytes2 align pr)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_Malloc_bytes_with_pr"
  I2F_Malloc_bytes_with_pr : ∀ (bytes1 : List (@memory_byte PInf)) (bytes2 : List (@memory_byte PFin)),
    List.Forall₂ I2F_memory_byte bytes1 bytes2 → ∀ (align : Nat) (pr : PInf.PROV.provenance),
    I2F_memS I2F_State I2F_Addr
    (Malloc_bytes_with_pr (Pa := PInf) bytes1 align pr) (Malloc_bytes_with_pr (Pa := PFin) bytes2 align pr)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_push_frame_stack"
  I2F_push_frame_stack : ∀ (f1 : @Frame PInf) (f2 : @Frame PFin), I2F_Frame f1 f2 →
    ∀ fs1 fs2, I2F_Framestack fs1 fs2 →
    I2F_Framestack (push_frame_stack (Pa := PInf) f1 fs1) (push_frame_stack (Pa := PFin) f2 fs2)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_Mempush"
  I2F_Mempush : I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (Mempush (Pa := PInf)) (Mempush (Pa := PFin))

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_Mempop"
  I2F_Mempop : I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (Mempop (Pa := PInf)) (Mempop (Pa := PFin))

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_Free"
  I2F_Free : ∀ (p1 : PInf.PTR.ptr) (p2 : PFin.PTR.ptr), I2F_Addr p1 p2 →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
    (Free (Pa := PInf) p1) (Free (Pa := PFin) p2)
