import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_memory.Transfers

open Vellvm.Semantics.Implementations.Memory Vellvm.Semantics.MemoryBytes
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_memS Vellvm.Theory.I2F.I2F_exp
open Vellvm.Theory.I2F.I2F_memory

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_read_bytes"
  Vellvm.Theory.I2F.I2F_memory.I2F_read_bytes : ∀ (p : PInf.PTR.ptr) (q : PFin.PTR.ptr),
    I2F_Addr p q → ∀ n : Nat, I2F_memS I2F_State (List.Forall₂ I2F_memory_byte)
      (@read_bytes PInf (@MemoryModelPrimitivesV PInf) p n)
      (@read_bytes PFin (@MemoryModelPrimitivesV PFin) q n)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_write_bytes"
  Vellvm.Theory.I2F.I2F_memory.I2F_write_bytes : ∀ (p : PInf.PTR.ptr) (q : PFin.PTR.ptr),
    I2F_Addr p q → ∀ (xs : List (@memory_byte PInf)) (ys : List (@memory_byte PFin)),
    List.Forall₂ I2F_memory_byte xs ys → I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@write_bytes PInf (@MemoryModelPrimitivesV PInf) p xs)
      (@write_bytes PFin (@MemoryModelPrimitivesV PFin) q ys)
