import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_memory.Intrinsics

open Vellvm.Semantics.DynamicValues Vellvm.Semantics.Implementations.Memory
open Vellvm.Semantics.LLVMEvents Vellvm.Theory.I2F.Refinement
open Vellvm.Theory.I2F.I2F_memS
open Vellvm.Theory.I2F.I2F_exp
open Vellvm.Theory.I2F.I2F_memory

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_memcpy"
  I2F_memcpy : ∀ (s d : PInf.PTR.ptr) (s′ d′ : PFin.PTR.ptr)
    (hs : I2F_Addr s s′) (hd : I2F_Addr d d′) (size : Nat) (vol : Bool),
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@memcpy PInf (@MemoryModelPrimitivesV PInf) s d size vol)
      (@memcpy PFin (@MemoryModelPrimitivesV PFin) s′ d′ size vol)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_memmove"
  I2F_memmove : ∀ (s d : PInf.PTR.ptr) (s′ d′ : PFin.PTR.ptr)
    (hs : I2F_Addr s s′) (hd : I2F_Addr d d′) (size : Nat) (vol : Bool),
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@memmove PInf (@MemoryModelPrimitivesV PInf) s d size vol)
      (@memmove PFin (@MemoryModelPrimitivesV PFin) s′ d′ size vol)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_memset"
  I2F_memset : ∀ (d : PInf.PTR.ptr) (d′ : PFin.PTR.ptr)
    (hd : I2F_Addr d d′) (x : @memory_byte PInf) (y : @memory_byte PFin)
    (h : I2F_memory_byte x y) (size : Nat) (vol : Bool),
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@memset PInf (@MemoryModelPrimitivesV PInf) d x size vol)
      (@memset PFin (@MemoryModelPrimitivesV PFin) d′ y size vol)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_malloc_bytes"
  I2F_malloc_bytes : ∀ (xs : List (@memory_byte PInf)) (ys : List (@memory_byte PFin))
    (h : List.Forall₂ I2F_memory_byte xs ys) (align : Nat),
    I2F_memS I2F_State I2F_Addr
      (@malloc_bytes PInf (@MemoryModelPrimitivesV PInf) xs align)
      (@malloc_bytes PFin (@MemoryModelPrimitivesV PFin) ys align)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_handle_memtransfer"
  I2F_handle_memtransfer : ∀ (overlap : Bool) (xs : List (@dvalue_base PInf)) (ys : List (@dvalue_base PFin))
    (h : List.Forall₂ I2F_dvalue_base xs ys),
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@handle_memtransfer PInf (@MemoryModelPrimitivesV PInf) overlap xs)
      (@handle_memtransfer PFin (@MemoryModelPrimitivesV PFin) overlap ys)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_handle_memcpy"
  I2F_handle_memcpy : ∀ (xs : List (@dvalue_base PInf)) (ys : List (@dvalue_base PFin))
    (h : List.Forall₂ I2F_dvalue_base xs ys),
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@handle_memcpy PInf (@MemoryModelPrimitivesV PInf) xs)
      (@handle_memcpy PFin (@MemoryModelPrimitivesV PFin) ys)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_handle_memmove"
  I2F_handle_memmove : ∀ (xs : List (@dvalue_base PInf)) (ys : List (@dvalue_base PFin))
    (h : List.Forall₂ I2F_dvalue_base xs ys),
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@handle_memmove PInf (@MemoryModelPrimitivesV PInf) xs)
      (@handle_memmove PFin (@MemoryModelPrimitivesV PFin) ys)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_handle_memset"
  I2F_handle_memset : ∀ (xs : List (@dvalue_base PInf)) (ys : List (@dvalue_base PFin))
    (h : List.Forall₂ I2F_dvalue_base xs ys),
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@handle_memset PInf (@MemoryModelPrimitivesV PInf) xs)
      (@handle_memset PFin (@MemoryModelPrimitivesV PFin) ys)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_handle_malloc"
  I2F_handle_malloc : ∀ (xs : List (@dvalue_base PInf)) (ys : List (@dvalue_base PFin))
    (h : List.Forall₂ I2F_dvalue_base xs ys) (align : Nat),
    I2F_memS I2F_State I2F_Addr
      (@handle_malloc PInf (@MemoryModelPrimitivesV PInf) xs align)
      (@handle_malloc PFin (@MemoryModelPrimitivesV PFin) ys align)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_handle_free"
  I2F_handle_free : ∀ (xs : List (@dvalue_base PInf)) (ys : List (@dvalue_base PFin))
    (h : List.Forall₂ I2F_dvalue_base xs ys),
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@handle_free PInf (@MemoryModelPrimitivesV PInf) xs)
      (@handle_free PFin (@MemoryModelPrimitivesV PFin) ys)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_handle_intrinsicM"
  I2F_handle_intrinsicM : ∀ (e : @IntrinsicRequest PInf) (e′ : @IntrinsicRequest PFin)
    (h : I2FE_Intrinsic e e′),
    I2F_memS I2F_State (fun x y ↦ I2FA_Intrinsic e x e′ y)
      (@handle_intrinsicM PInf (@MemoryModelPrimitivesV PInf) e)
      (@handle_intrinsicM PFin (@MemoryModelPrimitivesV PFin) e′)
