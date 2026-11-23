import PortChecks.Theory.I2F.I2F_memory.Transfers
import Vellvm.Theory.I2F.I2F_memory.Derived

open Vellvm Vellvm.Semantics Vellvm.Theory.I2F
open Syntax.DynamicTypes Syntax.LLVMAst DynamicValues MemoryBytes LLVMEvents
open Implementations.Memory Refinement I2F_exp I2F_memS I2F_memory

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_read_dvalue"
  Vellvm.Theory.I2F.I2F_memory.I2F_read_dvalue : ∀ (p : PInf.PTR.ptr) (q : PFin.PTR.ptr),
    I2F_Addr p q → ∀ t : dtyp, I2F_memS I2F_State I2F_dvalue
      (@read_dvalue PInf (@MemoryModelPrimitivesV PInf) t p)
      (@read_dvalue PFin (@MemoryModelPrimitivesV PFin) t q)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_write_dvalue"
  Vellvm.Theory.I2F.I2F_memory.I2F_write_dvalue : ∀ (p : PInf.PTR.ptr) (q : PFin.PTR.ptr),
    I2F_Addr p q → ∀ (t : dtyp) (v : @dvalue PInf) (w : @dvalue PFin), I2F_dvalue v w →
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@write_dvalue PInf (@MemoryModelPrimitivesV PInf) p t v)
      (@write_dvalue PFin (@MemoryModelPrimitivesV PFin) q t w)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_allocate_bytes"
  Vellvm.Theory.I2F.I2F_memory.I2F_allocate_bytes :
    ∀ (xs : List (@memory_byte PInf)) (ys : List (@memory_byte PFin)),
    List.Forall₂ I2F_memory_byte xs ys → ∀ align : Nat, I2F_memS I2F_State I2F_Addr
      (@allocate_bytes PInf (@MemoryModelPrimitivesV PInf) xs align)
      (@allocate_bytes PFin (@MemoryModelPrimitivesV PFin) ys align)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_allocate_dtyp"
  Vellvm.Theory.I2F.I2F_memory.I2F_allocate_dtyp : ∀ (t : dtyp) (n align : Nat),
    I2F_memS I2F_State I2F_Addr (@allocate_dtyp PInf (@MemoryModelPrimitivesV PInf) t n align)
      (@allocate_dtyp PFin (@MemoryModelPrimitivesV PFin) t n align)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_assert_inttoptr_types_ok"
  Vellvm.Theory.I2F.I2F_memory.I2F_assert_inttoptr_types_ok : ∀ t u : dtyp_base,
    I2F_memS I2F_State (fun (_ _ : Unit) ↦ True)
      (@assert_inttoptr_types_ok PInf (@MemoryModelPrimitivesV PInf) t u)
      (@assert_inttoptr_types_ok PFin (@MemoryModelPrimitivesV PFin) t u)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_convert_impure_base"
  Vellvm.Theory.I2F.I2F_memory.I2F_convert_impure_base : ∀ (c : impure_conversion) (t u : dtyp_base)
    (v : @dvalue_base PInf) (w : @dvalue_base PFin), I2F_dvalue_base v w →
    I2F_memS I2F_State I2F_dvalue_base (@convert_impure_base PInf (@MemoryModelPrimitivesV PInf) c t v u)
      (@convert_impure_base PFin (@MemoryModelPrimitivesV PFin) c t w u)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_convert_impure"
  Vellvm.Theory.I2F.I2F_memory.I2F_convert_impure : ∀ (c : impure_conversion) (t u : dtyp)
    (v : @dvalue PInf) (w : @dvalue PFin), I2F_dvalue v w → I2F_memS I2F_State I2F_dvalue
      (@convert_impure PInf (@MemoryModelPrimitivesV PInf) c t v u)
      (@convert_impure PFin (@MemoryModelPrimitivesV PFin) c t w u)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_handle_memoryM"
  Vellvm.Theory.I2F.I2F_memory.I2F_handle_memoryM : ∀ (e : (@MemoryE PInf).I) (f : (@MemoryE PFin).I),
    I2FE_Memory e f → I2F_memS I2F_State
      (fun (a : (@MemoryE PInf).O e) (b : (@MemoryE PFin).O f) ↦ I2FA_Memory e a f b)
      (@handle_memoryM PInf (@MemoryModelPrimitivesV PInf) e)
      (@handle_memoryM PFin (@MemoryModelPrimitivesV PFin) f)
