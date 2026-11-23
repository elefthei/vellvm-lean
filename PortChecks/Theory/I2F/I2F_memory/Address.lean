import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_memory.Address

open Vellvm Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_exp Vellvm.Theory.I2F.I2F_memory
open Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.Interfaces.Pointer Vellvm.Semantics.Interfaces.IPtr
open Vellvm.Semantics.Implementations.Memory Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues
open Vellvm.Syntax.DynamicTypes

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_Addr_ptr_to_int"
  I2F_Addr_ptr_to_int : ∀ (p : PInf.PTR.ptr) (q : PFin.PTR.ptr), I2F_Addr p q →
    PInf.P2I.ptr_to_int p = PFin.P2I.ptr_to_int q

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_intptr_seq"
  I2F_intptr_seq : ∀ start size : Nat, I2F_EOU (List.Forall₂ I2F_Iptr)
    (@intptr_seq PInf.IPTR start size) (@intptr_seq PFin.IPTR start size)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_ptr_byte_offset"
  I2F_ptr_byte_offset : ∀ p q i j, I2F_Addr p q → I2F_Iptr i j →
    I2F_EOU I2F_Addr (@ptr_byte_offset PInf p i) (@ptr_byte_offset PFin q j)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_get_consecutive_ptrs"
  I2F_get_consecutive_ptrs : ∀ p q, I2F_Addr p q → ∀ n : Nat, I2F_EOU (List.Forall₂ I2F_Addr)
    (@get_consecutive_ptrs PInf p n) (@get_consecutive_ptrs PFin q n)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_coerce_integer_to_int"
  I2F_coerce_integer_to_int : ∀ (b : Option Positive) (z : Int), I2F_EOU I2F_dvalue_base
    (@coerce_integer_to_int PInf b z) (@coerce_integer_to_int PFin b z)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_no_overlap"
  I2F_no_overlap : ∀ (a b : PInf.PTR.ptr) (n : Nat) (a' b' : PFin.PTR.ptr) (m : Nat),
    I2F_Addr a a' → I2F_Addr b b' →
    @no_overlap _ _ (@overlaps_ptoi _ _ PInf.P2I) a n b m =
      @no_overlap _ _ (@overlaps_ptoi _ _ PFin.P2I) a' n b' m

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|generate_num_poison_bytes_h_0"
  generate_num_poison_bytes_h_0 : ∀ {Pa : Params} (start : Nat),
    @generate_num_poison_bytes_h Pa start 0 = []

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|generate_num_poison_bytes_h_succ"
  generate_num_poison_bytes_h_succ : ∀ {Pa : Params} (start num : Nat),
    @generate_num_poison_bytes_h Pa start num.succ =
      @poison_memory_byte Pa :: @generate_num_poison_bytes_h Pa start.succ num

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_generate_num_poison_bytes_h"
  I2F_generate_num_poison_bytes_h : ∀ start num : Nat, List.Forall₂ I2F_memory_byte
    (@generate_num_poison_bytes_h PInf start num) (@generate_num_poison_bytes_h PFin start num)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_generate_num_poison_bytes"
  I2F_generate_num_poison_bytes : ∀ num : Nat, List.Forall₂ I2F_memory_byte
    (@generate_num_poison_bytes PInf num) (@generate_num_poison_bytes PFin num)

#source_check "src/rocq/Theory/I2F/I2F_memory.v|Vellvm.Theory.I2F.I2F_memory|I2F_generate_poison_bytes"
  I2F_generate_poison_bytes : ∀ dt : dtyp, List.Forall₂ I2F_memory_byte
    (@generate_poison_bytes PInf dt) (@generate_poison_bytes PFin dt)
