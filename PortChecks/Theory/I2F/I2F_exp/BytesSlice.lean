import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.BytesSlice

open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_pointer_byte_at"
  I2F_pointer_byte_at : ∀ {p q} i {b c}, I2F_Addr p q → I2F_memory_byte b c → @pointer_byte_at PInf p i b = @pointer_byte_at PFin q i c

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_pointer_slice_from"
  I2F_pointer_slice_from : ∀ {p q bs cs}, I2F_Addr p q → List.Forall₂ I2F_memory_byte bs cs → ∀ i,
    @pointer_slice_from PInf p i bs = @pointer_slice_from PFin q i cs

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_memory_bytes_to_pointer_slice"
  I2F_memory_bytes_to_pointer_slice : ∀ {bs cs}, List.Forall₂ I2F_memory_byte bs cs →
    match @memory_bytes_to_pointer_slice PInf bs, @memory_bytes_to_pointer_slice PFin cs with
    | none, none => True
    | some (p,i), some (q,j) => I2F_Addr p q ∧ i = j
    | _, _ => False

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_EOUP_memory_bytes_to_pointer"
  I2F_EOUP_memory_bytes_to_pointer : ∀ {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_EOUP I2F_Addr (@memory_bytes_to_pointer PInf bs) (@memory_bytes_to_pointer PFin cs)
