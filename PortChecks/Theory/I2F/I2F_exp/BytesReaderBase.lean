import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.BytesReaderBase

open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_packed_bits_to_dvalue"
  I2F_packed_bits_to_dvalue : ∀ t m {bs cs}, List.Forall₂ I2F_memory_bit bs cs → I2F_dvalue (@packed_bits_to_dvalue PInf t m bs) (@packed_bits_to_dvalue PFin t m cs)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_packed_bits_to_elts"
  I2F_packed_bits_to_elts : ∀ t m n {bs cs}, List.Forall₂ I2F_memory_bit bs cs → List.Forall₂ I2F_dvalue (@packed_bits_to_elts PInf t m n bs) (@packed_bits_to_elts PFin t m n cs)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_packed_vector_elts"
  I2F_packed_vector_elts : ∀ t m n {bs cs}, List.Forall₂ I2F_memory_byte bs cs → List.Forall₂ I2F_dvalue (@Theory.MemoryBytesFacts.packed_vector_elts PInf t m n bs) (@Theory.MemoryBytesFacts.packed_vector_elts PFin t m n cs)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_memory_bytes_to_dvalue_base"
  I2F_memory_bytes_to_dvalue_base : ∀ t {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_EOU I2F_dvalue_base (@memory_bytes_to_dvalue_base PInf bs t) (@memory_bytes_to_dvalue_base PFin cs t)
