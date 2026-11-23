import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.BytesPack

open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_dvalue_bv_all_poison"
  I2F_dvalue_bv_all_poison : ∀ {sz} {b b'}, @I2F_dvalue_bv sz b b' → @dvalue_bv_all_poison PInf sz b = @dvalue_bv_all_poison PFin sz b'

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_memory_byte_of_bits"
  I2F_memory_byte_of_bits : ∀ {bs cs}, List.Forall₂ I2F_memory_bit bs cs → I2F_memory_byte (@memory_byte_of_bits PInf bs) (@memory_byte_of_bits PFin cs)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_acc_bits_to_memory_bytes"
  I2F_acc_bits_to_memory_bytes : ∀ n {bs cs xs ys}, List.Forall₂ I2F_memory_bit bs cs → List.Forall₂ I2F_memory_byte xs ys →
    List.Forall₂ I2F_memory_byte (@acc_bits_to_memory_bytes PInf n bs xs) (@acc_bits_to_memory_bytes PFin n cs ys)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_acc_packed_bits_to_memory_bytes"
  I2F_acc_packed_bits_to_memory_bytes : ∀ n {bs cs xs ys}, List.Forall₂ I2F_memory_bit bs cs → List.Forall₂ I2F_memory_byte xs ys →
    List.Forall₂ I2F_memory_byte (@acc_packed_bits_to_memory_bytes PInf n bs xs) (@acc_packed_bits_to_memory_bytes PFin n cs ys)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_packed_elt_bits"
  I2F_packed_elt_bits : ∀ m {x y}, I2F_dvalue x y → I2F_EOU (List.Forall₂ I2F_memory_bit) (@packed_elt_bits PInf m x) (@packed_elt_bits PFin m y)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_packed_vector_bytes"
  I2F_packed_vector_bytes : ∀ m t {xs ys} o ta {bs cs}, List.Forall₂ I2F_dvalue xs ys → List.Forall₂ I2F_memory_byte bs cs →
    I2F_EOU I2F_ser_state (@writePacked PInf m t xs o ta bs) (@writePacked PFin m t ys o ta cs)
