import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.BytesByteValue

open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_mixed_fallback"
  I2F_mixed_fallback : ∀ (sz : Positive) {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_dvalue_bv
    (@BYTE_Mixed PInf sz (@get_bits_of_memory_byte_list PInf sz.val bs []).reverse) (@BYTE_Mixed PFin sz (@get_bits_of_memory_byte_list PFin sz.val cs []).reverse)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_existsb_ptr_bits"
  I2F_existsb_ptr_bits : ∀ (sz : Positive) {bs cs}, List.Forall₂ I2F_memory_byte bs cs → 
    (@get_bits_of_memory_byte_list PInf sz.val bs []).reverse.any (@is_ptr_bit PInf) =
    (@get_bits_of_memory_byte_list PFin sz.val cs []).reverse.any (@is_ptr_bit PFin)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_memory_bytes_to_bits_value"
  I2F_memory_bytes_to_bits_value : ∀ (sz : Positive) {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_dvalue_bv
    (@memory_bytes_to_bits_value PInf sz bs) (@memory_bytes_to_bits_value PFin sz cs)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_memory_bytes_to_byte_value"
  I2F_memory_bytes_to_byte_value : ∀ (sz : Positive) {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_EOU I2F_dvalue_bv
    (@memory_bytes_to_byte_value PInf sz bs) (@memory_bytes_to_byte_value PFin sz cs)
