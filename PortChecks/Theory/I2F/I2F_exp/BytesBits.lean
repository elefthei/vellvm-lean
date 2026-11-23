import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.BytesBits

open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|in_bounds_case"
  in_bounds_case : ∀ (k : Positive) (x : Int), x ≤ @max_unsigned k → 0 ≤ x → x = unsigned (@repr k x)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|unsigned_inj"
  unsigned_inj : ∀ (sz : Positive) (x y : bit_int sz), unsigned x = unsigned y → x = y

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_memory_byte_to_memory_bits"
  I2F_memory_byte_to_memory_bits : ∀ {b b'}, I2F_memory_byte b b' →
    List.Forall₂ I2F_memory_bit (@memory_byte_to_memory_bits PInf b) (@memory_byte_to_memory_bits PFin b')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_get_bits_of_memory_byte_list"
  I2F_get_bits_of_memory_byte_list : ∀ {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → ∀ n {acc acc'}, List.Forall₂ I2F_memory_bit acc acc' →
    List.Forall₂ I2F_memory_bit (@get_bits_of_memory_byte_list PInf n bs acc) (@get_bits_of_memory_byte_list PFin n bs' acc')
