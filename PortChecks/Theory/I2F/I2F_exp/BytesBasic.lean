import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.BytesBasic

open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_is_poison_bit"
  I2F_is_poison_bit : ∀ {b b'}, I2F_memory_bit b b' → @is_poison_bit PInf b = @is_poison_bit PFin b'

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_all_poison_bits"
  I2F_all_poison_bits : ∀ {bs bs'}, List.Forall₂ I2F_memory_bit bs bs' → @all_poison_bits PInf bs = @all_poison_bits PFin bs'

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_is_all_poison_byte"
  I2F_is_all_poison_byte : ∀ {b b'}, I2F_memory_byte b b' → @is_all_poison_byte PInf b = @is_all_poison_byte PFin b'

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_poison_split"
  I2F_poison_split : ∀ {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' →
    (@poison_split PInf bs).1 = (@poison_split PFin bs').1 ∧
    List.Forall₂ I2F_memory_byte (@poison_split PInf bs).2 (@poison_split PFin bs').2

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_all_poison_bytes"
  I2F_all_poison_bytes : ∀ {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → @all_poison_bytes PInf bs = @all_poison_bytes PFin bs'

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_is_ptr_bit"
  I2F_is_ptr_bit : ∀ {b b'}, I2F_memory_bit b b' → @is_ptr_bit PInf b = @is_ptr_bit PFin b'
