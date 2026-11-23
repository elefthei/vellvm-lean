import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.BytesWriterBase

open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_store_size_dtyp"
  I2F_store_size_dtyp : ∀ t, @store_size_dtyp PInf.SIZE t = @store_size_dtyp PFin.SIZE t

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_dtyp_alignment"
  I2F_dtyp_alignment : ∀ t, @dtyp_alignment PInf.SIZE t = @dtyp_alignment PFin.SIZE t

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_alloc_size_dtyp"
  I2F_alloc_size_dtyp : ∀ t, @alloc_size_dtyp PInf.SIZE t = @alloc_size_dtyp PFin.SIZE t

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_max_alignment"
  I2F_max_alignment : ∀ t, @max_preferred_dtyp_alignment PInf.SIZE t = @max_preferred_dtyp_alignment PFin.SIZE t

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_memory_byte_of_dvalue_bv"
  I2F_memory_byte_of_dvalue_bv : ∀ {sz} {b b'} i, @I2F_dvalue_bv sz b b' → I2F_memory_byte
    (@memory_byte_of_dvalue_bv PInf sz b i) (@memory_byte_of_dvalue_bv PFin sz b' i)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_poison_memory_byte"
  I2F_poison_memory_byte : I2F_memory_byte (@poison_memory_byte PInf) (@poison_memory_byte PFin)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_ser_state"
  I2F_ser_state : (Nat × List (@memory_byte PInf)) → (Nat × List (@memory_byte PFin)) → Prop

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_accumulate_poison_bytes"
  I2F_accumulate_poison_bytes : ∀ n {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → List.Forall₂ I2F_memory_byte (@accumulate_poison_bytes PInf n bs) (@accumulate_poison_bytes PFin n bs')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_accumulate_padding_bytes"
  I2F_accumulate_padding_bytes : ∀ o n {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → I2F_ser_state (@accumulate_padding_bytes PInf o n bs) (@accumulate_padding_bytes PFin o n bs')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_accumulate_padding"
  I2F_accumulate_padding : ∀ o ta {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → I2F_ser_state (@accumulate_padding PInf o ta bs) (@accumulate_padding PFin o ta bs')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_acc_memory_bytes_of_dvalue_base"
  I2F_acc_memory_bytes_of_dvalue_base : ∀ t {b c}, I2F_dvalue_base b c → ∀ o {xs ys}, List.Forall₂ I2F_memory_byte xs ys →
    I2F_ser_state (@acc_memory_bytes_of_dvalue_base PInf t b o xs) (@acc_memory_bytes_of_dvalue_base PFin t c o ys)
