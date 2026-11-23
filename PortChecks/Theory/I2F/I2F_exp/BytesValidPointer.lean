import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.BytesValidPointer

open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_EOUP_valid_pointer_bits"
  I2F_EOUP_valid_pointer_bits : ∀ {p p'} base off {bs bs'}, I2F_Addr p p' → List.Forall₂ I2F_memory_bit bs bs' →
    I2F_EOUP Eq (@valid_pointer_bits PInf p base off bs) (@valid_pointer_bits PFin p' base off bs')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_EOUP_valid_pointer_byte"
  I2F_EOUP_valid_pointer_byte : ∀ {p p'} i {bs bs'}, I2F_Addr p p' → I2F_memory_byte bs bs' →
    I2F_EOUP Eq (@valid_pointer_byte PInf p i bs) (@valid_pointer_byte PFin p' i bs')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_EOUP_valid_pointer_bytes"
  I2F_EOUP_valid_pointer_bytes : ∀ {p p'} i {bs bs'}, I2F_Addr p p' → List.Forall₂ I2F_memory_byte bs bs' →
    I2F_EOUP Eq (@valid_pointer_bytes PInf p i bs) (@valid_pointer_bytes PFin p' i bs')
