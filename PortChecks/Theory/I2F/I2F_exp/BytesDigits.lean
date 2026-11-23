import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.BytesDigits

open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u v
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_absorb_pois"
  I2F_absorb_pois : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (c : EOUP A) (d : EOUP B)
    (f : A → EOU (@dvalue_base PInf)) (g : B → EOU (@dvalue_base PFin)), I2F_EOUP R c d →
    (∀ a b, R a b → I2F_EOU I2F_dvalue_base (f a) (g b)) →
    I2F_EOU I2F_dvalue_base (@absorb_pois PInf A c f) (@absorb_pois PFin B d g)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_memory_bit_to_bit"
  I2F_memory_bit_to_bit : ∀ {b b'}, I2F_memory_bit b b' → I2F_EOUP Eq (@memory_bit_to_bit PInf  b) (@memory_bit_to_bit PFin  b')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_memory_bits_to_Z"
  I2F_memory_bits_to_Z : ∀ {bs bs'}, List.Forall₂ I2F_memory_bit bs bs' → I2F_EOUP Eq (@memory_bits_to_Z PInf  bs) (@memory_bits_to_Z PFin  bs')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_memory_byte_to_Z"
  I2F_memory_byte_to_Z : ∀ {b b'}, I2F_memory_byte b b' → I2F_EOUP Eq (@memory_byte_to_Z PInf  b) (@memory_byte_to_Z PFin  b')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_concat_bytes_Z_mixed"
  I2F_concat_bytes_Z_mixed : ∀ n {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → I2F_EOUP Eq (@concat_bytes_Z_mixed PInf n bs) (@concat_bytes_Z_mixed PFin n bs')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_memory_bytes_to_int"
  I2F_memory_bytes_to_int : ∀ sz {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → I2F_EOUP Eq (@memory_bytes_to_int PInf sz bs) (@memory_bytes_to_int PFin sz bs')
