import PortChecks.SourceType
import Vellvm.Theory.I2F.Refinement.Values

open Vellvm Vellvm.Numeric.Integers Vellvm.Semantics.DynamicValues
open Vellvm.Semantics.Interfaces.Pointer Vellvm.Syntax.DynamicTypes
open Vellvm.Theory.I2F.Refinement

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_Iptr"
  I2F_Iptr : PInf.IPTR.iptr → PFin.IPTR.iptr → Prop

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_Addr"
  I2F_Addr : PInf.PTR.ptr → PFin.PTR.ptr → Prop

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_Addr_ptr_aligned_to"
  I2F_Addr_ptr_aligned_to : ∀ (p : PInf.PTR.ptr) (q : PFin.PTR.ptr) (align : Nat),
    I2F_Addr p q → @ptr_aligned_to PInf.PROV PInf.PTR PInf.P2I p align =
      @ptr_aligned_to PFin.PROV PFin.PTR PFin.P2I q align

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_memory_bit"
  I2F_memory_bit : @memory_bit PInf → @memory_bit PFin → Prop

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_Bit_ptr"
  I2F_Bit_ptr : ∀ p q i, I2F_Addr p q → I2F_memory_bit (@Bit_ptr PInf p i) (@Bit_ptr PFin q i)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_Bit_psn"
  I2F_Bit_psn : I2F_memory_bit (@Bit_psn PInf) (@Bit_psn PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_Bit_bit"
  I2F_Bit_bit : ∀ b, I2F_memory_bit (@Bit_bit PInf b) (@Bit_bit PFin b)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_dvalue_bv"
  I2F_dvalue_bv : ∀ {sz : Positive}, @dvalue_bv PInf sz → @dvalue_bv PFin sz → Prop

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_BYTE_I"
  I2F_BYTE_I : ∀ {sz : Positive} (i : bit_int sz),
    I2F_dvalue_bv (@BYTE_I PInf sz i) (@BYTE_I PFin sz i)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_BYTE_Pointer"
  I2F_BYTE_Pointer : ∀ {sz : Positive} p q n, I2F_Addr p q →
    I2F_dvalue_bv (@BYTE_Pointer PInf sz p n) (@BYTE_Pointer PFin sz q n)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_BYTE_Mixed"
  I2F_BYTE_Mixed : ∀ {sz : Positive} {xs ys}, List.Forall₂ I2F_memory_bit xs ys →
    I2F_dvalue_bv (@BYTE_Mixed PInf sz xs) (@BYTE_Mixed PFin sz ys)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_dvalue_base"
  I2F_dvalue_base : @dvalue_base PInf → @dvalue_base PFin → Prop

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_dvalue_Pointer"
  I2F_dvalue_Pointer : ∀ p q, I2F_Addr p q →
    I2F_dvalue_base (@DVALUE_Pointer PInf p) (@DVALUE_Pointer PFin q)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_dvalue_Int"
  I2F_dvalue_Int : ∀ {sz} (i : bit_int sz),
    I2F_dvalue_base (@DVALUE_I PInf sz i) (@DVALUE_I PFin sz i)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_dvalue_Ptr"
  I2F_dvalue_Ptr : ∀ {p q}, I2F_Iptr p q →
    I2F_dvalue_base (@DVALUE_Iptr PInf p) (@DVALUE_Iptr PFin q)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_dvalue_Double"
  I2F_dvalue_Double : ∀ d, I2F_dvalue_base (@DVALUE_Double PInf d) (@DVALUE_Double PFin d)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_dvalue_Float"
  I2F_dvalue_Float : ∀ f, I2F_dvalue_base (@DVALUE_Float PInf f) (@DVALUE_Float PFin f)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_dvalue_Poison"
  I2F_dvalue_Poison : I2F_dvalue_base (@DVALUE_Poison PInf) (@DVALUE_Poison PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_dvalue_None"
  I2F_dvalue_None : I2F_dvalue_base (@DVALUE_None PInf) (@DVALUE_None PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_dvalue_B"
  I2F_dvalue_B : ∀ {sz} {x : @dvalue_bv PInf sz} {y : @dvalue_bv PFin sz},
    I2F_dvalue_bv x y → I2F_dvalue_base (@DVALUE_B PInf sz x) (@DVALUE_B PFin sz y)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_dvalue"
  I2F_dvalue : @dvalue PInf → @dvalue PFin → Prop

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_dvalue_Base"
  I2F_dvalue_Base : ∀ {b b'}, I2F_dvalue_base b b' →
    I2F_dvalue (@DVALUE_Base PInf b) (@DVALUE_Base PFin b')

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_dvalue_Struct"
  I2F_dvalue_Struct : ∀ p {xs ys}, List.Forall₂ I2F_dvalue xs ys →
    I2F_dvalue (@DVALUE_Struct PInf p xs) (@DVALUE_Struct PFin p ys)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_dvalue_Array"
  I2F_dvalue_Array : ∀ v {xs ys}, List.Forall₂ I2F_dvalue xs ys →
    I2F_dvalue (@DVALUE_Array PInf v xs) (@DVALUE_Array PFin v ys)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_dvalue_ind"
  I2F_dvalue_ind : ∀ {P : @dvalue PInf → @dvalue PFin → Prop},
    (∀ b b', I2F_dvalue_base b b' → P (@DVALUE_Base PInf b) (@DVALUE_Base PFin b')) →
    (∀ p xs ys, List.Forall₂ I2F_dvalue xs ys → List.Forall₂ P xs ys →
      P (@DVALUE_Struct PInf p xs) (@DVALUE_Struct PFin p ys)) →
    (∀ v xs ys, List.Forall₂ I2F_dvalue xs ys → List.Forall₂ P xs ys →
      P (@DVALUE_Array PInf v xs) (@DVALUE_Array PFin v ys)) →
    ∀ {x y}, I2F_dvalue x y → P x y

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_targs"
  I2F_targs : List (dtyp × @dvalue PInf) → List (dtyp × @dvalue PFin) → Prop

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_targs_fst"
  I2F_targs_fst : ∀ {xs ys}, I2F_targs xs ys → List.map Prod.fst xs = List.map Prod.fst ys

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_targs_snd"
  I2F_targs_snd : ∀ {xs ys}, I2F_targs xs ys →
    List.Forall₂ I2F_dvalue (List.map Prod.snd xs) (List.map Prod.snd ys)
