import PortChecks.SourceType
import Vellvm.Semantics.Operations.Gep

open Vellvm Vellvm.Syntax.LLVMAst Vellvm.Syntax.DynamicTypes Vellvm.Semantics.DynamicValues
open Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.Interfaces.Sizeof Vellvm.Semantics.EOU
open Vellvm.Semantics.Operations.Gep

#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|gep_indexable"
  gep_indexable : ∀ [Params], dtyp → Bool
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|sequential_stride"
  sequential_stride : ∀ [Params], Bool → dtyp → Nat
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|gep_index_bits"
  gep_index_bits : ∀ [Params], Int
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|trunc_to_index"
  trunc_to_index : ∀ [Params], Int → Int
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|gep_index"
  gep_index : ∀ [Pa : Params], @dvalue Pa → Option Int
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|gep_struct_field"
  gep_struct_field : ∀ [Params], Bool → List dtyp → Nat → Option (Nat × dtyp)
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|gep_steps_h"
  gep_steps_h : ∀ [Pa : Params], dtyp → List (@dvalue Pa) → EOUP (List (Int × Int))
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|gep_steps"
  gep_steps : ∀ [Pa : Params], dtyp → List (@dvalue Pa) → EOUP (List (Int × Int))
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|gep_offset"
  gep_offset : List (Int × Int) → Int
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|in_signed_index_range"
  in_signed_index_range : ∀ [Params], Int → Bool
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|in_unsigned_index_range"
  in_unsigned_index_range : ∀ [Params], Int → Bool
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|gep_nusw_ok"
  gep_nusw_ok : ∀ [Params], Int → Int → List (Int × Int) → Bool
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|gep_nuw_ok"
  gep_nuw_ok : ∀ [Params], Int → Int → List (Int × Int) → Bool
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|gep_inbounds_null_ok"
  gep_inbounds_null_ok : Int → List (Int × Int) → Bool
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|gep_index_trunc_ok"
  gep_index_trunc_ok : ∀ [Pa : Params], Bool → @dvalue Pa → Bool
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|gep_trunc_violated"
  gep_trunc_violated : ∀ [Pa : Params], gep_flags → List (@dvalue Pa) → Bool
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|gep_flags_violated"
  gep_flags_violated : ∀ [Params], gep_flags → Int → List (Int × Int) → Bool
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|handle_gep_ptr"
  handle_gep_ptr : ∀ [Pa : Params], gep_flags → dtyp → Pa.PTR.ptr → List (@dvalue Pa) → EOUP Pa.PTR.ptr
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|handle_gep_ptr_0"
  handle_gep_ptr_0 : ∀ [Pa : Params] (dt : dtyp) (p : Pa.PTR.ptr),
    handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr Pa.IPTR.zero_iptr)] = pure p
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|handle_gep_ptr_nil"
  handle_gep_ptr_nil : ∀ [Pa : Params] (flags : gep_flags) (dt : dtyp) (p : Pa.PTR.ptr),
    handle_gep_ptr flags dt p [] = raise_error "gep_steps: no indices".toUTF8
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|handle_gep_ptr_ix"
  handle_gep_ptr_ix : ∀ [Pa : Params] (dt : dtyp) (p : Pa.PTR.ptr) {p' : Pa.PTR.ptr} (ix : Pa.IPTR.iptr),
    handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = pure p' →
      Pa.P2I.ptr_to_int p' = Pa.P2I.ptr_to_int p + Int.ofNat (alloc_size_dtyp dt) * Pa.IPTR.to_Z ix
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|handle_gep_ptr_ix_OOM"
  handle_gep_ptr_ix_OOM : ∀ [Pa : Params] (dt : dtyp) (p p' : Pa.PTR.ptr) (ix : Pa.IPTR.iptr) {msg : IRString},
    handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = raise_oom msg →
      ∃ msg', Pa.P2I.int_to_ptr (Pa.P2I.ptr_to_int p + Int.ofNat (alloc_size_dtyp dt) * Pa.IPTR.to_Z ix)
        (Pa.PTR.ptr_provenance p) = raise_oom msg'
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|handle_gep_ptr_ix'"
  handle_gep_ptr_ix' : ∀ [Pa : Params] (dt : dtyp) (p : Pa.PTR.ptr) {p' : Pa.PTR.ptr} (ix : Pa.IPTR.iptr),
    raise_ret p' = Pa.P2I.int_to_ptr (Pa.P2I.ptr_to_int p + Int.ofNat (alloc_size_dtyp dt) * Pa.IPTR.to_Z ix)
      (Pa.PTR.ptr_provenance p) →
      handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = pure p'
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|handle_gep_ptr_ix'_OOM"
  handle_gep_ptr_ix'_OOM : ∀ [Pa : Params] (dt : dtyp) (p p' : Pa.PTR.ptr) (ix : Pa.IPTR.iptr) {msg : IRString},
    Pa.P2I.int_to_ptr (Pa.P2I.ptr_to_int p + Int.ofNat (alloc_size_dtyp dt) * Pa.IPTR.to_Z ix)
      (Pa.PTR.ptr_provenance p) = raise_oom msg →
      ∃ msg', handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = raise_oom msg'
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|handle_gep_ptr_preserves_provenance"
  handle_gep_ptr_preserves_provenance : ∀ [Pa : Params] (flags : gep_flags) (dt : dtyp)
    (ixs : List (@dvalue Pa)) (p : Pa.PTR.ptr) {p' : Pa.PTR.ptr},
    handle_gep_ptr flags dt p ixs = pure p' → Pa.PTR.ptr_provenance p = Pa.PTR.ptr_provenance p'
#source_check "src/rocq/Semantics/Operations/Gep.v|Vellvm.Semantics.Operations.Gep|eval_gep"
  eval_gep : ∀ [Pa : Params], gep_flags → dtyp → @dvalue Pa → List (@dvalue Pa) → EOU (@dvalue Pa)
