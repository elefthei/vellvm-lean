import PortChecks.SourceType
import Vellvm.Semantics.DynamicValues.Canonical

open Vellvm Vellvm.Numeric.Integers Vellvm.Syntax.DynamicTypes
open Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.DynamicValues

#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dtyp_is_empty"
  dtyp_is_empty : dtyp → Bool
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|empty_dvalue_of_dtyp"
  empty_dvalue_of_dtyp : ∀ [Pa : Params], dtyp → dvalue
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|poison_of_dtyp"
  poison_of_dtyp : ∀ [Pa : Params], dtyp → dvalue
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|fields_all_poison"
  fields_all_poison : ∀ [Pa : Params], List dtyp → List dvalue → Bool
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|agg_is_poison"
  agg_is_poison : ∀ [Pa : Params], dtyp → List dvalue → Bool
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|canonicalize_agg"
  canonicalize_agg : ∀ [Pa : Params], dtyp → List dvalue → dvalue
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dvalue_is_canonical"
  dvalue_is_canonical : ∀ [Pa : Params], dtyp → dvalue → Bool
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|vector_elts"
  vector_elts : ∀ [Pa : Params], Nat → dvalue → Option (List dvalue)

#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dvalue_bv_has_sz"
  dvalue_bv_has_sz : ∀ [Pa : Params] {sz : Positive}, Positive → dvalue_bv sz → Prop
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|BYTE_Pointer_sz"
  BYTE_Pointer_sz : ∀ [Pa : Params] {sz : Positive} (x : Pa.PTR.ptr) (idx : Nat),
    dvalue_bv_has_sz (sz := sz) sz (BYTE_Pointer x idx)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|BYTE_Int_sz"
  BYTE_Int_sz : ∀ [Pa : Params] {sz sz' : Positive} (x : bit_int sz),
    sz = sz' → dvalue_bv_has_sz sz' (BYTE_I x)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|BYTE_Mixed_sz"
  BYTE_Mixed_sz : ∀ [Pa : Params] {sz : Positive} (bits : List memory_bit) {sz' : Positive},
    bits.length = sz'.val → sz = sz' → dvalue_bv_has_sz (sz := sz) sz' (BYTE_Mixed bits)

#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dvalue_has_dtyp"
  dvalue_has_dtyp : ∀ [Pa : Params], dvalue → dtyp → Prop
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|DVALUE_Base_typ"
  DVALUE_Base_typ : ∀ [Pa : Params] (dv : dvalue_base) (t : dtyp_base),
    dvalue_base_has_dtyp_base dv t = true → dvalue_base_canonical dv = true →
    dvalue_has_dtyp (DVALUE_Base dv) (DTYPE_Base t)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|DVALUE_Poison_typ_agg"
  DVALUE_Poison_typ_agg : ∀ [Pa : Params] (t : dtyp), dtyp_is_empty t = false →
    dvalue_has_dtyp (DVALUE_Base DVALUE_Poison) t
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|DVALUE_Struct_typ"
  DVALUE_Struct_typ : ∀ [Pa : Params] (p : Bool) {fields : List dvalue} {dts : List dtyp},
    agg_is_poison (DTYPE_Struct p dts) fields = false → List.Forall₂ dvalue_has_dtyp fields dts →
    dvalue_has_dtyp (DVALUE_Struct p fields) (DTYPE_Struct p dts)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|DVALUE_Array_typ"
  DVALUE_Array_typ : ∀ [Pa : Params] (v : Bool) {xs : List dvalue} (sz : Nat) {dt : dtyp},
    NO_VOID dt → agg_is_poison (DTYPE_Array v sz dt) xs = false →
    (∀ x ∈ xs, dvalue_has_dtyp x dt) → xs.length = sz →
    dvalue_has_dtyp (DVALUE_Array v xs) (DTYPE_Array v sz dt)

#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|fields_canonical"
  fields_canonical : ∀ [Pa : Params], List dtyp → List dvalue → Bool
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dvalue_is_canonical_struct"
  dvalue_is_canonical_struct : ∀ [Pa : Params] (p : Bool) (fields : List dvalue) (q : Bool)
    (dts : List dtyp), dvalue_is_canonical (DTYPE_Struct q dts) (DVALUE_Struct p fields) =
    (((p == q) && !agg_is_poison (DTYPE_Struct q dts) fields) && fields_canonical dts fields)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dvalue_is_canonical_sound"
  dvalue_is_canonical_sound : ∀ [Pa : Params] (dv : dvalue) (dt : dtyp),
    dvalue_is_canonical dt dv = true → dvalue_has_dtyp dv dt
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dvalue_is_canonical_complete"
  dvalue_is_canonical_complete : ∀ [Pa : Params] {dv : dvalue} {dt : dtyp},
    dvalue_has_dtyp dv dt → dvalue_is_canonical dt dv = true
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dvalue_is_canonical_iff"
  dvalue_is_canonical_iff : ∀ [Pa : Params] (dv : dvalue) (dt : dtyp),
    dvalue_is_canonical dt dv = true ↔ dvalue_has_dtyp dv dt
