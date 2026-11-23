import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_attributes

open Vellvm Vellvm.Semantics.Attributes Vellvm.Semantics.DynamicValues
open Vellvm.Syntax.LLVMAst Vellvm.Syntax.DynamicTypes
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_attributes

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_assert_aligned_to"
  I2F_assert_aligned_to : ∀ {a1 : @dvalue PInf} {a2 : @dvalue PFin} (align : Option int_syntax)
    (msg : IRString), I2F_dvalue a1 a2 → I2F_EOU (fun _ _ ↦ True)
      (@assert_aligned_to PInf a1 align msg) (@assert_aligned_to PFin a2 align msg)

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_assert_alignment"
  I2F_assert_alignment : ∀ {a1 : @dvalue PInf} {a2 : @dvalue PFin}
    (anns : List (annotation dtyp)) (msg : IRString), I2F_dvalue a1 a2 →
    I2F_EOU (fun _ _ ↦ True) (@assert_alignment PInf a1 anns msg) (@assert_alignment PFin a2 anns msg)

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_value_attr_nonnull"
  I2F_value_attr_nonnull : ∀ (attrs : List param_attr) {x : @dvalue PInf} {y : @dvalue PFin},
    I2F_dvalue x y → I2F_dvalue (@value_attr_nonnull PInf attrs x) (@value_attr_nonnull PFin attrs y)

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_value_attr_align"
  I2F_value_attr_align : ∀ (attrs : List param_attr) {x : @dvalue PInf} {y : @dvalue PFin},
    I2F_dvalue x y → I2F_dvalue (@value_attr_align PInf attrs x) (@value_attr_align PFin attrs y)

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_value_attr_range"
  I2F_value_attr_range : ∀ (attrs : List param_attr) {x : @dvalue PInf} {y : @dvalue PFin},
    I2F_dvalue x y → I2F_dvalue (@value_attr_range PInf attrs x) (@value_attr_range PFin attrs y)

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_fp_class"
  I2F_fp_class : ∀ {b : @dvalue_base PInf} {c : @dvalue_base PFin}, I2F_dvalue_base b c →
    @fp_class PInf b = @fp_class PFin c

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_value_nofpclass"
  I2F_value_nofpclass : ∀ (mask : Int) (dt : dtyp) {x : @dvalue PInf} {y : @dvalue PFin},
    I2F_dvalue x y → I2F_dvalue (@value_nofpclass PInf mask dt x) (@value_nofpclass PFin mask dt y)

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_value_attr_nofpclass"
  I2F_value_attr_nofpclass : ∀ (attrs : List param_attr) (dt : dtyp) {x : @dvalue PInf} {y : @dvalue PFin},
    I2F_dvalue x y → I2F_dvalue (@value_attr_nofpclass PInf attrs dt x) (@value_attr_nofpclass PFin attrs dt y)

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_value_attrs_poison"
  I2F_value_attrs_poison : ∀ (attrs : List param_attr) (dt : dtyp) {x : @dvalue PInf} {y : @dvalue PFin},
    I2F_dvalue x y → I2F_dvalue (@value_attrs_poison PInf attrs dt x) (@value_attrs_poison PFin attrs dt y)

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_apply_value_attrs"
  I2F_apply_value_attrs : ∀ (attrs : List param_attr) (msg : IRString) (dt : dtyp)
    {x : @dvalue PInf} {y : @dvalue PFin}, I2F_dvalue x y → I2F_EOU I2F_dvalue
      (@apply_value_attrs PInf attrs msg dt x) (@apply_value_attrs PFin attrs msg dt y)

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_value_metadata_range_base"
  I2F_value_metadata_range_base : ∀ (rs : List (int_syntax × int_syntax)) {x : @dvalue PInf} {y : @dvalue PFin},
    I2F_dvalue x y → I2F_dvalue (@value_metadata_range_base PInf rs x) (@value_metadata_range_base PFin rs y)

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_value_metadata_range"
  I2F_value_metadata_range : ∀ (r : Option (List (int_syntax × int_syntax))) (dt : dtyp)
    {x : @dvalue PInf} {y : @dvalue PFin}, I2F_dvalue x y → I2F_dvalue
      (@value_metadata_range PInf r dt x) (@value_metadata_range PFin r dt y)

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_forallb_well_defined"
  I2F_forallb_well_defined : ∀ {xs : List (@dvalue PInf)} {ys : List (@dvalue PFin)},
    List.Forall₂ I2F_dvalue xs ys → xs.all (@dvalue_well_defined PInf) = ys.all (@dvalue_well_defined PFin)

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_check_call_result"
  I2F_check_call_result : ∀ (fattrs : List fn_attr) (msg : IRString)
    {xs : List (@dvalue PInf)} {ys : List (@dvalue PFin)}
    {r1 : @dvalue PInf ⊕ @dvalue PInf} {r2 : @dvalue PFin ⊕ @dvalue PFin},
    List.Forall₂ I2F_dvalue xs ys → Sum.LiftRel I2F_dvalue I2F_dvalue r1 r2 →
    I2F_EOU (fun _ _ ↦ True) (@check_call_result PInf fattrs msg xs r1) (@check_call_result PFin fattrs msg ys r2)

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_check_callee"
  I2F_check_callee : ∀ {x : @dvalue PInf} {y : @dvalue PFin}, I2F_dvalue x y →
    I2F_EOU (fun _ _ ↦ True) (@check_callee PInf x) (@check_callee PFin y)

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_dvalue_ptr_address"
  I2F_dvalue_ptr_address : ∀ {x : @dvalue PInf} {y : @dvalue PFin}, I2F_dvalue x y →
    @dvalue_ptr_address PInf x = @dvalue_ptr_address PFin y

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_bundle_uint"
  I2F_bundle_uint : ∀ {x : @dvalue PInf} {y : @dvalue PFin}, I2F_dvalue x y →
    @bundle_uint PInf x = @bundle_uint PFin y

#source_check "src/rocq/Theory/I2F/I2F_attributes.v|Vellvm.Theory.I2F.I2F_attributes|I2F_bundle_sint"
  I2F_bundle_sint : ∀ {x : @dvalue PInf} {y : @dvalue PFin}, I2F_dvalue x y →
    @bundle_sint PInf x = @bundle_sint PFin y
