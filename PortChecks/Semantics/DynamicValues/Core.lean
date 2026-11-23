import PortChecks.SourceType
import Vellvm.Semantics.DynamicValues.Core

open Vellvm Vellvm.Semantics.DynamicValues Vellvm.Semantics.Interfaces.Params
open Vellvm.Syntax.LLVMAst Vellvm.Numeric.Integers

#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|Eqv_nat"
  Eqv_nat : HasEquiv.{1,0} Nat
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|Decidable_eq_N"
  Decidable_eq_N : ∀ x y : Nat, Decidable (x = y)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dvalue_ind"
  dvalue_ind : ∀ [Pa : Params] (P : dvalue → Prop),
    (∀ b, P (DVALUE_Base b)) →
    (∀ p fs, (∀ x ∈ fs, P x) → P (DVALUE_Struct p fs)) →
    (∀ v es, (∀ x ∈ es, P x) → P (DVALUE_Array v es)) → ∀ dv, P dv
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|memory_bit_eq_dec"
  memory_bit_eq_dec : ∀ [Pa : Params] (x y : memory_bit), Decidable (x = y)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dvalue_bv_eq_dec"
  dvalue_bv_eq_dec : ∀ [Pa : Params] {sz : Positive} (x y : dvalue_bv sz), Decidable (x = y)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dvalue_base_eq_dec"
  dvalue_base_eq_dec : ∀ [Pa : Params] (x y : dvalue_base), Decidable (x = y)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dvalue_eq_dec"
  dvalue_eq_dec : ∀ [Pa : Params] (x y : dvalue), Decidable (x = y)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|eq_dec_dvalue"
  eq_dec_dvalue : ∀ [Pa : Params], BEq dvalue
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|eqv_dvalue"
  eqv_dvalue : ∀ [Pa : Params], HasEquiv.{1,0} dvalue
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dvalue_is_poison_true"
  dvalue_is_poison_true : ∀ [Pa : Params] (d : dvalue), dvalue_is_poison d = true → d = DVALUE_Base DVALUE_Poison
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dvalue_is_poison_false"
  dvalue_is_poison_false : ∀ [Pa : Params] (d : dvalue), dvalue_is_poison d = false → d ≠ DVALUE_Base DVALUE_Poison
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|ibinop_eq_dec"
  ibinop_eq_dec : ∀ x y : ibinop, Decidable (x = y)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|fbinop_eq_dec"
  fbinop_eq_dec : ∀ x y : fbinop, Decidable (x = y)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|icmp_eq_dec"
  icmp_eq_dec : ∀ x y : icmp, Decidable (x = y)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|fcmp_eq_dec"
  fcmp_eq_dec : ∀ x y : fcmp, Decidable (x = y)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|fast_math_eq_dec"
  fast_math_eq_dec : ∀ x y : fast_math, Decidable (x = y)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|conversion_type_eq_dec"
  conversion_type_eq_dec : ∀ x y : conversion_type, Decidable (x = y)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|ToDvalue_iptr"
  ToDvalue_iptr : ∀ [Pa : Params], ToDvalueBase Pa.IPTR.iptr
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|ToDvalue_Int"
  ToDvalue_Int : ∀ [Pa : Params] {sz : Positive}, ToDvalueBase (bit_int sz)
