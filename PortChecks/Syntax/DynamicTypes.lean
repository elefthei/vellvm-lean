import PortChecks.SourceType
import Vellvm.Syntax.DynamicTypes

open Vellvm.Syntax.DynamicTypes

#source_check "src/rocq/Syntax/DynamicTypes.v|Vellvm.Syntax.DynamicTypes|dtyp_base_eq_dec"
  dtyp_base_eq_dec : ∀ x y : dtyp_base, Decidable (x = y)
#source_check "src/rocq/Syntax/DynamicTypes.v|Vellvm.Syntax.DynamicTypes|dtyp_eq_dec"
  dtyp_eq_dec : ∀ x y : dtyp, Decidable (x = y)
#source_check "src/rocq/Syntax/DynamicTypes.v|Vellvm.Syntax.DynamicTypes|dtyp_ind"
  dtyp_ind : ∀ P : dtyp → Prop, (∀ t, P (DTYPE_Base t)) →
    (∀ p ts, (∀ t ∈ ts, P t) → P (DTYPE_Struct p ts)) →
    (∀ v n t, P t → P (DTYPE_Array v n t)) → ∀ t, P t
#source_check "src/rocq/Syntax/DynamicTypes.v|Vellvm.Syntax.DynamicTypes|dtyp_rec"
  dtyp_rec : ∀ P : dtyp → Type, (∀ t, P (DTYPE_Base t)) →
    (∀ p ts, (∀ t ∈ ts, P t) → P (DTYPE_Struct p ts)) →
    (∀ v n t, P t → P (DTYPE_Array v n t)) → ∀ t, P t
#source_check "src/rocq/Syntax/DynamicTypes.v|Vellvm.Syntax.DynamicTypes|dtyp_eqb_refl"
  dtyp_eqb_refl : ∀ dt, dtyp_eqb dt dt = true
#source_check "src/rocq/Syntax/DynamicTypes.v|Vellvm.Syntax.DynamicTypes|dtyp_eqb_eq"
  dtyp_eqb_eq : ∀ x y, dtyp_eqb x y = true → x = y
#source_check "src/rocq/Syntax/DynamicTypes.v|Vellvm.Syntax.DynamicTypes|vector_dtyp_base_dec"
  vector_dtyp_base_dec : ∀ t, Decidable (vector_dtyp_base t)
#source_check "src/rocq/Syntax/DynamicTypes.v|Vellvm.Syntax.DynamicTypes|dtyp_measure_gt_0"
  dtyp_measure_gt_0 : ∀ t, 0 < dtyp_measure t
#source_check "src/rocq/Syntax/DynamicTypes.v|Vellvm.Syntax.DynamicTypes|Decidable_eq_N"
  Decidable_eq_N : ∀ x y : Nat, Decidable (x = y)
#source_check "src/rocq/Syntax/DynamicTypes.v|Vellvm.Syntax.DynamicTypes|NO_VOID_Struct_fields"
  NO_VOID_Struct_fields : ∀ p ts, NO_VOID (DTYPE_Struct p ts) → ∀ dt ∈ ts, NO_VOID dt
#source_check "src/rocq/Syntax/DynamicTypes.v|Vellvm.Syntax.DynamicTypes|NO_VOID_base_dec"
  NO_VOID_base_dec : ∀ dt, Decidable (NO_VOID_base dt)
#source_check "src/rocq/Syntax/DynamicTypes.v|Vellvm.Syntax.DynamicTypes|NO_VOID_dec"
  NO_VOID_dec : ∀ dt, Decidable (NO_VOID dt)
