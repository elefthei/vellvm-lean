import PortChecks.SourceType
import Vellvm.Semantics.DynamicValues.Default

open Vellvm.Semantics.DynamicValues Vellvm.Semantics.Interfaces.Params
open Vellvm.Semantics.EOU Vellvm.Syntax.DynamicTypes

#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dvalue_default_base_NO_VOID"
  dvalue_default_base_NO_VOID : ∀ [Pa : Params] (t : dtyp_base) {v : dvalue_base},
    default_dvalue_base_of_dtyp_base t = raise_ret v → NO_VOID_base t
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|dvalue_default_NO_VOID"
  dvalue_default_NO_VOID : ∀ [Pa : Params] (t : dtyp) {v : dvalue},
    default_dvalue_of_dtyp t = raise_ret v → NO_VOID t

-- An empty array still asks its element type for a default.
example [Pa : Params] (vec : Bool) :
    default_dvalue_of_dtyp (DTYPE_Array vec 0 (DTYPE_Base DTYPE_Label)) =
      raise_error "Unimplemented default type: label".toUTF8 := by
  rw [default_dvalue_of_dtyp, default_dvalue_of_dtyp]
  rfl

example [Pa : Params] (p vec : Bool) (n : Nat) :
    default_dvalue_of_dtyp (DTYPE_Array vec n (DTYPE_Struct p [])) =
      raise_ret (DVALUE_Array vec (List.replicate n (DVALUE_Struct p []))) := by
  rw [default_dvalue_of_dtyp, default_dvalue_of_dtyp,
    Vellvm.Utils.ListUtil.N_to_nat_safe_eq]
  change raise_ret (DVALUE_Array vec (Vellvm.Utils.ListUtil.repeat_acc _ n)) = _
  rw [Vellvm.Utils.ListUtil.repeat_acc_eq]
