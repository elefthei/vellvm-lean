import PortChecks.SourceType
import Vellvm.Semantics.Operations.Select

open Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.DynamicValues Vellvm.Semantics.EOU
open Vellvm.Syntax.DynamicTypes Vellvm.Semantics.Operations.Select

#source_check "src/rocq/Semantics/Operations/Select.v|Vellvm.Semantics.Operations.Select|eval_select_base"
  eval_select_base : ∀ [Pa : Params], dvalue_base → dvalue_base → dvalue_base → EOU dvalue_base
#source_check "src/rocq/Semantics/Operations/Select.v|Vellvm.Semantics.Operations.Select|eval_select_base_dvalue"
  eval_select_base_dvalue : ∀ [Pa : Params], dvalue_base → dvalue → dvalue → EOU dvalue
#source_check "src/rocq/Semantics/Operations/Select.v|Vellvm.Semantics.Operations.Select|eval_select"
  eval_select : ∀ [Pa : Params], dvalue → dtyp → dvalue → dvalue → EOU dvalue

variable [Pa : Params]

example (t : dtyp) (x y : dvalue) :
    eval_select (DVALUE_Base DVALUE_Poison) t x y = raise_ret (poison_of_dtyp t) := rfl

-- Even two poison alternatives do not mask a non-scalar condition lane.
example : eval_select (DVALUE_Array true [DVALUE_Struct false []])
    (DTYPE_Array true 1 DTYPE_Pointer) (DVALUE_Base DVALUE_Poison) (DVALUE_Base DVALUE_Poison) =
    raise_error "dvalue_to_dvalue_base: got non-base value".toUTF8 := rfl
