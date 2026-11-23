import Vellvm.Semantics.DynamicValues

namespace Vellvm.Semantics.Operations.Select
open Interfaces.Params DynamicValues EOU Syntax.DynamicTypes Utils.ListUtil Numeric.Integers

variable [Pa : Params]

def eval_select_base (cnd v1 v2 : dvalue_base) : EOU dvalue_base :=
  match cnd with
  | .DVALUE_Poison => raise_ret DVALUE_Poison
  | .DVALUE_I ⟨1, _⟩ i => raise_ret (if unsigned i == 1 then v1 else v2)
  | _ => raise_error "eval_select_base: ill-typed select.".toUTF8

def eval_select_base_dvalue (cnd : dvalue_base) (v1 v2 : dvalue) : EOU dvalue :=
  match cnd with
  | .DVALUE_Poison => raise_ret (DVALUE_Base DVALUE_Poison)
  | .DVALUE_I ⟨1, _⟩ i => raise_ret (if unsigned i == 1 then v1 else v2)
  | _ => raise_error "eval_select_base_dvalue: ill-typed select.".toUTF8

def eval_select (cnd : dvalue) (v_t : dtyp) (v1 v2 : dvalue) : EOU dvalue :=
  match cnd with
  | .DVALUE_Base .DVALUE_Poison => raise_ret (poison_of_dtyp v_t)
  | .DVALUE_Base c => eval_select_base_dvalue c v1 v2
  | .DVALUE_Array true conds =>
    match v_t with
    | .DTYPE_Array true sz _ => do
      let cs ← map_monad dvalue_to_dvalue_base conds
      let selectLanes (xs ys : List dvalue) :=
        canonicalize_agg v_t <$> vec_loop (fun c (x, y) ↦ eval_select_base_dvalue c x y)
          (cs.zip (xs.zip ys))
      match v1, v2 with
      | .DVALUE_Array true xs, .DVALUE_Array true ys => selectLanes xs ys
      | .DVALUE_Base .DVALUE_Poison, .DVALUE_Array true ys =>
        selectLanes (List.replicate sz (DVALUE_Base DVALUE_Poison)) ys
      | .DVALUE_Array true xs, .DVALUE_Base .DVALUE_Poison =>
        selectLanes xs (List.replicate sz (DVALUE_Base DVALUE_Poison))
      | .DVALUE_Base .DVALUE_Poison, .DVALUE_Base .DVALUE_Poison =>
        raise_ret (DVALUE_Base DVALUE_Poison)
      | _, _ => raise_error "eval_select: non-vector argument values".toUTF8
    | _ => raise_error "eval_select: ill-typed select.".toUTF8
  | _ => raise_error "eval_select: ill-typed select.".toUTF8

end Vellvm.Semantics.Operations.Select
