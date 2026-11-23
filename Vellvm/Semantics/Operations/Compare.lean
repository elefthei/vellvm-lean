import Vellvm.Semantics.DynamicValues

namespace Vellvm.Semantics.Operations.Compare
open Interfaces.Params DynamicValues EOU Syntax.DynamicTypes Syntax.LLVMAst Utils.ListUtil

variable [Pa : Params]

def is_icmp_operand : dvalue_base → Bool
  | .DVALUE_I _ _ | .DVALUE_Iptr _ | .DVALUE_Pointer _ => true
  | _ => false

def eval_icmp_int_base (samesign : Bool) (op : icmp) (v1 v2 : dvalue_base) : EOU dvalue_base :=
  match v1, v2 with
  | .DVALUE_I w x, .DVALUE_I w' y =>
    if h : w = w' then eval_int_icmp samesign op x (h.symm ▸ y) else illTyped v1 v2
  | .DVALUE_Iptr x, .DVALUE_Iptr y =>
    letI := Pa.IPTR.VMemInt_iptr
    eval_int_icmp samesign op x y
  | .DVALUE_Poison, .DVALUE_Poison => raise_ret DVALUE_Poison
  | .DVALUE_Poison, v | v, .DVALUE_Poison =>
    if is_icmp_operand v then raise_ret DVALUE_Poison else raise_error "ill_typed-iop".toUTF8
  | _, _ => illTyped v1 v2
where
  illTyped (x y : dvalue_base) : EOU dvalue_base :=
    raise_error ("eval_icmp_base: ill_typed-icmp: ".toUTF8 ++ show_dvalue_base x ++
      ", ".toUTF8 ++ show_dvalue_base y)

def ptr_to_addr (a : Pa.PTR.ptr) : EOU dvalue_base :=
  match Pa.SIZE.bit_sizeof_dtyp (DTYPE_Base DTYPE_Pointer) with
  | 0 => raise_error "ptr_to_addr: pointers have no address bits".toUTF8
  | n+1 => coerce_integer_to_int (some ⟨n+1, Nat.zero_lt_succ n⟩) (Pa.P2I.ptr_to_int a)

def eval_icmp_base (samesign : Bool) (op : icmp) (v1 v2 : dvalue_base) : EOU dvalue_base :=
  match v1, v2 with
  | .DVALUE_Pointer a1, .DVALUE_Pointer a2 => do
    let i1 ← ptr_to_addr a1
    let i2 ← ptr_to_addr a2
    eval_icmp_int_base samesign op i1 i2
  | _, _ => eval_icmp_int_base samesign op v1 v2

def eval_icmp (samesign : Bool) (op : icmp) (dt : dtyp) (v1 v2 : dvalue) : EOU dvalue :=
  match dt with
  | .DTYPE_Array true sz _ =>
    match vector_elts sz v1, vector_elts sz v2 with
    | some xs, some ys => do
      if xs.length != ys.length then raise_ub "icmp of different-length vectors".toUTF8
      else
        let xs' ← map_monad dvalue_to_dvalue_base xs
        let ys' ← map_monad dvalue_to_dvalue_base ys
        let vals ← vec_loop (eval_icmp_base samesign op) (xs'.zip ys')
        return canonicalize_agg (DTYPE_Array true sz (DTYPE_I ⟨1, by decide⟩))
          (vals.map DVALUE_Base)
    | _, _ => raise_error "eval_icmp_base: ill-typed icmp".toUTF8
  | _ =>
    match v1, v2 with
    | .DVALUE_Base x, .DVALUE_Base y => DVALUE_Base <$> eval_icmp_base samesign op x y
    | _, _ => raise_error "eval_icmp_base: ill-typed icmp".toUTF8

end Vellvm.Semantics.Operations.Compare
