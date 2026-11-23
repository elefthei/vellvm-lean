import Vellvm.Semantics.DynamicValues.Canonical
import Vellvm.Semantics.LLVMEvents
import Vellvm.Numeric.Floats.Raw
import Vellvm.Utils.ZUtil

namespace Vellvm.Semantics.Attributes
open Interfaces.Params DynamicValues Numeric.Integers Syntax.LLVMAst Syntax.DynamicTypes EOU
open LLVMEvents (exc)

def denote_int_syntax (x : int_syntax) : Int := x.toInt

def explicit_alignment (anns : List (annotation dtyp)) : Option Nat :=
  (anns.findSome? ann_align).map fun a ↦ (denote_int_syntax a).toNat

def attr_is_nonnull : param_attr → Bool
  | .PARAMATTR_Nonnull | .PARAMATTR_Dereferenceable _ => true
  | _ => false

def attr_is_noundef : param_attr → Bool
  | .PARAMATTR_Noundef | .PARAMATTR_Dereferenceable _ => true
  | _ => false

def in_wrapping_range (sz : Positive) (x lo hi : Int) : Bool :=
  let m := (2 : Int) ^ sz.val
  let x := x % m
  let lo := lo % m
  let hi := hi % m
  if lo == hi then false
  else if lo < hi then decide (lo ≤ x) && decide (x < hi)
  else decide (lo ≤ x) || decide (x < hi)

def fp_class_of_bits (e m bits : Int) : Int :=
  let neg := Numeric.Zbits.testbit bits (e + m)
  let ones := fun n ↦ Utils.ZUtil.shiftl 1 n - 1
  let exp := Int.land (Utils.ZUtil.shiftl bits (-m)) (ones e)
  let mant := Int.land bits (ones m)
  if exp == ones e then
    if mant == 0 then (if neg then 4 else 512)
    else if Numeric.Zbits.testbit mant (m - 1) then 2 else 1
  else if exp == 0 then
    if mant == 0 then (if neg then 32 else 64) else (if neg then 16 else 128)
  else if neg then 8 else 256

def is_power_of_two (n : Int) : Bool := decide (0 < n) && Int.land n (n - 1) == 0

variable [Pa : Params]

def assert_aligned_to (a : dvalue) (align : Option int_syntax) (msg : IRString) : EOU Unit :=
  match a, align with
  | DVALUE_Base (DVALUE_Pointer p), some al =>
    if Interfaces.Pointer.ptr_aligned_to p (denote_int_syntax al).toNat then pure ()
    else raise_ub msg
  | _, _ => pure ()

def assert_alignment (a : dvalue) (anns : List (annotation dtyp)) (msg : IRString) : EOU Unit :=
  assert_aligned_to a (anns.findSome? ann_align) msg

def value_attr_nonnull (attrs : List param_attr) (v : dvalue) : dvalue :=
  match v with
  | DVALUE_Base (DVALUE_Pointer p) =>
    if attrs.any attr_is_nonnull && Pa.P2I.ptr_to_int p == Pa.P2I.ptr_to_int Pa.PTR.null
    then DVALUE_Base DVALUE_Poison else v
  | _ => v

def value_attr_align (attrs : List param_attr) (v : dvalue) : dvalue :=
  match v, attrs.findSome? attr_align with
  | DVALUE_Base (DVALUE_Pointer p), some al =>
    if Interfaces.Pointer.ptr_aligned_to p (denote_int_syntax al).toNat then v
    else DVALUE_Base DVALUE_Poison
  | _, _ => v

def value_attr_range (attrs : List param_attr) (v : dvalue) : dvalue :=
  match v, attrs.findSome? attr_range with
  | DVALUE_Base (DVALUE_I sz x), some (lo, hi) =>
    if in_wrapping_range sz (unsigned x) (denote_int_syntax lo) (denote_int_syntax hi) then v
    else DVALUE_Base DVALUE_Poison
  | _, _ => v

def fp_class : dvalue_base → Option Int
  | DVALUE_Double d => some (fp_class_of_bits 11 52 (unsigned (Numeric.Floats.Float.to_bits d)))
  | DVALUE_Float f => some (fp_class_of_bits 8 23 (unsigned (Numeric.Floats.Float32.to_bits f)))
  | _ => none

mutual
  def value_nofpclass (mask : Int) (dt : dtyp) (v : dvalue) : dvalue :=
    match v, dt with
    | DVALUE_Base b, _ =>
      match fp_class b with
      | some c => if Int.land mask c == 0 then v else DVALUE_Base DVALUE_Poison
      | none => v
    | DVALUE_Array _ elts, .DTYPE_Array _ _ t =>
      canonicalize_agg dt (nofpclassElts mask t elts)
    | DVALUE_Struct _ fields, .DTYPE_Struct _ ts => canonicalize_agg dt (nofpclassFields mask ts fields)
    | _, _ => v
  termination_by structural v

  def nofpclassElts (mask : Int) (t : dtyp) (vs : List dvalue) : List dvalue :=
    match vs with
    | [] => []
    | v :: vs' => value_nofpclass mask t v :: nofpclassElts mask t vs'
  termination_by structural vs

  def nofpclassFields (mask : Int) (ts : List dtyp) (vs : List dvalue) : List dvalue :=
    match ts, vs with
    | t :: ts', v :: vs' => value_nofpclass mask t v :: nofpclassFields mask ts' vs'
    | _, _ => vs
  termination_by structural vs
end

def value_attr_nofpclass (attrs : List param_attr) (dt : dtyp) (v : dvalue) : dvalue :=
  match attrs.findSome? attr_nofpclass with
  | some mask => value_nofpclass mask dt v
  | none => v

def value_attrs_poison (attrs : List param_attr) (dt : dtyp) (v : dvalue) : dvalue :=
  value_attr_nofpclass attrs dt (value_attr_range attrs (value_attr_align attrs (value_attr_nonnull attrs v)))

def apply_value_attrs (attrs : List param_attr) (msg : IRString) (dt : dtyp) (v : dvalue) : EOU dvalue :=
  let v := value_attrs_poison attrs dt v
  if attrs.any attr_is_noundef && !dvalue_well_defined v then raise_ub msg else pure v

def in_metadata_ranges (sz : Positive) (x : Int) (ranges : List (int_syntax × int_syntax)) : Bool :=
  ranges.any fun (lo, hi) ↦ in_wrapping_range sz x (denote_int_syntax lo) (denote_int_syntax hi)

def value_metadata_range_base (ranges : List (int_syntax × int_syntax)) (v : dvalue) : dvalue :=
  match v with
  | DVALUE_Base (DVALUE_I sz x) =>
    if in_metadata_ranges sz (unsigned x) ranges then v else DVALUE_Base DVALUE_Poison
  | _ => v

def value_metadata_range (ranges : Option (List (int_syntax × int_syntax))) (dt : dtyp) (v : dvalue) : dvalue :=
  match ranges, v with
  | none, _ => v
  | some rs, DVALUE_Array true elts => canonicalize_agg dt (elts.map (value_metadata_range_base rs))
  | some rs, _ => value_metadata_range_base rs v

def check_call_result (fattrs : List fn_attr) (msg : IRString) (args : List dvalue)
    (res : exc ⊕ dvalue) : EOU Unit :=
  match res with
  | .inl _ =>
    if fattrs.any fn_attr_is_nounwind then raise_ub (msg ++ ": unwinding out of a nounwind function.".toUTF8)
    else pure ()
  | .inr v =>
    if fattrs.any fn_attr_is_noreturn then raise_ub (msg ++ ": returning from a noreturn function.".toUTF8)
    else if fattrs.any fn_attr_is_nocreateundeforpoison && args.all dvalue_well_defined && !dvalue_well_defined v
    then raise_ub (msg ++ ": a nocreateundeforpoison function returned undef or poison for well-defined arguments.".toUTF8)
    else pure ()

def check_cconv (fcc cc : cconv) (fname : IRString) : EOU Unit :=
  if cconv_eqb cc fcc then pure ()
  else raise_ub ("Call to ".toUTF8 ++ fname ++ " with a calling convention that does not match its definition.".toUTF8)

def check_callee (fv : dvalue) : EOU Unit :=
  match fv with
  | DVALUE_Base DVALUE_Poison => raise_ub "call via poison function pointer".toUTF8
  | DVALUE_Base (DVALUE_Pointer p) =>
    if Pa.P2I.ptr_to_int p == Pa.P2I.ptr_to_int Pa.PTR.null then raise_ub "call via null function pointer".toUTF8
    else pure ()
  | _ => raise_error "function call to non-pointer value".toUTF8

def bundle_uint : dvalue → Option Int
  | DVALUE_Base (DVALUE_I _ x) => some (unsigned x)
  | _ => none

def bundle_sint : dvalue → Option Int
  | DVALUE_Base (DVALUE_I _ x) => some (signed x)
  | _ => none

end Vellvm.Semantics.Attributes
