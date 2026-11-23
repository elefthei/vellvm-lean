module

public import Vellvm.Semantics.IntrinsicsDefinitions.Families
public import Vellvm.Semantics.DynamicValues.Core

@[expose] public section

namespace Vellvm.Semantics.IntrinsicsDefinitions
open Interfaces.Params DynamicValues EOU Numeric Syntax.DynamicTypes

variable [Pa : Params]

abbrev pure_base_function := List dvalue_base → EOU (dvalue_base ⊕ dvalue_base)
abbrev pure_function := List dvalue → EOU (dvalue ⊕ dvalue)

def clearSign {p e : Int} : Flocq.binary_float p e → Flocq.binary_float p e
  | .B754_zero _ => .B754_zero false
  | .B754_infinity _ => .B754_infinity false
  | .B754_nan _ pl h => .B754_nan false pl h
  | .B754_finite _ m i h => .B754_finite false m i h

def llvm_fabs : pure_base_function
  | [.DVALUE_Float x] => .raise_ret (.inr (.DVALUE_Float (clearSign x)))
  | [.DVALUE_Double x] => .raise_ret (.inr (.DVALUE_Double (clearSign x)))
  | _ => .raise_error "llvm.fabs got incorrect / ill-typed inputs".toUTF8

def quiet_nan_pl64 (pl : Positive) : Bool := pl.val.testBit 51
def quiet_nan_pl32 (pl : Positive) : Bool := pl.val.testBit 22

-- Both operands are numbers. On equality the source chooses by the sign of a,
-- so the lesser of opposite signed zeroes is always -0, in either order.
def chooseLeftMinimum {p e : Int} (a b : Flocq.binary_float p e) : Bool :=
  match a, b with
  | .B754_infinity s, _ => s
  | _, .B754_infinity s => !s
  | _, _ => match compare (Flocq.B2Q a) (Flocq.B2Q b) with
    | .lt => true
    | .eq => Flocq.Bsign a
    | .gt => false

-- Flocq's binop_nan_pl32/64 selects the first NaN without quieting its payload.
def maxnum {p e : Int} (quiet : Positive → Bool) (a b : Flocq.binary_float p e) :=
  match a, b with
  | .B754_nan .., .B754_nan .. => a
  | .B754_nan _ pl _, _ => if quiet pl then b else a
  | _, .B754_nan _ pl _ => if quiet pl then a else b
  | _, _ => if chooseLeftMinimum a b then b else a

def Float_maxnum (a b : ll_double) : ll_double := maxnum quiet_nan_pl64 a b
def Float32_maxnum (a b : ll_float) : ll_float := maxnum quiet_nan_pl32 a b

def llvm_maxnum : pure_base_function
  | [.DVALUE_Float a, .DVALUE_Float b] => .raise_ret (.inr (.DVALUE_Float (Float32_maxnum a b)))
  | [.DVALUE_Double a, .DVALUE_Double b] => .raise_ret (.inr (.DVALUE_Double (Float_maxnum a b)))
  | _ => .raise_error "llvm.maxnum got incorrect / ill-typed inputs".toUTF8

def minimumNumberOrNaN {p e : Int} (a b : Flocq.binary_float p e) :=
  match a, b with
  | .B754_nan .., _ => a
  | _, .B754_nan .. => b
  | _, _ => if chooseLeftMinimum a b then a else b

def Float_minimum (a b : ll_double) : ll_double := minimumNumberOrNaN a b
def Float32_minimum (a b : ll_float) : ll_float := minimumNumberOrNaN a b

example (s : Bool) (pl : Positive) (h : Flocq.nan_pl 24 pl = true) :
    Float32_maxnum (.B754_nan s pl h) (.B754_nan (!s) pl h) = .B754_nan s pl h := rfl

def llvm_minimum : pure_base_function
  | [.DVALUE_Float a, .DVALUE_Float b] => .raise_ret (.inr (.DVALUE_Float (Float32_minimum a b)))
  | [.DVALUE_Double a, .DVALUE_Double b] => .raise_ret (.inr (.DVALUE_Double (Float_minimum a b)))
  | _ => .raise_error "llvm.minimum got incorrect / ill-typed inputs".toUTF8

def llvm_vellvm_internal_throw : pure_base_function
  | [] => .raise_ret (.inl .DVALUE_None)
  | _ => .raise_error "llvm_vellvm_internal_throw got incorrect / ill-typed inputs".toUTF8

def llvm_assume : pure_base_function
  | [.DVALUE_I ⟨1, _⟩ c] =>
    if Integers.eq c Integers.one then .raise_ret (.inr .DVALUE_None)
    else .raise_ub "llvm.assume: the condition is false.".toUTF8
  | [.DVALUE_Poison] => .raise_ub "llvm.assume: the condition is poison.".toUTF8
  | _ => .raise_error "llvm.assume got incorrect / ill-typed inputs".toUTF8

def dvalue_to_ival : dvalue → Option ival
  | .DVALUE_Base (.DVALUE_I sz x) => some (.IV_Int sz (Integers.unsigned x))
  | .DVALUE_Base .DVALUE_Poison => some .IV_Poison
  | .DVALUE_Array true elts => elts.foldr lane (some (.IV_Vector []))
  | _ => none
where
  lane : dvalue → Option ival → Option ival
    | .DVALUE_Base (.DVALUE_I sz x), some (.IV_Vector xs) =>
      some (.IV_Vector ((sz, Integers.unsigned x) :: xs))
    | .DVALUE_Base (.DVALUE_I ..), some .IV_Poison | .DVALUE_Base .DVALUE_Poison, some _ =>
      some .IV_Poison
    | _, _ => none

def dvalues_to_ivals (vs : List dvalue) : Option (List ival) := vs.mapM dvalue_to_ival

def ires_to_dvalue : ires → dvalue
  | .IR_Int sz z => .DVALUE_Base (.DVALUE_I sz (Integers.repr z))
  | .IR_Overflow sz z overflow => .DVALUE_Struct false [
      .DVALUE_Base (.DVALUE_I sz (Integers.repr z)),
      .DVALUE_Base (.DVALUE_I ⟨1, by decide⟩ (if overflow then Integers.one else Integers.zero))]
  | .IR_Poison => .DVALUE_Base .DVALUE_Poison

def is_iv_poison : ival → Bool
  | .IV_Poison => true
  | _ => false

def llvm_int_intrinsic (f : int_intrinsic) (t : dtyp) : pure_function := fun args ↦
  let result := (dvalues_to_ivals args).bind fun vals ↦
    if vals.any is_iv_poison then some ires.IR_Poison else f t vals
  match result with
  | some r => .raise_ret (.inr (ires_to_dvalue r))
  | none => .raise_error "integer intrinsic got incorrect / ill-typed inputs".toUTF8

def pure_base_to_pure (f : pure_base_function) : pure_function := fun args ↦ do
  let vs ← Utils.ListUtil.map_monad dvalue_to_dvalue_base args
  return (← f vs).map DVALUE_Base DVALUE_Base

end Vellvm.Semantics.IntrinsicsDefinitions
