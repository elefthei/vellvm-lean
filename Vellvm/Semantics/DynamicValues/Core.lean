module

public import Vellvm.Semantics.DynamicValues.Basic

@[expose] public section

namespace Vellvm.Semantics.DynamicValues
open Interfaces.Params Numeric.Integers Syntax.LLVMAst Syntax.DynamicTypes EOU

instance Eqv_nat : HasEquiv.{1,0} Nat := ⟨(· = ·)⟩
def FT_Rounding : Numeric.Flocq.Mode := .mode_NE

def inttyp : Nat → Type
  | 1 => VellvmIntegers.int1
  | 8 => VellvmIntegers.int8
  | 16 => VellvmIntegers.int16
  | 32 => VellvmIntegers.int32
  | 64 => VellvmIntegers.int64
  | _ => Empty

def Decidable_eq_N : DecidableEq Nat := inferInstance

variable [Pa : Params]

def Z_to_memory_bit (z : Int) : memory_bit := .Bit_bit (Numeric.Integers.repr z)

def dvalue_to_dvalue_base : dvalue → EOU dvalue_base
  | .DVALUE_Base b => .raise_ret b
  | _ => .raise_error "dvalue_to_dvalue_base: got non-base value".toUTF8

def is_poison_bit : memory_bit → Bool
  | .Bit_psn => true
  | _ => false

def is_int_bit : memory_bit → Bool
  | .Bit_bit _ => true
  | _ => false

def is_ptr_bit : memory_bit → Bool
  | .Bit_ptr .. => true
  | _ => false

def int_bits_to_Z : List memory_bit → Int
  | [] => 0
  | .Bit_bit b :: rest => unsigned b + 2 * int_bits_to_Z rest
  | _ :: rest => 2 * int_bits_to_Z rest

def all_pointer_bits_from (p : Pa.PTR.ptr) (j : Nat) : List memory_bit → Bool
  | [] => true
  | .Bit_ptr q i :: rest => Numeric.Rocqlib.chooseSide (Pa.PTR.eq_dec_ptr p q) true false &&
      i == j && all_pointer_bits_from p (1 + j) rest
  | _ => false

def is_pointer_chunk (bit_sz : Positive) (bits : List memory_bit) : Bool :=
  match bits with
  | .Bit_ptr p j :: _ => bit_sz.val % 8 == 0 && j % bit_sz.val == 0 && all_pointer_bits_from p j bits
  | _ => false

def dvalue_bv_all_poison {sz : Positive} : dvalue_bv sz → Bool
  | .BYTE_Mixed bits => bits.all is_poison_bit
  | _ => false

def dvalue_bv_canonical {sz : Positive} : dvalue_bv sz → Bool
  | .BYTE_I _ => true
  | .BYTE_Pointer .. => sz.val % 8 == 0
  | .BYTE_Mixed bits => bits.length == sz.val && !(is_pointer_chunk sz bits) &&
      !(bits.all is_int_bit) && !(bits.all is_poison_bit)

def dvalue_base_canonical : dvalue_base → Bool
  | .DVALUE_B _ bv => dvalue_bv_canonical bv
  | _ => true

def dvalue_base_has_dtyp_base : dvalue_base → dtyp_base → Bool
  | .DVALUE_Pointer _, .DTYPE_Pointer | .DVALUE_Iptr _, .DTYPE_Iptr
  | .DVALUE_Double _, .DTYPE_FP .FP_double | .DVALUE_Float _, .DTYPE_FP .FP_float
  | .DVALUE_Poison, _ | .DVALUE_None, .DTYPE_Void => true
  | .DVALUE_I w _, .DTYPE_I w' | .DVALUE_B w _, .DTYPE_B w' => w == w'
  | _, _ => false

theorem dvalue_ind (P : dvalue → Prop) (base : ∀ b, P (DVALUE_Base b))
    (struct : ∀ p fs, (∀ x ∈ fs, P x) → P (DVALUE_Struct p fs))
    (array : ∀ v es, (∀ x ∈ es, P x) → P (DVALUE_Array v es)) (dv : dvalue) : P dv :=
  match dv with
  | .DVALUE_Base b => base b
  | .DVALUE_Struct p fs => struct p fs fun x _ ↦ dvalue_ind P base struct array x
  | .DVALUE_Array v es => array v es fun x _ ↦ dvalue_ind P base struct array x
termination_by sizeOf dv
decreasing_by all_goals decreasing_tactic

local instance ptrDec : DecidableEq Pa.PTR.ptr := Numeric.Rocqlib.eqDecidable Pa.PTR.eq_dec_ptr
local instance iptrDec : DecidableEq Pa.IPTR.iptr := Numeric.Rocqlib.eqDecidable Pa.IPTR.eq_dec_iptr

deriving instance DecidableEq for memory_bit
deriving instance DecidableEq for dvalue_bv
deriving instance DecidableEq for dvalue_base

def memory_bit_eq_dec : DecidableEq memory_bit := inferInstance
def dvalue_bv_eq_dec {sz : Positive} : DecidableEq (dvalue_bv sz) := inferInstance
def dvalue_base_eq_dec : DecidableEq dvalue_base := inferInstance

mutual
  def dvalue_eq_dec (x y : dvalue) : Decidable (x = y) := by
    cases x with
    | DVALUE_Base a =>
      cases y with
      | DVALUE_Base b => exact decidable_of_iff (a = b) (by simp)
      | _ => exact .isFalse (by intro h; cases h)
    | DVALUE_Struct p xs =>
      cases y with
      | DVALUE_Struct q ys =>
        letI := dvalue_list_eq_dec xs ys
        exact decidable_of_iff (p = q ∧ xs = ys) (by simp)
      | _ => exact .isFalse (by intro h; cases h)
    | DVALUE_Array v xs =>
      cases y with
      | DVALUE_Array w ys =>
        letI := dvalue_list_eq_dec xs ys
        exact decidable_of_iff (v = w ∧ xs = ys) (by simp)
      | _ => exact .isFalse (by intro h; cases h)

  def dvalue_list_eq_dec (xs ys : List dvalue) : Decidable (xs = ys) := by
    cases xs with
    | nil => cases ys <;> first | exact .isTrue rfl | exact .isFalse (by intro h; cases h)
    | cons a as =>
      cases ys with
      | nil => exact .isFalse (by intro h; cases h)
      | cons b bs =>
        letI := dvalue_eq_dec a b
        letI := dvalue_list_eq_dec as bs
        exact decidable_of_iff (a = b ∧ as = bs) (by simp)
end

attribute [instance_reducible, instance] dvalue_eq_dec

def dvalue_eqb (a b : dvalue) : Bool := decide (a = b)
instance eq_dec_dvalue : BEq dvalue := ⟨dvalue_eqb⟩
instance eqv_dvalue : HasEquiv.{1,0} dvalue := ⟨(· = ·)⟩

def dvalue_is_poison : dvalue → Bool
  | .DVALUE_Base .DVALUE_Poison => true
  | _ => false

theorem dvalue_is_poison_true (d : dvalue) : dvalue_is_poison d = true → d = DVALUE_Base DVALUE_Poison := by
  cases d with
  | DVALUE_Base b => cases b <;> simp [dvalue_is_poison]
  | _ => simp [dvalue_is_poison]

theorem dvalue_is_poison_false (d : dvalue) : dvalue_is_poison d = false → d ≠ DVALUE_Base DVALUE_Poison := by
  rintro h rfl; cases h

def dvalue_ptr_address : dvalue → Option Int
  | .DVALUE_Base (.DVALUE_Pointer p) => some (Pa.P2I.ptr_to_int p)
  | _ => none

def dvalue_base_well_defined : dvalue_base → Bool
  | .DVALUE_Poison => false
  | .DVALUE_B _ (.BYTE_Mixed bits) => !(bits.any is_poison_bit)
  | _ => true

def dvalue_well_defined : dvalue → Bool
  | .DVALUE_Base b => dvalue_base_well_defined b
  | .DVALUE_Struct _ fields | .DVALUE_Array _ fields => fields.all dvalue_well_defined

deriving instance DecidableEq for ibinop, fbinop, icmp, fcmp, fast_math, pure_conversion,
  impure_conversion, conversion_type

def ibinop_eq_dec : DecidableEq ibinop := inferInstance
def fbinop_eq_dec : DecidableEq fbinop := inferInstance
def icmp_eq_dec : DecidableEq icmp := inferInstance
def fcmp_eq_dec : DecidableEq fcmp := inferInstance
def fast_math_eq_dec : DecidableEq fast_math := inferInstance
def conversion_type_eq_dec : DecidableEq conversion_type := inferInstance

def is_DVALUE_IX : dvalue_base → Bool
  | .DVALUE_I .. => true
  | _ => false

class ToDvalueBase [Pa : Params] (I : Type u) where
  Build_ToDvalueBase ::
  tdb : I → dvalue_base
export ToDvalueBase (Build_ToDvalueBase tdb)

instance ToDvalue_iptr : ToDvalueBase Pa.IPTR.iptr := ⟨DVALUE_Iptr⟩
instance ToDvalue_Int {sz : Positive} : ToDvalueBase (bit_int sz) := ⟨DVALUE_I sz⟩

def dvalue_base_int_unsigned : dvalue_base → Int
  | .DVALUE_I _ x => unsigned x
  | .DVALUE_Iptr i => Pa.IPTR.to_unsigned i
  | _ => 0

def dvp (_ : dtyp_base) : dvalue_base := .DVALUE_Poison

end Vellvm.Semantics.DynamicValues
