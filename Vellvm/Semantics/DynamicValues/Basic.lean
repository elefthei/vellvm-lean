module

public import Vellvm.Semantics.Interfaces.Params
public import Vellvm.Numeric.Flocq.Binary

@[expose] public section

namespace Vellvm.Semantics.DynamicValues
open Interfaces.Params Numeric.Integers

abbrev ll_float := Numeric.Flocq.binary_float 24 128
abbrev ll_double := Numeric.Flocq.binary_float 53 1024

inductive memory_bit [Pa : Params] where
  | Bit_ptr (p : Pa.PTR.ptr) (idx : Nat)
  | Bit_psn
  | Bit_bit (b : VellvmIntegers.int1)
export memory_bit (Bit_ptr Bit_psn Bit_bit)

inductive dvalue_bv [Pa : Params] (bit_sz : Positive) where
  | BYTE_Pointer (p : Pa.PTR.ptr) (idx : Nat)
  | BYTE_I (x : bit_int bit_sz)
  | BYTE_Mixed (bits : List memory_bit)
export dvalue_bv (BYTE_Pointer BYTE_I BYTE_Mixed)

inductive dvalue_base [Pa : Params] where
  | DVALUE_Pointer (p : Pa.PTR.ptr)
  | DVALUE_I (sz : Positive) (x : bit_int sz)
  | DVALUE_Iptr (x : Pa.IPTR.iptr)
  | DVALUE_Double (x : ll_double)
  | DVALUE_Float (x : ll_float)
  | DVALUE_Poison
  | DVALUE_None
  | DVALUE_B (sz : Positive) (bv : dvalue_bv sz)
export dvalue_base (DVALUE_Pointer DVALUE_I DVALUE_Iptr DVALUE_Double DVALUE_Float
  DVALUE_Poison DVALUE_None DVALUE_B)

inductive dvalue [Pa : Params] where
  | DVALUE_Base (db : dvalue_base)
  | DVALUE_Struct (packed : Bool) (fields : List dvalue)
  | DVALUE_Array (vector : Bool) (elts : List dvalue)
export dvalue (DVALUE_Base DVALUE_Struct DVALUE_Array)

instance [Params] : Coe dvalue_base dvalue := ⟨DVALUE_Base⟩

end Vellvm.Semantics.DynamicValues
