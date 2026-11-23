import Vellvm.Semantics.DynamicValues.Core
import Vellvm.Numeric.Floats.Basic
import Vellvm.Syntax.ShowAST

namespace Vellvm.Semantics.DynamicValues
open Interfaces.Params Numeric.Floats Utils.StringUtil Syntax.ShowAST

/-- Print the exact IEEE representation, including the sign and payload of a NaN. -/
def double_to_hex_string (f : float) : IRString :=
  let n := (Numeric.Integers.unsigned (Float.to_bits f)).toNat
  ⟨(48 :: 120 :: hexNatBytes n).toArray⟩

def float_to_hex_string (f : float32) : IRString := double_to_hex_string (Float32.to_double f)

instance showFloat : Show float := ⟨double_to_hex_string⟩
instance showFloat32 : Show float32 := ⟨float_to_hex_string⟩

variable [Pa : Params]

def show_memory_bit : memory_bit → IRString
  | .Bit_ptr p n => Pa.PTR.show_ptr p ++ lit "[" ++ show_nat n ++ lit "]"
  | .Bit_psn => lit "p"
  | .Bit_bit b => show_Z (Numeric.Integers.unsigned b)

instance showMemoryBit : Show memory_bit := ⟨show_memory_bit⟩

def show_dvalue_bv {sz : Positive} : dvalue_bv sz → IRString
  | .BYTE_Pointer p i => Pa.PTR.show_ptr p ++ lit "[" ++ show_nat i ++ lit "]"
  | .BYTE_I x => show_nat sz.val ++ lit " " ++ show_Z (Numeric.Integers.unsigned x)
  | .BYTE_Mixed bits => lit "[" ++ «show» bits ++ lit "]"

instance showDvalueBV {sz : Positive} : Show (dvalue_bv sz) := ⟨show_dvalue_bv⟩

def show_dvalue_base : dvalue_base → IRString
  | .DVALUE_Pointer a => lit "addr " ++ Pa.PTR.show_ptr a
  | .DVALUE_I sz x => lit "i" ++ show_nat sz.val ++ lit " " ++ show_Z (Numeric.Integers.unsigned x)
  | .DVALUE_Iptr x => lit "intptr " ++ show_Z (Pa.IPTR.to_Z x)
  | .DVALUE_Double x => lit "double " ++ double_to_hex_string x
  | .DVALUE_Float x => lit "float " ++ float_to_hex_string x
  | .DVALUE_Poison => lit "poison"
  | .DVALUE_None => lit "none"
  | .DVALUE_B sz x => lit "b" ++ show_nat sz.val ++ lit " " ++ show_dvalue_bv x

instance showDvalueBase : Show dvalue_base := ⟨show_dvalue_base⟩

def show_dvalue : dvalue → IRString
  | .DVALUE_Base db => show_dvalue_base db
  | .DVALUE_Struct p fs =>
    let fields := concat_str_sep (lit ", ") (fs.map show_dvalue)
    if p then lit "<{" ++ fields ++ lit "}>" else lit "{" ++ fields ++ lit "}"
  | .DVALUE_Array v es =>
    let elts := concat_str_sep (lit ", ") (es.map show_dvalue)
    if v then lit "< " ++ elts ++ lit ">" else lit "[" ++ elts ++ lit "]"

instance showDValue : Show dvalue := ⟨show_dvalue⟩

end Vellvm.Semantics.DynamicValues
