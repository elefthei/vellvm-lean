import PortChecks.SourceType
import Vellvm.Semantics.DynamicValues.Show

open Vellvm Vellvm.Semantics.DynamicValues Vellvm.Semantics.Interfaces.Params
open Vellvm.Utils.StringUtil Vellvm.Numeric.Floats

#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|showFloat"
  showFloat : Show float
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|showFloat32"
  showFloat32 : Show float32
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|showMemoryBit"
  showMemoryBit : ∀ [Pa : Params], Show memory_bit
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|showDvalueBV"
  showDvalueBV : ∀ [Pa : Params] {sz : Positive}, Show (dvalue_bv sz)
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|showDvalueBase"
  showDvalueBase : ∀ [Pa : Params], Show dvalue_base
#source_check "src/rocq/Semantics/DynamicValues.v|Vellvm.Semantics.DynamicValues|showDValue"
  showDValue : ∀ [Pa : Params], Show dvalue
