import PortChecks.SourceType
import Vellvm.Semantics.Operations.Conversion

open Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.DynamicValues Vellvm.Semantics.EOU
open Vellvm.Syntax.LLVMAst Vellvm.Syntax.DynamicTypes Vellvm.Semantics.Operations.Conversion
open Vellvm.Semantics.LLVMEvents

#source_check "src/rocq/Semantics/Operations/Conversion.v|Vellvm.Semantics.Operations.Conversion|float_to_double"
  float_to_double : ll_float → ll_double
#source_check "src/rocq/Semantics/Operations/Conversion.v|Vellvm.Semantics.Operations.Conversion|double_to_float"
  double_to_float : ll_double → ll_float
#source_check "src/rocq/Semantics/Operations/Conversion.v|Vellvm.Semantics.Operations.Conversion|convert_pure_base"
  convert_pure_base : ∀ [Pa : Params], pure_conversion → dtyp_base → dvalue_base → dtyp_base → EOU dvalue_base
#source_check "src/rocq/Semantics/Operations/Conversion.v|Vellvm.Semantics.Operations.Conversion|get_base_conversion_type"
  get_base_conversion_type : dtyp → dtyp → Option (dtyp_base × dtyp_base)
#source_check "src/rocq/Semantics/Operations/Conversion.v|Vellvm.Semantics.Operations.Conversion|get_vector_conversion_type"
  get_vector_conversion_type : dtyp → dtyp → Option (dtyp_base × dtyp_base)
#source_check "src/rocq/Semantics/Operations/Conversion.v|Vellvm.Semantics.Operations.Conversion|convert_pure"
  convert_pure : ∀ [Pa : Params], pure_conversion → dtyp → dvalue → dtyp → EOU dvalue
#source_check "src/rocq/Semantics/Operations/Conversion.v|Vellvm.Semantics.Operations.Conversion|convert"
  Vellvm.Semantics.Operations.Conversion.convert : ∀ [Pa : Params], conversion_type → dtyp → dvalue → dtyp → MCFGtop dvalue

open Vellvm.Numeric.Integers
variable [Pa : Params]

-- 255 truncates to signed -1 at both widths, but does not unsigned-round-trip.
example : convert_pure_base (Trunc true false) (DTYPE_I ⟨8, by decide⟩)
    (DVALUE_I ⟨8, by decide⟩ (Vellvm.Numeric.Integers.repr 255)) (DTYPE_I ⟨1, by decide⟩) =
    raise_ret DVALUE_Poison := rfl

example : convert_pure_base (Trunc false true) (DTYPE_I ⟨8, by decide⟩)
    (DVALUE_I ⟨8, by decide⟩ (Vellvm.Numeric.Integers.repr 255)) (DTYPE_I ⟨1, by decide⟩) =
    raise_ret (DVALUE_I ⟨1, by decide⟩ (Vellvm.Numeric.Integers.repr 1)) := rfl
