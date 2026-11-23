import PortChecks.SourceType
import Vellvm.Semantics.Libraries

namespace Vellvm.Semantics.Libraries
open Interfaces.Params Syntax.LLVMAst Syntax.DynamicTypes LLVMEvents Denotation

#source_check "src/rocq/Semantics/Libraries.v|Vellvm.Semantics.Libraries|i8_str_index"
  i8_str_index : ∀ [Pa : Params], Pa.PTR.ptr → Int → CFGtop (Numeric.Integers.bit_int ⟨8, by decide⟩)

#source_check "src/rocq/Semantics/Libraries.v|Vellvm.Semantics.Libraries|putchar_denotation"
  putchar_denotation : ∀ [Pa : Params], function_denotation

#source_check "src/rocq/Semantics/Libraries.v|Vellvm.Semantics.Libraries|puts_denotation"
  puts_denotation : ∀ [Pa : Params], function_denotation

#source_check "src/rocq/Semantics/Libraries.v|Vellvm.Semantics.Libraries|_LIBRARIES"
  _LIBRARIES : ∀ [Pa : Params], List (function_id × function_denotation)

#source_check "src/rocq/Semantics/Libraries.v|Vellvm.Semantics.Libraries|library_functions"
  library_functions : ∀ [Pa : Params], List (declaration dtyp) → List (function_id × function_denotation)

example [Params] : _LIBRARIES =
    [(.Name "puts".toUTF8, puts_denotation), (.Name "putchar".toUTF8, putchar_denotation)] := rfl

example (d : declaration dtyp) :
    selected [{ d with dc_name := .Name "putchar".toUTF8 }, { d with dc_name := .Name "putchar".toUTF8 },
      { d with dc_name := .Anon 0 }, { d with dc_name := .Name "puts".toUTF8 }] =
    [(.Name "puts".toUTF8, .puts), (.Name "putchar".toUTF8, .putchar)] := rfl

example [Pa : Params] (cc : cconv) (rt dt : dtyp) :
    putchar_denotation cc rt [(dt, .DVALUE_Base (.DVALUE_I ⟨32, by decide⟩ (Numeric.Integers.repr 511)))] =
      Sum.inr <$> (do
        io_stdout [Numeric.Integers.repr 255]
        pure (.DVALUE_Base (.DVALUE_I ⟨8, by decide⟩ (Numeric.Integers.repr 255)))
        : CFGtop DynamicValues.dvalue) := rfl

end Vellvm.Semantics.Libraries
