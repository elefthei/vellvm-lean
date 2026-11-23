import PortChecks.SourceType
import Vellvm.Semantics.TopLevel.Initialization

namespace Vellvm.Semantics.TopLevel
open Interfaces.Params DynamicValues LLVMEvents Syntax.DynamicTypes Syntax.LLVMAst

#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|allocate_global"
  allocate_global : ∀ [Params], «global» dtyp → MCFGtop Unit
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|allocate_globals"
  allocate_globals : ∀ [Params], List («global» dtyp) → MCFGtop Unit
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|i8"
  i8 : dtyp
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|i8_array_of_string"
  i8_array_of_string : ∀ [Params], IRString → dvalue
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|allocate_arg"
  allocate_arg : ∀ [Params], IRString → MCFGtop dvalue
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|allocate_args"
  allocate_args : ∀ [Params], List IRString → MCFGtop dvalue
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|build_main_args"
  build_main_args : ∀ [Params], List IRString → MCFGtop (List (dtyp × dvalue))
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|allocate_declaration"
  allocate_declaration : ∀ [Params], declaration dtyp → MCFGtop Unit
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|allocate_declarations"
  allocate_declarations : ∀ [Params], List (declaration dtyp) → MCFGtop Unit
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|initialize_global"
  initialize_global : ∀ [Params], «global» dtyp → MCFGtop Unit
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|initialize_globals"
  initialize_globals : ∀ [Params], List («global» dtyp) → MCFGtop Unit
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|allocate_block_address"
  allocate_block_address : ∀ [Params], function_id × block_id → MCFGtop Unit
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|allocate_block_addresses"
  allocate_block_addresses : ∀ [Params], List (function_id × block_id) → MCFGtop Unit
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|block_address_eq_dec"
  block_address_eq_dec : ∀ x y : function_id × block_id, Decidable (x = y)
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|build_global_environment"
  build_global_environment : ∀ [Params], Syntax.CFG.mcfg dtyp → MCFGtop Unit

-- Non-UTF-8 data and embedded NULs survive; only the final NUL is added.
example [Params] : i8_array_of_string ⟨#[255, 0, 65]⟩ =
    DVALUE_Array false (([255, 0, 65, 0] : List Nat).map fun n ↦
      DVALUE_Base (DVALUE_I ⟨8, by decide⟩ (Numeric.Integers.repr n))) := rfl

end Vellvm.Semantics.TopLevel
