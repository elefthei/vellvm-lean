import PortChecks.SourceType
import PortChecks.Semantics.TopLevel.Initialization
import Vellvm.Semantics.TopLevel

namespace Vellvm.Semantics.TopLevel
open Interfaces.Params Syntax.LLVMAst Syntax.CFG Syntax.DynamicTypes DynamicValues
open LLVMEvents (MCFGtop MCFGbot)
open InterpretationStack (Res)
open Implementations.IPtrInfinite

#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|ll_toplevel_entity"
  ll_toplevel_entity : Type
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|ll_toplevel_entities"
  ll_toplevel_entities : Type
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|PREDEFINED_FUNCTIONS"
  PREDEFINED_FUNCTIONS : ll_toplevel_entities
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|userdecl_defined_in"
  userdecl_defined_in : IRString → ll_toplevel_entities → Bool
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|decl_defined_in"
  decl_defined_in : ll_toplevel_entity → ll_toplevel_entities → Bool
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|defines_decl"
  defines_decl : ll_toplevel_entities → ll_toplevel_entity → Bool
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|link"
  link : ll_toplevel_entities → ll_toplevel_entities → ll_toplevel_entities
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|link_all"
  link_all : List ll_toplevel_entities → ll_toplevel_entities → ll_toplevel_entities
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|address_one_function"
  address_one_function : ∀ [Pa : Params], definition dtyp (cfg dtyp) → MCFGtop (Int × Denotation.function_denotation)
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|address_one_library_function"
  address_one_library_function : ∀ [Pa : Params], function_id × Denotation.function_denotation →
    MCFGtop (Int × Denotation.function_denotation)
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|denote_vellvm"
  denote_vellvm : ∀ [Pa : Params], dtyp → function_id → List (dtyp × dvalue) → mcfg dtyp → MCFGtop dvalue
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|interpreter_gen"
  interpreter_gen : ∀ [Pa : Params], dtyp → function_id → MCFGtop (List (dtyp × dvalue)) →
    ll_toplevel_entities → MCFGbot (Res dvalue)
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|interpreter_param"
  interpreter_param : ∀ [Pa : Params], List IRString → ll_toplevel_entities → MCFGbot (Res dvalue)

local instance : Params := @Implementations.ParamsV.ParamsV IPZ IPZTheory
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|interpreter"
  interpreter : List IRString → ll_toplevel_entities → MCFGbot (Res dvalue)
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|dvalue_eqb"
  dvalue_eqb : dvalue → dvalue → Bool
#source_check "src/rocq/Semantics/TopLevel.v|Vellvm.Semantics.TopLevel|dvalue_is_canonical"
  dvalue_is_canonical : dtyp → dvalue → Bool

end Vellvm.Semantics.TopLevel
