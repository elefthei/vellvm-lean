import PortChecks.SourceType
import Vellvm.Syntax.LLVMAst

open Vellvm.Syntax.LLVMAst

#source_check "src/rocq/Syntax/LLVMAst.v|Vellvm.Syntax.LLVMAst|internal_floating_point_variant_dec_bl"
  internal_floating_point_variant_dec_bl : ∀ x y : floating_point_variant,
    floating_point_variant_beq x y = true → x = y

#source_check "src/rocq/Syntax/LLVMAst.v|Vellvm.Syntax.LLVMAst|internal_floating_point_variant_dec_lb"
  internal_floating_point_variant_dec_lb : ∀ {x y : floating_point_variant},
    x = y → floating_point_variant_beq x y = true
