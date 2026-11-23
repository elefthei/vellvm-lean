import Vellvm.Semantics.Denotation
import PortChecks.SourceType

namespace Vellvm.Semantics.Denotation
open Syntax.LLVMAst

#source_check "src/rocq/Semantics/Denotation.v|Vellvm.Semantics.Denotation|indirectbr_target_In"
  indirectbr_target_In : ∀ (z : Int) (brs : List block_id) (addrs : List (Option Int)) {b : block_id},
    indirectbr_target z (brs.zip addrs) = some b → b ∈ brs

end Vellvm.Semantics.Denotation
