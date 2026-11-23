import PortChecks.SourceType
import Vellvm.Utils.BoolUtil

universe u

#source_check "src/rocq/Utils/BoolUtil.v|Vellvm.Utils.BoolUtil|option_pred"
  Vellvm.Utils.BoolUtil.option_pred : ∀ {A : Type u}, (A → Bool) → Option A → Bool
