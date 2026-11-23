import PortChecks.SourceType
import Vellvm.Utils.OptionUtil

universe u

#source_check "src/rocq/Utils/OptionUtil.v|Vellvm.Utils.OptionUtil|from_option"
  Vellvm.Utils.OptionUtil.from_option : ∀ {A : Type u}, A → Option A → A
