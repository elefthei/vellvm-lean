import PortChecks.SourceType
import Vellvm.Utils.Tactics

universe u v

#source_check "src/rocq/Utils/Tactics.v|Vellvm.Utils.Tactics|inj_pair2"
  Vellvm.Utils.Tactics.inj_pair2 : ∀ (U : Type u) (P : U → Type v) (p : U) (x y : P p),
    (⟨p, x⟩ : Sigma P) = ⟨p, y⟩ → x = y
