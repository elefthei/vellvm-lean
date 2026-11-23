import PortChecks.SourceType
import Vellvm.Utils.CTreeUtil

universe u v

#source_check "src/rocq/Utils/ITreeUtil.v|Vellvm.Utils.ITreeUtil|void_elim"
  Vellvm.Utils.CTreeUtil.void_elim : ∀ {A : Type v}, PEmpty.{u+1} → A

#source_check "src/rocq/Utils/ITreeUtil.v|Vellvm.Utils.ITreeUtil|trigger_cast'"
  Vellvm.Utils.CTreeUtil.trigger_cast' : ∀ {E B : ITree.Effect.{u}} {A : Type u} (e : E.I),
    E.O e = PEmpty → CTree.CTree E B A
