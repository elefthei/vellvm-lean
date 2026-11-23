module

public import CTree.Core.Definitions

@[expose] public section
namespace Vellvm.Utils.CTreeUtil

universe u v

def void_elim {A : Type v} : PEmpty.{u+1} → A := nofun

def trigger_cast' {E B : ITree.Effect.{u}} {A : Type u} (e : E.I) (h : E.O e = PEmpty) :
    CTree.CTree E B A :=
  CTree.CTree.trigger e >>= fun x ↦ void_elim (h ▸ x)

end Vellvm.Utils.CTreeUtil
