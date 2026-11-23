module

public import Vellvm.Tree.ExecutionMrec
public import Vellvm.Tree.ExecutionState
public import CTree.Interp.RecursionFacts
public import CTree.Interp.FoldStateT

@[expose] public section
namespace Vellvm.Tree
open ITree (Effect Subeffect)
open CTree (CTree)

universe u v

@[implicit_reducible] def NoChoice : Effect.{u} := ⟨PEmpty, fun _ ↦ PEmpty⟩

/-- Workers are polymorphic in the presentation; result and cursor-state universes are separate. -/
class Runtime (M : Effect.{u} → Effect.{u} → Type u → Type v) where
  monad {E B} : Monad (M E B)
  trigger {E B} (e : E.I) : M E B (E.O e)
  branch {E B} (c : B.I) : M E B (B.O c)
  iter {E B X Y} (body : X → M E B (X ⊕ Y)) (x : X) : M E B Y
  translate {E F B X} (h : (e : E.I) → (f : F.I) × (F.O f → E.O e)) (t : M E B X) : M F B X
  interp {E F B D X} [B -< D] (h : (e : E.I) → M F D (E.O e)) (t : M E B X) : M F D X
  interp_state {E F B D X S} [B -< D] (h : (e : E.I) → S → M F D (E.O e × S))
    (t : M E B X) (st : S) : M F D (X × S)
  interp_mrec {D E B X} (ctx : (d : D.I) → M (D ⊕ₑ E) B (D.O d)) (t : M (D ⊕ₑ E) B X) : M E B X

attribute [instance 90] Runtime.monad

instance : Runtime CTree where
  monad := inferInstance
  trigger := CTree.trigger
  branch := CTree.branch
  iter := CTree.iter
  translate := CTree.translate
  interp := CTree.interp
  interp_state := CTree.interp_state
  interp_mrec := CTree.interp_mrec

instance : Runtime Producer where
  monad := { pure := Producer.ret, bind := Producer.bind }
  trigger := Producer.trigger
  branch := Producer.branch
  iter := Producer.iter
  translate := Producer.translate
  interp := Producer.interp
  interp_state := Producer.interp_state
  interp_mrec := Producer.interp_mrec

namespace Runtime
variable {M : Effect.{u} → Effect.{u} → Type u → Type v} [Runtime M]

def emit {E F B : Effect.{u}} [i : E -< F] (e : E.I) : M F B (E.O e) :=
  let ⟨f, back⟩ := i.map e
  back <$> trigger f

end Runtime
end Vellvm.Tree
