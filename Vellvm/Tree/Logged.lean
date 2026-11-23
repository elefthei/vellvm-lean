module

public import Vellvm.Semantics.Instrumentation
public import Vellvm.Tree.Catch

@[expose] public section
namespace Vellvm.Tree
open ITree (Effect Subeffect)
open Semantics Interfaces.Params Instrumentation

/-- The additional summand belongs to the debugger, not to the LLVM signature. -/
def Logged [Pa : Params] (E B : Effect) (X : Type) := Producer (E ⊕ₑ Trace) B X

namespace Logged
variable [Pa : Params] {D E F B C : Effect} {S X : Type}

@[inline] def trace (request : TraceRequest) : Logged E B Unit :=
  Producer.trigger (E := E ⊕ₑ Trace) (.inr request)

/-- Relabel the worker row, leaving the private row and its answers untouched. -/
def liftMap (h : (e : E.I) → (f : F.I) × (F.O f → E.O e)) :
    (e : (E ⊕ₑ Trace).I) → (f : (F ⊕ₑ Trace).I) × ((F ⊕ₑ Trace).O f → (E ⊕ₑ Trace).O e)
  | .inl e => let ⟨f, back⟩ := h e; ⟨.inl f, back⟩
  | .inr r => ⟨.inr r, id⟩

/-- `interp_mrec` recognizes recursive requests only in the first summand. -/
def reassoc : (e : ((D ⊕ₑ E) ⊕ₑ Trace).I) →
    (f : (D ⊕ₑ (E ⊕ₑ Trace)).I) × ((D ⊕ₑ (E ⊕ₑ Trace)).O f → ((D ⊕ₑ E) ⊕ₑ Trace).O e)
  | .inl (.inl d) => ⟨.inl d, id⟩
  | .inl (.inr e) => ⟨.inr (.inl e), id⟩
  | .inr r => ⟨.inr (.inr r), id⟩

def forward (h : (e : E.I) → Logged F C (E.O e)) :
    (e : (E ⊕ₑ Trace).I) → Logged F C ((E ⊕ₑ Trace).O e)
  | .inl e => h e
  | .inr r => trace r

def forwardState (h : (e : E.I) → S → Logged F C (E.O e × S)) :
    (e : (E ⊕ₑ Trace).I) → S → Logged F C ((E ⊕ₑ Trace).O e × S)
  | .inl e, s => h e s
  | .inr r, s => Producer.bind (trace (E := F) r) fun _ ↦ Producer.ret ((), s)

instance : Runtime (Logged (Pa := Pa)) where
  monad := { pure := Producer.ret, bind := Producer.bind }
  trigger {E B} e := Producer.trigger (E := E ⊕ₑ Trace) (.inl e)
  branch := Producer.branch
  iter := Producer.iter
  translate := fun h ↦ Producer.translate (liftMap h)
  interp := fun h ↦ Producer.interp (forward h)
  interp_state := fun h ↦ Producer.interp_state (forwardState h)
  interp_mrec := fun ctx t ↦ Producer.interp_mrec
    (fun d ↦ Producer.translate reassoc (ctx d)) (Producer.translate reassoc t)

/-- A catch can interrupt public events; it cannot consume a debugger update. -/
def selectPublic (select : E.I → Option X) : (E ⊕ₑ Trace).I → Option X
  | .inl e => select e
  | .inr _ => none

instance : Catch (Logged (Pa := Pa)) where
  run select t := Catch.producerRun (selectPublic select) t

instance : Diagnostics (Logged (Pa := Pa)) where
  setLoc loc := trace (.setLoc loc)
  diagnostic bytes := trace (.diagnostic bytes)

instance : Snapshots (Logged (Pa := Pa)) where
  record := trace

end Logged
end Vellvm.Tree
