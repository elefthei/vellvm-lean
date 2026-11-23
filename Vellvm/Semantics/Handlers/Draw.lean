module

public import Vellvm.Semantics.Choices
public import CTree.Interp.FoldCTree

@[expose] public section
namespace Vellvm.Semantics.Handlers.Draw
open ITree (Effect)
open CTree (CTree)
open Tree Instrumentation Interfaces.Params LLVMEvents DynamicValues

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M] [Diagnostics M] [Pa : Params]
  {E B : Effect} [FailureE -< E] [OOME -< E] [UBE -< E]

def handle_drawWith (choose : Chooser Pa M E B) : (e : DrawE.I) → M E B (DrawE.O e)
  | .Draw dt => match h : default_dvalue_of_dtyp dt with
    | .raise_ret v => choose (.draw dt v h)
    | .raise_error s => LLVMEvents.Worker.«raise» s
    | .raise_oom s => LLVMEvents.Worker.raiseOOM s
    | .raise_ub s => LLVMEvents.Worker.raiseUB s
end Worker

variable [Pa : Params] {E G B : Effect}

def handle_draw [FailureE -< E] [OOME -< E] [UBE -< E] (e : DrawE.I) : CTree E B (DrawE.O e) :=
  Worker.handle_drawWith referenceChooser e

def E_trigger (G : Effect) (e : E.I) : CTree (E ⊕ₑ G) B (E.O e) := CTree.trigger' E e
def G_trigger (E : Effect) (g : G.I) : CTree (E ⊕ₑ G) B (G.O g) := CTree.trigger' G g

variable [FailureE -< G] [OOME -< G] [UBE -< G]

def interp_draw_h (e : (E ⊕ₑ DrawE ⊕ₑ G).I) : CTree (E ⊕ₑ G) B ((E ⊕ₑ DrawE ⊕ₑ G).O e) :=
  match e with
  | .inl f => E_trigger G f
  | .inr (.inl d) => handle_draw d
  | .inr (.inr g) => G_trigger E g

def interp_draw {X} (t : CTree (E ⊕ₑ DrawE ⊕ₑ G) B X) : CTree (E ⊕ₑ G) B X :=
  CTree.interp (interp_draw_h (E := E) (G := G)) t

end Vellvm.Semantics.Handlers.Draw
