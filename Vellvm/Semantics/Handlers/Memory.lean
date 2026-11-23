import Vellvm.Semantics.Handlers.Memory.Selection
import Vellvm.Semantics.Implementations.Memory

namespace Vellvm.Semantics.Handlers.Memory
open ITree (Effect)
open CTree (CTree)
open Interfaces.Params LLVMEvents Implementations.Memory Tree

variable [Pa : Params] {E G B : Effect}

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M]

def handle_memory (h : {X : Type} → ConcreteMem X → State → M E B (X × State))
    (e : MemoryE.I) := h (handle_memoryM (MMP := MemoryModelPrimitivesV) e)

def handle_intrinsic (h : {X : Type} → ConcreteMem X → State → M E B (X × State))
    (e : IntrinsicE.I) := h (handle_intrinsicM (MMP := MemoryModelPrimitivesV) e)

end Worker

def handle_memory (h : {X : Type} → ConcreteMem X → State → CTree E B (X × State))
    (e : MemoryE.I) := Worker.handle_memory h e

def handle_intrinsic (h : {X : Type} → ConcreteMem X → State → CTree E B (X × State))
    (e : IntrinsicE.I) := Worker.handle_intrinsic h e

def E_trigger (E G : Effect) {S : Type} (e : E.I) (s : S) : CTree (E ⊕ₑ G) B (E.O e × S) := do
  return (← CTree.trigger' E e, s)
def G_trigger (E G : Effect) {S : Type} (g : G.I) (s : S) : CTree (E ⊕ₑ G) B (G.O g × S) := do
  return (← CTree.trigger' G g, s)

abbrev Input [Params] (E G : Effect) := E ⊕ₑ IntrinsicE ⊕ₑ MemoryE ⊕ₑ G
variable [FailureE -< G] [UBE -< G] [OOME -< G]

def interp_memory_h (e : (Input E G).I) (s : State) : CTree (E ⊕ₑ G) B ((Input E G).O e × State) :=
  match e with
  | .inl f => E_trigger E G f s
  | .inr (.inl i) => handle_intrinsic (fun m st ↦ memM_interp m st) i s
  | .inr (.inr (.inl m)) => handle_memory (fun m st ↦ memM_interp m st) m s
  | .inr (.inr (.inr g)) => G_trigger E G g s

def interp_memory {X} (t : CTree (Input E G) B X) (s : State) : CTree (E ⊕ₑ G) B (X × State) :=
  CTree.interp_state (interp_memory_h (E := E) (G := G)) t s

end Vellvm.Semantics.Handlers.Memory
