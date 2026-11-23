module

public import Vellvm.Semantics.Choices
public import Vellvm.Semantics.Simulation

@[expose] public section
namespace Vellvm.Semantics.Handlers.Memory
open ITree (Effect)
open CTree (CTree)
open Interfaces.Params Interfaces.Memory Implementations.Memory LLVMEvents Tree Instrumentation

abbrev ConcreteMem [Pa : Params] := memS State Pa.PTR.ptr Pa.PROV.provenance

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M] [Diagnostics M] [Pa : Params]
  {E B : Effect} [FailureE -< E] [OOME -< E] [UBE -< E]

def memM_interpWith (choose : Chooser Pa M E B) {X} : ConcreteMem X → State → M E B (X × State)
  | .Mret x, s => pure (x, s)
  | .Moom msg, _ => LLVMEvents.Worker.raiseOOM msg
  | .Merr msg, _ => LLVMEvents.Worker.«raise» msg
  | .Mub msg, _ => LLVMEvents.Worker.raiseUB msg
  | .Mget k, s => memM_interpWith choose (k s) s
  | .Mput s k, _ => memM_interpWith choose (k ()) s
  | .Mchoose (.Cnext_key size align) k, s => do
    let addr ← choose (.nextKey s.state_memory_stack.Memory_stack_memory size align)
    memM_interpWith choose (k addr) s
  | .Mchoose .Cfresh_prov k, s => do
    let p ← choose (.fresh s.state_provenance)
    memM_interpWith choose (k p) { s with state_provenance := p }
  | .Mchoose .Cexposed_prov k, s => do
    let p ← choose .exposed
    memM_interpWith choose (k p) s

end Worker

variable [Pa : Params] {E B : Effect}

def fresh_provenance (s : State) : CTree E B (Pa.PROV.provenance × State) :=
  let p := Pa.PROV.next_provenance s.state_provenance
  pure (p, { s with state_provenance := p })

def memM_interp [FailureE -< E] [OOME -< E] [UBE -< E] {X} (m : ConcreteMem X) (s : State) :
    CTree E B (X × State) := Worker.memM_interpWith referenceChooser m s

end Vellvm.Semantics.Handlers.Memory
