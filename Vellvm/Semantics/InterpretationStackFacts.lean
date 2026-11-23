import Vellvm.Semantics.InterpretationStack

namespace Vellvm.Semantics
open ITree (Effect)
open Vellvm.Tree Instrumentation Interfaces.Params LLVMEvents Handlers

variable {M : Effect → Effect → Type → Type v} {N : Effect → Effect → Type → Type w}
  [Runtime M] [Runtime N] [Diagnostics M] [Diagnostics N] [Pa : Params] [Snapshots M] [Snapshots N]
  (sim : Simulation M N) {E B : Effect} {X : Type}

namespace Handlers.Memory.Worker
open Implementations.Memory

theorem memM_interpWith_related [FailureE -< E] [OOME -< E] [UBE -< E]
    {p : Chooser Pa M E B} {q : Chooser Pa N E B} (hp : ∀ c, sim.R (p c) (q c))
    (m : ConcreteMem X) (s : State) : sim.R (memM_interpWith p m s) (memM_interpWith q m s) := by
  induction m generalizing s with
  | Mret x => exact sim.pure (x, s)
  | Moom msg => exact sim.raiseOOM msg
  | Mub msg => exact sim.raiseUB msg
  | Merr msg => exact sim.«raise» msg
  | Mget k ih => exact ih s s
  | Mput s' k ih => exact ih () s'
  | Mchoose c k ih =>
    cases c with
    | Cnext_key size align =>
      exact sim.bind (hp (.nextKey s.state_memory_stack.Memory_stack_memory size align))
        (fun addr ↦ ih addr s)
    | Cfresh_prov =>
      exact sim.bind (hp (.fresh s.state_provenance))
        (fun prov ↦ ih prov { s with state_provenance := prov })
    | Cexposed_prov => exact sim.bind (hp .exposed) (fun prov ↦ ih prov s)

end Handlers.Memory.Worker

namespace Handlers.Draw.Worker

theorem handle_drawWith_related [FailureE -< E] [OOME -< E] [UBE -< E]
    {p : Chooser Pa M E B} {q : Chooser Pa N E B} (hp : ∀ c, sim.R (p c) (q c))
    (e : DrawE.I) : sim.R (handle_drawWith p e) (handle_drawWith q e) := by
  cases e with
  | Draw dt =>
    simp only [handle_drawWith]
    split
    · apply hp
    · apply sim.«raise»
    · apply sim.raiseOOM
    · apply sim.raiseUB

end Handlers.Draw.Worker

namespace InterpretationStack.Worker

theorem interp_vellvm_hWith_related {p : Chooser Pa M MCFGEbot B} {q : Chooser Pa N MCFGEbot B}
    (hp : ∀ c, sim.R (p c) (q c)) (e : MCFGEtop.I) (s : FusedS) :
    sim.R (interp_vellvm_hWith p e s) (interp_vellvm_hWith q e s) := by
  rcases s with ⟨mem, ls, g⟩
  rcases e with ext | intr | glob | (loc | stk) | memory | draw | rest
  · exact sim.bind (sim.emit (E := ExternalCallE) ext) fun x ↦ sim.pure (x, mem, ls, g)
  · exact sim.bind (Memory.Worker.memM_interpWith_related sim hp _ mem)
      fun (x, mem') ↦ sim.pure (x, mem', ls, g)
  · exact sim.bind (Global.Worker.handle_global_debug_related sim glob g)
      fun (x, g') ↦ sim.pure (x, mem, ls, g')
  · exact sim.bind (Stack.Worker.handle_local_stack_related sim
      (Local.Worker.handle_local_debug_related sim) loc ls) fun (x, ls') ↦ sim.pure (x, mem, ls', g)
  · exact sim.bind (Stack.Worker.handle_stack_related sim stk ls)
      fun (x, ls') ↦ sim.pure (x, mem, ls', g)
  · exact sim.bind (Memory.Worker.memM_interpWith_related sim hp _ mem)
      fun (x, mem') ↦ sim.pure (x, mem', ls, g)
  · exact sim.bind (Draw.Worker.handle_drawWith_related sim hp draw) fun x ↦ sim.pure (x, mem, ls, g)
  · exact sim.bind (sim.emit (E := OOME ⊕ₑ LLVMExcE ⊕ₑ UBE ⊕ₑ DebugE ⊕ₑ FailureE) rest)
      fun x ↦ sim.pure (x, mem, ls, g)

theorem interp_mcfgWith_related {C : Effect} [C -< B] {p : Chooser Pa M MCFGEbot B}
    {q : Chooser Pa N MCFGEbot B} (hp : ∀ c, sim.R (p c) (q c))
    {t : M MCFGEtop C X} {u : N MCFGEtop C X} (ht : sim.R t u) (s : FusedS) :
    sim.R (interp_mcfgWith p t s) (interp_mcfgWith q u s) :=
  sim.state s (interp_vellvm_hWith_related sim hp) (Intrinsics.Worker.interp_intrinsics_sim sim ht)

theorem interp_mcfg_related {t : M MCFGEtop NoChoice X} {u : N MCFGEtop NoChoice X}
    (ht : sim.R t u) (s : FusedS) : sim.R (interp_mcfg t s) (interp_mcfg u s) :=
  interp_mcfgWith_related sim (p := referenceChooser) (q := referenceChooser)
    (fun c ↦ sim.pure c.reference) ht s

end InterpretationStack.Worker
end Vellvm.Semantics
