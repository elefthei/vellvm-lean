module

public import Vellvm.Semantics.Handlers.Local

@[expose] public section
namespace Vellvm.Semantics.Handlers.Stack
open ITree (Effect Subeffect)
open CTree (CTree)
open Vellvm.Tree Interfaces.Params DynamicValues LLVMEvents Instrumentation Syntax.RawIdMaps
open Local (local_env)

structure stack_frame [Pa : Params] where
  Build_stack_frame ::
  stack_vars : local_env
  stack_exc : Option dvalue
  stack_loc : Option IRString
export stack_frame (Build_stack_frame stack_vars stack_exc stack_loc)

abbrev stack [Params] := List stack_frame

structure debug_local_stack [Pa : Params] where
  mk_debug_local_stack ::
  local_stack_set : stack_frame → Unit
  local_stack_get : Unit → stack
  local_stack_push : stack_frame → Unit
  local_stack_pop : Unit → Unit
export debug_local_stack
  (mk_debug_local_stack local_stack_set local_stack_get local_stack_push local_stack_pop)

def local_stack_object [Pa : Params] : debug_local_stack :=
  ⟨fun _ ↦ (), fun _ ↦ [], fun _ ↦ (), fun _ ↦ ()⟩

def upd_local_sf [Pa : Params] (env : stack_frame) (l : local_env) : stack_frame :=
  { env with stack_vars := l }

abbrev State [Params] := stack_frame × stack
abbrev Effin [Params] (E F G : Effect) := E ⊕ₑ F ⊕ₑ (LocalE ⊕ₑ StackE) ⊕ₑ G
abbrev Effout := Local.Effout

abbrev LocalHandler [Params] (M : Effect → Effect → Type → Type v) (E B : Effect) :=
  (e : LocalE.I) → local_env → M E B (LocalE.O e × local_env)

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M]
variable [Pa : Params] [Diagnostics M] [Snapshots M]

def handle_stack {E B : Effect} [FailureE -< E] (e : StackE.I) (s : State) :
    M E B (StackE.O e × State) :=
  match e with
  | .StackPush args => do
    let vars := args.foldr (fun (k, v) m ↦ RM.add k v m) (RM.empty dvalue)
    let frame : stack_frame := ⟨vars, none, some (get_loc ())⟩
    Snapshots.record (.framePush frame.stack_vars frame.stack_exc)
    pure ((), frame, s.1 :: s.2)
  | .StackPop =>
    match s.2 with
    | [] => LLVMEvents.Worker.«raise» "Tried to pop too many stack frames.".toUTF8
    | frame :: stk => do
      Snapshots.record .framePop
      pure ((), frame, stk)
  | .StackRaise x => pure ((), { s.1 with stack_exc := some x }, s.2)
  | .StackGetExc => pure (s.1.stack_exc, { s.1 with stack_exc := none }, s.2)

def handle_local_stack {E B : Effect} [FailureE -< E] (h : LocalHandler M E B)
    (e : LocalE.I) (s : State) : M E B (LocalE.O e × State) := do
  let (r, vars) ← h e s.1.stack_vars
  let frame := upd_local_sf s.1 vars
  Snapshots.record (.frameSet frame.stack_vars frame.stack_exc)
  pure (r, frame, s.2)

def E_trigger (E F G : Effect) {B : Effect} {S : Type} (e : E.I) (s : S) :
    M (Effout E F G) B (E.O e × S) :=
  StateLaws.Worker.forward (E := Effout E F G) (.inl e) s

def F_trigger (E F G : Effect) {B : Effect} {S : Type} (e : F.I) (s : S) :
    M (Effout E F G) B (F.O e × S) :=
  StateLaws.Worker.forward (E := Effout E F G) (.inr (.inl e)) s

def G_trigger (E F G : Effect) {B : Effect} {S : Type} (e : G.I) (s : S) :
    M (Effout E F G) B (G.O e × S) :=
  StateLaws.Worker.forward (E := Effout E F G) (.inr (.inr e)) s

variable {E F G B : Effect} [FailureE -< Effout E F G]

def interp_local_stack_h (h : LocalHandler M (Effout E F G) B) (e : (Effin E F G).I)
    (s : State) : M (Effout E F G) B ((Effin E F G).O e × State) :=
  match e with
  | .inl x => E_trigger E F G x s
  | .inr (.inl x) => F_trigger E F G x s
  | .inr (.inr (.inl (.inl x))) => handle_local_stack h x s
  | .inr (.inr (.inl (.inr x))) => handle_stack x s
  | .inr (.inr (.inr x)) => G_trigger E F G x s

def interp_local_stack {X : Type} (t : M (Effin E F G) B X) (s : State) :
    M (Effout E F G) B (X × State) :=
  Runtime.interp_state (interp_local_stack_h (Local.Worker.handle_local_debug (M := M))) t s

variable {N : Effect → Effect → Type → Type w} [Runtime N] [Diagnostics N] [Snapshots N]
variable (sim : Simulation M N)

theorem handle_stack_related {E B : Effect} [FailureE -< E] (e : StackE.I) (s : State) :
    sim.R (E := E) (B := B) (handle_stack e s) (handle_stack e s) := by
  cases e with
  | StackPush _ => exact sim.bind (sim.record _) fun _ ↦ sim.pure _
  | StackPop =>
    rcases s with ⟨frame, _ | rest⟩
    · exact sim.«raise» _
    · exact sim.bind (sim.record _) fun _ ↦ sim.pure _
  | StackRaise _ => exact sim.pure _
  | StackGetExc => exact sim.pure _

theorem handle_local_stack_related {E B : Effect} [FailureE -< E]
    {h : LocalHandler M E B} {g : LocalHandler N E B} (hh : ∀ e s, sim.R (h e s) (g e s))
    (e : LocalE.I) (s : State) : sim.R (handle_local_stack h e s) (handle_local_stack g e s) :=
  sim.bind (hh e s.1.stack_vars) fun (_, _) ↦ sim.bind (sim.record _) fun _ ↦ sim.pure _

theorem interp_local_stack_h_related {h : LocalHandler M (Effout E F G) B}
    {g : LocalHandler N (Effout E F G) B} (hh : ∀ e s, sim.R (h e s) (g e s))
    (e : (Effin E F G).I) (s : State) :
    sim.R (interp_local_stack_h h e s) (interp_local_stack_h g e s) := by
  rcases e with e | (f | ((l | st) | g))
  · exact sim.bind (sim.trigger _) fun _ ↦ sim.pure _
  · exact sim.bind (sim.trigger _) fun _ ↦ sim.pure _
  · exact handle_local_stack_related sim hh l s
  · exact handle_stack_related sim st s
  · exact sim.bind (sim.trigger _) fun _ ↦ sim.pure _

/-- Both producer meaning and trace erasure preserve the return value and the entire frame stack. -/
theorem interp_local_stack_related {X} {p : M (Effin E F G) B X} {q : N (Effin E F G) B X}
    (hpq : sim.R p q) (s : State) : sim.R (interp_local_stack p s) (interp_local_stack q s) :=
  sim.state s (interp_local_stack_h_related sim (Local.Worker.handle_local_debug_related sim)) hpq

end Worker

variable [Pa : Params]

def handle_stack {E B : Effect} [FailureE -< E] (e : StackE.I) (s : State) :
    CTree E B (StackE.O e × State) := Worker.handle_stack e s

def handle_local_stack {E B : Effect} [FailureE -< E] (h : LocalHandler CTree E B)
    (e : LocalE.I) (s : State) : CTree E B (LocalE.O e × State) := Worker.handle_local_stack h e s

def E_trigger (E F G : Effect) {B : Effect} {S : Type} (e : E.I) (s : S) :
    CTree (Effout E F G) B (E.O e × S) := Worker.E_trigger E F G e s

def F_trigger (E F G : Effect) {B : Effect} {S : Type} (e : F.I) (s : S) :
    CTree (Effout E F G) B (F.O e × S) := Worker.F_trigger E F G e s

def G_trigger (E F G : Effect) {B : Effect} {S : Type} (e : G.I) (s : S) :
    CTree (Effout E F G) B (G.O e × S) := Worker.G_trigger E F G e s

variable {E F G B : Effect} [FailureE -< Effout E F G]

def interp_local_stack_h (h : LocalHandler CTree (Effout E F G) B) (e : (Effin E F G).I)
    (s : State) : CTree (Effout E F G) B ((Effin E F G).O e × State) :=
  Worker.interp_local_stack_h h e s

def interp_local_stack {X : Type} (t : CTree (Effin E F G) B X) (s : State) :
    CTree (Effout E F G) B (X × State) := Worker.interp_local_stack t s

end Vellvm.Semantics.Handlers.Stack
