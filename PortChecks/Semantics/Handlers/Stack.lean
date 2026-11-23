import PortChecks.SourceType
import Vellvm.Semantics.Handlers.Stack
import Vellvm.Tree.Logged

open ITree (Effect Subeffect)
open CTree (CTree)
open Vellvm Vellvm.Tree Vellvm.Semantics Vellvm.Semantics.Interfaces.Params
open DynamicValues LLVMEvents Handlers.Stack Syntax.LLVMAst Syntax.RawIdMaps
open Handlers.Local (local_env)

#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|stack_frame"
  stack_frame : ∀ [Pa : Params], Type
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|Build_stack_frame"
  Build_stack_frame : ∀ [Pa : Params], local_env → Option dvalue → Option IRString → stack_frame
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|stack_vars"
  stack_vars : ∀ [Pa : Params], stack_frame → local_env
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|stack_exc"
  stack_exc : ∀ [Pa : Params], stack_frame → Option dvalue
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|stack_loc"
  stack_loc : ∀ [Pa : Params], stack_frame → Option IRString
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|stack"
  stack : ∀ [Pa : Params], Type
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|debug_local_stack"
  debug_local_stack : ∀ [Pa : Params], Type
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|mk_debug_local_stack"
  mk_debug_local_stack : ∀ [Pa : Params], (stack_frame → Unit) → (Unit → stack) →
    (stack_frame → Unit) → (Unit → Unit) → debug_local_stack
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|local_stack_set"
  local_stack_set : ∀ [Pa : Params], debug_local_stack → stack_frame → Unit
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|local_stack_get"
  local_stack_get : ∀ [Pa : Params], debug_local_stack → Unit → stack
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|local_stack_push"
  local_stack_push : ∀ [Pa : Params], debug_local_stack → stack_frame → Unit
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|local_stack_pop"
  local_stack_pop : ∀ [Pa : Params], debug_local_stack → Unit → Unit
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|local_stack_object"
  local_stack_object : ∀ [Pa : Params], debug_local_stack
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|upd_local_sf"
  upd_local_sf : ∀ [Pa : Params], stack_frame → local_env → stack_frame

private abbrev SState [Params] := stack_frame × List stack_frame
private abbrev InRow [Params] (E F G : Effect) := E ⊕ₑ F ⊕ₑ (LocalE ⊕ₑ StackE) ⊕ₑ G
private abbrev OutRow (E F G : Effect) := E ⊕ₑ F ⊕ₑ G
private abbrev Loc [Params] (E B : Effect) :=
  (e : LocalE.I) → local_env → CTree E B (LocalE.O e × local_env)

#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|handle_stack"
  handle_stack : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] (e : StackE.I),
    SState → CTree E B (StackE.O e × SState)
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|handle_local_stack"
  handle_local_stack : ∀ [Pa : Params] {E B : Effect} [FailureE -< E], Loc E B →
    (e : LocalE.I) → SState → CTree E B (LocalE.O e × SState)
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|E_trigger"
  E_trigger : ∀ (E F G : Effect.{0}) {B : Effect.{0}} {S : Type} (e : E.I),
    S → CTree (OutRow E F G) B (E.O e × S)
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|F_trigger"
  F_trigger : ∀ (E F G : Effect.{0}) {B : Effect.{0}} {S : Type} (e : F.I),
    S → CTree (OutRow E F G) B (F.O e × S)
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|G_trigger"
  G_trigger : ∀ (E F G : Effect.{0}) {B : Effect.{0}} {S : Type} (e : G.I),
    S → CTree (OutRow E F G) B (G.O e × S)
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|interp_local_stack_h"
  interp_local_stack_h : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< OutRow E F G],
    Loc (OutRow E F G) B → (e : (InRow E F G).I) → SState →
    CTree (OutRow E F G) B ((InRow E F G).O e × SState)
#source_check "src/rocq/Semantics/Handlers/Stack.v|Vellvm.Semantics.Handlers.Stack|interp_local_stack"
  interp_local_stack : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< OutRow E F G] {X : Type},
    CTree (InRow E F G) B X → SState → CTree (OutRow E F G) B (X × SState)

variable [Pa : Params]

-- A push snapshots the new frame, not its caller. The leftmost duplicate binding wins.
example (s : SState) (key : raw_id) (a b : dvalue) :
    let vars := RM.add key a (RM.add key b (RM.empty dvalue))
    let frame : stack_frame := ⟨vars, none, some .empty⟩
    let p := Handlers.Stack.Worker.handle_stack (M := Logged) (E := FailureE) (B := NoChoice)
      (.StackPush [(key, a), (key, b)]) s
    ∃ k, p.next p.initial = .vis (.inr (.framePush vars none)) k ∧
      p.next (k ()) = .ret ((), frame, s.1 :: s.2) ∧ RM.find key vars = some a :=
  ⟨_, rfl, rfl, by simp⟩

-- A successful local write updates the locals view before the debugger's top stack frame.
example (s : SState) (key : raw_id) (v : dvalue) :
    let vars := RM.add key v s.1.stack_vars
    let p := Handlers.Stack.Worker.handle_local_stack (M := Logged) (E := FailureE) (B := NoChoice)
      (Handlers.Local.Worker.handle_local_debug (M := Logged)) (.LocalWrite key v) s
    ∃ k l, p.next p.initial = .vis (.inr (.locals vars)) k ∧
      p.next (k ()) = .vis (.inr (.frameSet vars s.1.stack_exc)) l ∧
      p.next (l ()) = .ret ((), upd_local_sf s.1 vars, s.2) := ⟨_, _, rfl, rfl, rfl⟩

-- Underflow reports its diagnostic before failure; it never reports a successful frame pop.
example (f : stack_frame) :
    let p := Handlers.Stack.Worker.handle_stack (M := Logged) (E := FailureE) (B := NoChoice)
      .StackPop (f, [])
    ∃ k l, p.next p.initial = .vis (.inr (.diagnostic "Tried to pop too many stack frames.".toUTF8)) k ∧
      p.next (k ()) = .vis (.inl (.Throw ())) l := ⟨_, _, rfl, rfl⟩

example (f caller : stack_frame) (rest : stack) :
    let p := Handlers.Stack.Worker.handle_stack (M := Logged) (E := FailureE) (B := NoChoice)
      .StackPop (f, caller :: rest)
    ∃ k, p.next p.initial = .vis (.inr .framePop) k ∧ p.next (k ()) = .ret ((), caller, rest) :=
  ⟨_, rfl, rfl⟩

-- Raising and reading change no debugger state. The first read returns and clears the payload.
example (s : SState) (x : dvalue) :
    let p : Logged FailureE NoChoice (Option dvalue × Option dvalue × SState) := do
      let (_, s) ← Handlers.Stack.Worker.handle_stack (.StackRaise x) s
      let (first, s) ← Handlers.Stack.Worker.handle_stack .StackGetExc s
      let (second, s) ← Handlers.Stack.Worker.handle_stack .StackGetExc s
      pure (first, second, s)
    p.next p.initial = .ret (some x, none, { s.1 with stack_exc := none }, s.2) := rfl
