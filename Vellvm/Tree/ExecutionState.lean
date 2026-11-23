module

public import Vellvm.Tree.Execution

/-! # Productive interpretation of event handlers -/

@[expose] public section
namespace Vellvm.Tree.Producer
open ITree (Effect Subeffect)
open CTree (CTreeF)

universe u
variable {E F B D : Effect.{u}} {X St : Type u}

/-- A pending handler remembers its own cursor and where to return in the source. -/
inductive InterpCursor (h : (e : E.I) → Producer F D (E.O e)) (A : Type u) : Type u where
  | source (s : A)
  | afterAction (s : A)
  | pending (e : E.I) (resume : E.O e → A) (next : CachedNext (h e)) (s : (h e).S)

namespace InterpCursor

@[inline] def handlerHead (h : (e : E.I) → Producer F D (E.O e)) {A : Type u}
    (e : E.I) (k : E.O e → A) (n : CachedNext (h e)) (s : (h e).S) :
    CTreeF F D X (InterpCursor h A) :=
  match n.val s with
  | .ret x => .guard (.source (k x))
  | .stuck => .stuck
  | .guard j => .guard (.pending e k n j)
  | .step j => .step (.pending e k n j)
  | .vis f l => .vis f fun a ↦ .pending e k n (l a)
  | .br c l => .br c fun a ↦ .pending e k n (l a)

end InterpCursor

/-- Run a handler to completion, exposing each of its heads before resuming the source.
The fold also guards the continuation of a source step or branch, but not a handler step or branch. -/
def interp [sub : B -< D] (h : (e : E.I) → Producer F D (E.O e)) (p : Producer E B X) :
    Producer F D X where
  S := InterpCursor h p.S
  initial := .source p.initial
  next
    | .pending e k n s => InterpCursor.handlerHead h e k n s
    | .afterAction s => .guard (.source s)
    | .source s => match p.next s with
      | .ret x => .ret x
      | .stuck => .stuck
      | .guard j => .guard (.source j)
      | .step j => .step (.afterAction j)
      | .br b k => let ⟨c, back⟩ := sub.map b; .br c fun a ↦ .afterAction (k (back a))
      | .vis e k =>
        let handler := h e
        InterpCursor.handlerHead h e k ⟨handler.next, rfl⟩ handler.initial

/-- The state supplied to a handler is part of its request; its answer carries the new state. -/
abbrev StateRequest (E : Effect.{u}) (St : Type u) : Effect.{u} :=
  ⟨E.I × St, fun es ↦ E.O es.1 × St⟩

@[inline] def stateInput (p : Producer E B X) (st : St) : Producer (StateRequest E St) B (X × St) where
  S := p.S × St
  initial := (p.initial, st)
  next := fun (i, s) ↦ match p.next i with
    | .ret x => .ret (x, s)
    | .stuck => .stuck
    | .guard j => .guard (j, s)
    | .step j => .step (j, s)
    | .br b k => .br b fun a ↦ (k a, s)
    | .vis e k => .vis (e, s) fun xs ↦ (k xs.1, xs.2)

def interp_state [B -< D] (h : (e : E.I) → St → Producer F D (E.O e × St))
    (p : Producer E B X) (s : St) : Producer F D (X × St) :=
  interp (E := StateRequest E St) (fun es ↦ h es.1 es.2) (stateInput p s)

end Vellvm.Tree.Producer
