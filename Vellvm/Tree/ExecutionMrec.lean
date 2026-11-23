module

public import Vellvm.Tree.Execution

@[expose] public section
namespace Vellvm.Tree.Producer
open ITree (Effect)
open CTree (CTreeF)

universe u
variable {D E B : Effect.{u}} {X : Type u}

namespace Mrec

/-- `none` is the root; `some d` is executing the body of request `d`. -/
abbrev Answer (D : Effect.{u}) (X : Type u) : Option D.I → Type u
  | none => X
  | some d => D.O d

variable (ctx : (d : D.I) → Producer (D ⊕ₑ E) B (D.O d)) (root : Producer (D ⊕ₑ E) B X)

def body : (i : Option D.I) → Producer (D ⊕ₑ E) B (Answer D X i)
  | none => root
  | some d => ctx d

inductive Stack : Option D.I → Type u where
  | done : Stack none
  | push {i} (d : D.I) (caller : CachedNext (body ctx root i))
      (resume : D.O d → (body ctx root i).S) (rest : Stack i) : Stack (some d)

structure Cursor where
  pendingGuard : Bool
  {frame : Option D.I}
  stack : Stack ctx root frame
  transition : CachedNext (body ctx root frame)
  state : (body ctx root frame).S

/-- A return can resume the caller immediately: each such pop removes one frame. -/
def run {i} (st : Stack ctx root i) (transition : CachedNext (body ctx root i))
    (s : (body ctx root i).S) : CTreeF E B X (Cursor ctx root) :=
  match transition.val s with
  | .ret x => match st with
    | .done => .ret x
    | .push _ caller k rest => run rest caller (k x)
  | .stuck => .stuck
  | .guard j => .guard ⟨false, st, transition, j⟩
  | .step j => .step ⟨true, st, transition, j⟩
  | .br b k => .br b fun a ↦ ⟨true, st, transition, k a⟩
  | .vis (.inr e) k => .vis e fun a ↦ ⟨true, st, transition, k a⟩
  | .vis (.inl d) k =>
    let callee := ctx d
    .guard ⟨false, .push d transition k st, ⟨callee.next, rfl⟩, callee.initial⟩
termination_by structural st

def next : Cursor ctx root → CTreeF E B X (Cursor ctx root)
  | ⟨true, st, t, s⟩ => .guard ⟨false, st, t, s⟩
  | ⟨false, st, t, s⟩ => run ctx root st t s

end Mrec

def interp_mrec (ctx : (d : D.I) → Producer (D ⊕ₑ E) B (D.O d))
    (root : Producer (D ⊕ₑ E) B X) : Producer E B X :=
  ⟨Mrec.Cursor ctx root, ⟨false, .done, ⟨root.next, rfl⟩, root.initial⟩, Mrec.next ctx root⟩

def mrec (ctx : (d : D.I) → Producer (D ⊕ₑ E) B (D.O d)) (d : D.I) :
    Producer E B (D.O d) := interp_mrec ctx (ctx d)

end Vellvm.Tree.Producer
