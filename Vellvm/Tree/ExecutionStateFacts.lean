module

public import Vellvm.Tree.ExecutionState
public import CTree.Interp.FoldStateT

/-! # Head-for-head adequacy of productive interpretation -/

@[expose] public section
namespace Vellvm.Tree.Producer
open ITree (Effect Subeffect)
open CTree (CTree CTreeF)
open Coinductive (PF)
open Coinduction

universe u
variable {E F B D : Effect.{u}} {X St : Type u}

namespace InterpCursor
variable (h : (e : E.I) → Producer F D (E.O e)) (p : Producer E B X)

/-- Meaning of a paused cursor, given the public interpretation of each source position. -/
def reference (den : p.S → CTree F D X) : InterpCursor h p.S → CTree F D X
  | .source i => den i
  | .afterAction i => (den i).guard
  | .pending e k _ s => (h e).meaningAt s >>= fun a ↦ (den (k a)).guard

private def sourceHead [B -< D] (den : p.S → CTree F D X) : CTreeF E B X p.S → CTree F D X
  | .ret x => .ret x
  | .stuck => .stuck
  | .guard j => (den j).guard
  | .step j => (den j).guard.step
  | .vis e k => (h e).meaning >>= fun a ↦ (den (k a)).guard
  | .br b k => .br' b fun a ↦ (den (k a)).guard

private theorem handler_unfold (den : p.S → CTree F D X) (e : E.I) (k : E.O e → p.S)
    (n : CachedNext (h e)) (s : (h e).S) :
    ((h e).meaningAt s >>= fun a ↦ (den (k a)).guard).unfold =
      PF.map (CTreeF F D X) (reference h p den) (handlerHead h e k n s) := by
  rw [CTree.unfold_bind, observe_meaningAt]
  simp only [handlerHead, n.property]
  cases (h e).next s <;> first | exact CTree.unfold_guard _ | rfl

private theorem reference_unfold [sub : B -< D] (den : p.S → CTree F D X)
    (step : ∀ i, den i = sourceHead h p den (p.next i)) (c : InterpCursor h p.S) :
    (reference h p den c).unfold =
      PF.map (CTreeF F D X) (reference h p den) ((interp h p).next c) := by
  cases c with
  | pending e k n s => exact handler_unfold h p den e k n s
  | afterAction i => exact CTree.unfold_guard _
  | source i =>
    change (den i).unfold = _
    rw [step i]
    cases hn : p.next i with
    | vis e k =>
      simpa only [interp, hn, sourceHead, meaning] using
        handler_unfold h p den e k ⟨(h e).next, rfl⟩ (h e).initial
    | br b k =>
      simp only [sourceHead, CTree.br', CTree.unfold_br, interp, hn]
      rfl
    | _ => simp only [interp, hn, sourceHead, CTree.unfold_ret, CTree.unfold_stuck,
               CTree.unfold_guard, CTree.unfold_step] <;> rfl

/-- The proof matches guards, rather than invoking a stuttering or handler-congruence rule. -/
private theorem adequate [B -< D] (den : p.S → CTree F D X)
    (step : ∀ i, den i = sourceHead h p den (p.next i)) (bL bR : Bool) :
    ∀ c, eqit Eq bL bR ((interp h p).meaningAt c) (reference h p den c) := by
  coinduction R hR ih
  intro c
  change Layer _ R _ _
  rw [observe_meaningAt, reference_unfold h p den step c]
  cases (interp h p).next c with
  | ret _ => exact .ret rfl
  | stuck => exact .stuck
  | guard s => exact .guard (ih s)
  | step s => exact .step (ih s)
  | br b k => exact .br fun a ↦ ih (k a)
  | vis f k =>
    refine .vis rfl fun a b hab ↦ ?_
    cases eq_of_heq hab
    exact ih (k a)

end InterpCursor

/-- Also covers pending handlers and the continuation immediately after an observable action. -/
theorem interp_meaningAt [B -< D] (h : (e : E.I) → Producer F D (E.O e)) (p : Producer E B X)
    (c : InterpCursor h p.S) (bL bR : Bool) : eqit Eq bL bR ((interp h p).meaningAt c)
      (InterpCursor.reference h p (fun i ↦ CTree.interp (fun e ↦ (h e).meaning) (p.meaningAt i)) c) := by
  apply InterpCursor.adequate
  intro i
  rw [CTree.unfold_interp, observe_meaningAt]
  cases p.next i <;> first | rfl |
    (simp [InterpCursor.sourceHead, CTree.mbr, CTree.branch', CTree.br']; rfl)

theorem interp_meaning [B -< D] (h : (e : E.I) → Producer F D (E.O e)) (p : Producer E B X) :
    eutt Eq (interp h p).meaning (CTree.interp (fun e ↦ (h e).meaning) p.meaning) :=
  interp_meaningAt h p (.source p.initial) true true

/-- The state carried by a pending handler is its starting state; its returned state is
passed to the source continuation only when the handler completes. -/
theorem interp_state_meaningAt [B -< D] (h : (e : E.I) → St → Producer F D (E.O e × St))
    (p : Producer E B X) (st : St) (c : (interp_state h p st).S) (bL bR : Bool) :
    eqit Eq bL bR ((interp_state h p st).meaningAt c)
      (InterpCursor.reference (E := StateRequest E St) (fun es ↦ h es.1 es.2) (stateInput p st)
        (fun (i, s) ↦ CTree.interp_state (fun e st' ↦ (h e st').meaning) (p.meaningAt i) s) c) := by
  apply InterpCursor.adequate
  rintro ⟨i, s⟩
  dsimp only
  rw [CTree.unfold_interp_state, observe_meaningAt]
  cases hn : p.next i <;> simp only [stateInput, hn] <;> first | rfl |
    (simp [InterpCursor.sourceHead, CTree.mbr, CTree.branch', CTree.br']; rfl)

theorem interp_state_meaning [B -< D] (h : (e : E.I) → St → Producer F D (E.O e × St))
    (p : Producer E B X) (st : St) : eutt Eq (interp_state h p st).meaning
      (CTree.interp_state (fun e s ↦ (h e s).meaning) p.meaning st) :=
  interp_state_meaningAt h p st (.source (p.initial, st)) true true

section Examples
private abbrev Ask : Effect.{0} := ⟨Unit, fun _ ↦ Nat⟩

/-- The handler asks the outside world for a number, updates the state, then spends one guard. -/
example :
    let h := fun (_ : Ask.I) (s : Nat) ↦
      bind (trigger (E := Ask) (B := Ask) ()) fun a ↦ ret (a + 1, s + a)
    let p := interp_state h (trigger (E := Ask) (B := Ask) ()) 4
    ∃ k j, p.next p.initial = .vis () k ∧ p.next (k 7) = .guard j ∧ p.next j = .ret (8, 11) :=
  ⟨_, _, rfl, rfl, rfl⟩

/-- A source guard cycle remains the same one-head transition for every initial state. -/
example [B -< D] (h : (e : E.I) → St → Producer F D (E.O e × St)) (s : St) :
    let loop : Producer E B X := ⟨PUnit, ⟨⟩, fun i ↦ .guard i⟩
    let p := interp_state h loop s
    p.next p.initial = .guard p.initial := rfl

end Examples
end Vellvm.Tree.Producer
