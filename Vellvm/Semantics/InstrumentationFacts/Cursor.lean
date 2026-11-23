module

public import Vellvm.Semantics.InstrumentationFacts.Core

@[expose] public section
namespace Vellvm.Semantics.Instrumentation
open Tree Interfaces.Params Coinduction
open ITree (Effect)
open CTree (CTree CTreeF)
open Coinductive (PF)

variable [Pa : Params] {E B : Effect} {X S : Type}

/-- Track debugger data alongside the live cursor. Private requests are still presented to the
caller; the tracker changes state when the caller resumes them. -/
def track (update : S → TraceRequest → S) (p : Logged E B X) (initial : S) : Logged E B (X × S) :=
  ⟨p.S × S, (p.initial, initial), fun (i, s) ↦ match p.next i with
    | .ret x => .ret (x, s)
    | .stuck => .stuck
    | .guard j => .guard (j, s)
    | .step j => .step (j, s)
    | .br b k => .br b fun a ↦ (k a, s)
    | .vis (.inl e) k => .vis (.inl e) fun a ↦ (k a, s)
    | .vis (.inr r) k => .vis (.inr r) fun a ↦ (k a, update s r)⟩

/-- Dropping the debugger state and its private effects is transparent at *every* position.
The entire result `X`, including any LLVM state in it, is retained. -/
theorem forget_tracker (update : S → TraceRequest → S) (p : Logged E B X) (initial : S) :
    ∀ (i : p.S) (s : S),
    (erase ((track update p initial).meaningAt (i, s)) >>= fun xs ↦ pure xs.1) =
      erase (p.meaningAt i) := by
  suffices eqv : ∀ (i : p.S) (s : S), eqit Eq false false
      (erase ((track update p initial).meaningAt (i, s)) >>= fun xs ↦ pure xs.1)
      (erase (p.meaningAt i)) from fun i s ↦ eqit_strict_iff_eq.mp (eqv i s)
  coinduction C hc ih
  intro i s
  change Layer _ C _ _
  rw [CTree.unfold_bind, unfold_erase, unfold_erase,
    Producer.observe_meaningAt (E := E ⊕ₑ Trace) (track update p initial) (i, s),
    Producer.observe_meaningAt (E := E ⊕ₑ Trace) p i]
  dsimp only [track]
  cases hn : p.next i with
  | ret x =>
    change Layer _ C (pure x : CTree E B X).unfold (.ret x)
    rw [CTree.unfold_pure]; exact .ret rfl
  | stuck => exact .stuck
  | guard j => exact .guard (ih j s)
  | step j => exact .step (ih j s)
  | br b k => exact .br fun a ↦ ih _ _
  | vis e k => cases e with
    | inr r => exact .guard (ih _ _)
    | inl e =>
      refine .vis rfl fun a b ab ↦ ?_
      cases eq_of_heq ab
      exact ih _ _

end Vellvm.Semantics.Instrumentation
