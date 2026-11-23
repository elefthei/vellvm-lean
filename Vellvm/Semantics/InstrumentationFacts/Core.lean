module

public import Vellvm.Tree.Logged
public import Vellvm.Tree.StrictEq
public import Vellvm.Utils.rutt_cutoff

@[expose] public section
namespace Vellvm.Semantics.Instrumentation
open Tree Interfaces.Params
open ITree (Effect)
open CTree (CTree CTreeF)
open Coinductive Coinduction

variable [Pa : Params] {E B : Effect} {X Y S : Type}

/-- Only a private request becomes silent. All public answer types and continuations survive. -/
def eraseHead (h : CTreeF (E ⊕ₑ Trace) B X S) : CTreeF E B X S := match h with
  | .ret x => .ret x
  | .stuck => .stuck
  | .step s => .step s
  | .guard s => .guard s
  | .br b k => .br b k
  | .vis (.inl e) k => .vis e k
  | .vis (.inr _) k => .guard (k ())

def erase (t : CTree (E ⊕ₑ Trace) B X) : CTree E B X :=
  cofix (CTreeF E B X) (fun u ↦ eraseHead u.unfold) t

theorem unfold_erase (t : CTree (E ⊕ₑ Trace) B X) :
    (erase t).unfold = PF.map _ erase (eraseHead t.unfold) := by
  change (Producer.meaningAt ⟨_, t, fun u ↦ eraseHead u.unfold⟩ t).unfold = _
  exact Producer.observe_meaningAt _ _

@[simp] theorem erase_ret (x : X) : erase (E := E) (B := B) (pure x) = pure x := by
  apply CTree.unfold_inj; rw [unfold_erase, CTree.unfold_pure, CTree.unfold_pure]; rfl

@[simp] theorem erase_stuck : erase (E := E) (B := B) (X := X) .stuck = .stuck := by
  apply CTree.unfold_inj; rw [unfold_erase, CTree.unfold_stuck, CTree.unfold_stuck]; rfl

@[simp] theorem erase_guard (t : CTree (E ⊕ₑ Trace) B X) : erase t.guard = (erase t).guard := by
  apply CTree.unfold_inj; rw [unfold_erase, CTree.unfold_guard, CTree.unfold_guard]; rfl

@[simp] theorem erase_step (t : CTree (E ⊕ₑ Trace) B X) : erase t.step = (erase t).step := by
  apply CTree.unfold_inj; rw [unfold_erase, CTree.unfold_step, CTree.unfold_step]; rfl

@[simp] theorem erase_vis (e : E.I) (k : E.O e → CTree (E ⊕ₑ Trace) B X) :
    erase (CTree.vis (Sum.inl e) k) = .vis e (fun a ↦ erase (k a)) := by
  apply CTree.unfold_inj; rw [unfold_erase, CTree.unfold_vis, CTree.unfold_vis]; rfl

@[simp] theorem erase_trace (r : TraceRequest) (k : Unit → CTree (E ⊕ₑ Trace) B X) :
    erase (CTree.vis (Sum.inr r) k) = .guard (erase (k ())) := by
  apply CTree.unfold_inj; rw [unfold_erase, CTree.unfold_vis, CTree.unfold_guard]; rfl

@[simp] theorem erase_br (b : B.I) (k : B.O b → CTree (E ⊕ₑ Trace) B X) :
    erase (CTree.br b k) = .br b (fun a ↦ erase (k a)) := by
  apply CTree.unfold_inj; rw [unfold_erase, CTree.unfold_br, CTree.unfold_br]; rfl

/-- The erasure cursor advances the original producer by exactly one head. -/
def eraseCursor (p : Logged E B X) : Producer E B X :=
  ⟨p.S, p.initial, fun s ↦ eraseHead (p.next s)⟩

/-- Valid also when paused at a pending handler, or in a recursive callee. -/
theorem eraseCursor_meaningAt (p : Logged E B X) (s : p.S) :
    (eraseCursor p).meaningAt s = erase (p.meaningAt s) := by
  apply eqit_strict_iff_eq.mp (Producer.meaningAt_strict (eraseCursor p)
    (fun s ↦ erase (p.meaningAt s)) _ s)
  intro j
  change (erase (p.meaningAt j)).unfold = PF.map (CTreeF E B X)
    (fun s ↦ erase (p.meaningAt s)) (eraseHead (p.next j))
  rw [unfold_erase, Producer.observe_meaningAt (E := E ⊕ₑ Trace) p j]
  cases p.next j with
  | vis e k => cases e <;> rfl
  | _ => rfl

private theorem bind_strict (k : X → CTree (E ⊕ₑ Trace) B Y) :
    ∀ t, eqit Eq false false (erase (t >>= k)) (erase t >>= fun x ↦ erase (k x)) := by
  coinduction R hR ih
  intro t
  cases t with
  | ret x => simpa only [CTree.pure_bind', erase_ret] using
      gfp_le_chain (.step hR) _ _ (eqit_refl false false (erase (k x)))
  | stuck => change Layer _ R _ _; simp only [CTree.stuck_bind, erase_stuck, CTree.unfold_stuck]; exact .stuck
  | step t => change Layer _ R _ _; simp only [CTree.step_bind, erase_step, CTree.unfold_step]; exact .step (ih t)
  | guard t => change Layer _ R _ _; simp only [CTree.guard_bind, erase_guard, CTree.unfold_guard]; exact .guard (ih t)
  | br b l => change Layer _ R _ _; simp only [CTree.br_bind, erase_br, CTree.unfold_br]; exact .br fun a ↦ ih (l a)
  | vis e l =>
    change Layer _ R _ _
    cases e with
    | inr r => simp only [CTree.vis_bind, erase_trace, CTree.guard_bind, CTree.unfold_guard]; exact .guard (ih _)
    | inl e =>
      simp only [CTree.vis_bind, erase_vis, CTree.unfold_vis]
      refine .vis rfl fun a b hab ↦ ?_
      cases eq_of_heq hab; exact ih _

@[simp] theorem erase_bind (t : CTree (E ⊕ₑ Trace) B X) (k : X → CTree (E ⊕ₑ Trace) B Y) :
    erase (t >>= k) = (erase t >>= fun x ↦ erase (k x)) := eqit_strict_iff_eq.mp (bind_strict k t)

end Vellvm.Semantics.Instrumentation
