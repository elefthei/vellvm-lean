module

public import Vellvm.Semantics.InstrumentationFacts.Core

@[expose] public section
namespace Vellvm.Semantics.Instrumentation
open Tree Interfaces.Params
open ITree (Effect)
open CTree Coinduction

variable {E B : Effect} {X A : Type}

namespace CatchFacts
variable (sel : E.I → Option X)

private theorem ret (a : A) : Catch.ctreeRun (B := B) sel (pure a) = pure (.inr a) := by
  apply unfold_inj; simp only [Catch.unfold_ctreeRun, unfold_pure]
private theorem stuck : Catch.ctreeRun (B := B) (A := A) sel .stuck = .stuck := by
  apply unfold_inj; simp only [Catch.unfold_ctreeRun, unfold_stuck]
private theorem guard (t : CTree E B A) : Catch.ctreeRun sel t.guard = (Catch.ctreeRun sel t).guard := by
  apply unfold_inj; simp only [Catch.unfold_ctreeRun, unfold_guard]
private theorem step (t : CTree E B A) : Catch.ctreeRun sel t.step = (Catch.ctreeRun sel t).guard.step := by
  apply unfold_inj; simp only [Catch.unfold_ctreeRun, unfold_step]
private theorem br (b : B.I) (k : B.O b → CTree E B A) :
    Catch.ctreeRun sel (.br b k) = .br b (fun a ↦ (Catch.ctreeRun sel (k a)).guard) := by
  apply unfold_inj; simp only [Catch.unfold_ctreeRun, unfold_br]
private theorem visNone (e : E.I) (k : E.O e → CTree E B A) (hs : sel e = none) :
    Catch.ctreeRun sel (.vis e k) = .vis e (fun a ↦ (Catch.ctreeRun sel (k a)).guard) := by
  apply unfold_inj; simp only [Catch.unfold_ctreeRun, unfold_vis, hs]
private theorem visSome (e : E.I) (k : E.O e → CTree E B A) (x : X) (hs : sel e = some x) :
    Catch.ctreeRun sel (.vis e k) = pure (.inl x) := by
  apply unfold_inj; simp only [Catch.unfold_ctreeRun, unfold_vis, unfold_pure, hs]

private theorem guardChain {C : Coinduction.Rel (CTree E B A) (CTree E B A)}
    (hc : Chain (layerMon B (eqitComparison E Eq true true)) C) {l r} (h : C l r) :
    C l.guard r.guard := by
  apply b_chain hc; change Layer _ C _ _; rw [unfold_guard, unfold_guard]; exact .guard h

private theorem fuse [Params] : ∀ t : CTree (E ⊕ₑ Trace) B A,
    eutt Eq (erase (Catch.ctreeRun (Logged.selectPublic sel) t)) (Catch.ctreeRun sel (erase t)) := by
  coinduction C hc ih
  intro t
  change Layer _ C _ _
  cases t with
  | ret a => simp only [ret, erase_ret, unfold_pure]; exact .ret rfl
  | stuck => simp only [stuck, erase_stuck, unfold_stuck]; exact .stuck
  | guard t => simp only [guard, erase_guard, unfold_guard]; exact .guard (ih t)
  | step t => simp only [step, erase_step, erase_guard, unfold_step]; exact .step (guardChain hc (ih t))
  | br b k => simp only [br, erase_br, erase_guard, unfold_br]; exact .br fun a ↦ guardChain hc (ih _)
  | vis e k =>
    cases e with
    | inr r =>
      rw [visNone _ _ _ (show Logged.selectPublic sel (.inr r) = none from rfl)]
      simp only [erase_trace, erase_guard, guard, unfold_guard]
      apply Layer.skipL rfl
      rw [unfold_guard]; exact .guard (ih _)
    | inl e =>
      cases hs : sel e with
      | some x =>
        rw [visSome (E := E ⊕ₑ Trace) (Logged.selectPublic sel) (.inl e) k x hs]
        simp only [erase_ret, erase_vis, visSome sel e _ x hs, unfold_pure]; exact .ret rfl
      | none =>
        rw [visNone (E := E ⊕ₑ Trace) (Logged.selectPublic sel) (.inl e) k hs]
        simp only [erase_vis, erase_guard, visNone sel e _ hs, unfold_vis]
        refine .vis rfl fun a b ab ↦ ?_
        cases eq_of_heq ab
        exact guardChain hc (ih _)

end CatchFacts

theorem agrees_catch [Params] (sel : E.I → Option X) {l : Logged E B A} {r : CTree E B A}
    (hr : eutt Eq (erase l.meaning) r) :
    eutt Eq (erase (Producer.meaning (Catch.run (M := Logged) sel l))) (Catch.run sel r) := by
  change eutt Eq (erase (Catch.producerRun (Logged.selectPublic sel) l).meaning) (Catch.ctreeRun sel r)
  rw [Catch.meaning_producerRun (E := E ⊕ₑ Trace) (Logged.selectPublic sel) l]
  exact Utils.rutt_cutoff.ruttc_eutt_l _ _ _ (CatchFacts.fuse sel _)
    (Catch.ctreeRun_congr sel true true _ _ hr)

end Vellvm.Semantics.Instrumentation
