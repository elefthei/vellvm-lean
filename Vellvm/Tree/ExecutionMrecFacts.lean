module

public import Vellvm.Tree.ExecutionMrec
public import CTree.Interp.RecursionFacts

@[expose] public section
namespace Vellvm.Tree.Producer
open ITree (Effect)
open CTree (CTree CTreeF)
open Coinductive Coinduction

universe u
variable {D E B : Effect.{u}} {X : Type u}
variable (ctx : (d : D.I) → Producer (D ⊕ₑ E) B (D.O d)) (root : Producer (D ⊕ₑ E) B X)

namespace Mrec

/-- The finite suspended callers are ordinary binds in the open, pre-interpretation tree. -/
def kont : {i : Option D.I} → Stack ctx root i → Answer D X i → CTree (D ⊕ₑ E) B X
  | _, .done => pure
  | _, .push _ k rest => fun x ↦ (body ctx root _).meaningAt (k x) >>= kont rest

def running {i} (st : Stack ctx root i) (s : (body ctx root i).S) : CTree E B X :=
  CTree.interp_mrec (fun d ↦ (ctx d).meaning) ((body ctx root i).meaningAt s >>= kont ctx root st)

def spec : Cursor ctx root → CTree E B X
  | ⟨true, st, s⟩ => .guard (running ctx root st s)
  | ⟨false, st, s⟩ => running ctx root st s

theorem unfold_running {i} (st : Stack ctx root i) (s : (body ctx root i).S) :
    (running ctx root st s).unfold = PF.map (CTreeF E B X) (spec ctx root) (run ctx root st s) := by
  have h := (CTree.fold_unfold ((body ctx root i).meaningAt s)).symm
  rw [observe_meaningAt] at h
  unfold running
  rw [run]
  cases hs : (body ctx root i).next s with
  | ret x =>
    rw [hs] at h
    change _ = (pure x : CTree (D ⊕ₑ E) B _) at h
    rw [h, CTree.pure_bind' x (kont ctx root st)]
    cases st with
    | done => simp [kont]; rfl
    | push d k rest => exact unfold_running rest (k x)
  | stuck =>
    rw [hs] at h
    change _ = CTree.stuck at h
    rw [h, CTree.stuck_bind, CTree.interp_mrec_stuck, CTree.unfold_stuck]
    rfl
  | step j =>
    rw [hs] at h
    change _ = CTree.step _ at h
    rw [h, CTree.step_bind, CTree.interp_mrec_step, CTree.unfold_step]
    rfl
  | guard j =>
    rw [hs] at h
    change _ = CTree.guard _ at h
    rw [h, CTree.guard_bind, CTree.interp_mrec_guard_eq, CTree.unfold_guard]
    rfl
  | vis e k =>
    rw [hs] at h
    change _ = CTree.vis e _ at h
    rw [h, CTree.vis_bind]
    cases e with
    | inl d => rw [CTree.interp_mrec_vis_inl, CTree.unfold_guard]; rfl
    | inr e => rw [CTree.interp_mrec_vis_inr, CTree.unfold_vis]; rfl
  | br b k =>
    rw [hs] at h
    change _ = CTree.br b _ at h
    rw [h, CTree.br_bind, CTree.interp_mrec_br, CTree.unfold_br]
    rfl
termination_by structural st

theorem unfold_spec (s : Cursor ctx root) :
    (spec ctx root s).unfold = PF.map (CTreeF E B X) (spec ctx root) (next ctx root s) := by
  obtain ⟨flag, st, s⟩ := s
  cases flag with
  | false => exact unfold_running ctx root st s
  | true => exact CTree.unfold_guard _

end Mrec

/-- Each cursor denotes its package interpreter with exactly the same heads, including guards. -/
theorem interp_mrec_cursor (bL bR : Bool) : ∀ s : Mrec.Cursor ctx root,
    eqit Eq bL bR ((interp_mrec ctx root).meaningAt s) (Mrec.spec ctx root s) := by
  coinduction R hR ih
  intro s
  change Layer _ R _ _
  rw [observe_meaningAt (interp_mrec ctx root) s, Mrec.unfold_spec ctx root s]
  change Layer _ R (PF.map (CTreeF E B X) _ (Mrec.next ctx root s))
    (PF.map (CTreeF E B X) _ (Mrec.next ctx root s))
  cases Mrec.next ctx root s with
  | ret x => exact .ret rfl
  | stuck => exact .stuck
  | step j => exact .step (ih j)
  | guard j => exact .guard (ih j)
  | br b k => exact .br fun a ↦ ih (k a)
  | vis e k =>
    refine .vis rfl fun a b h ↦ ?_
    cases eq_of_heq h
    exact ih (k a)

theorem interp_mrec_meaning (bL bR : Bool) :
    eqit Eq bL bR (interp_mrec ctx root).meaning
      (CTree.interp_mrec (fun d ↦ (ctx d).meaning) root.meaning) := by
  simpa [Mrec.spec, Mrec.running, Mrec.kont, Mrec.body, meaning, interp_mrec] using
    interp_mrec_cursor ctx root bL bR (interp_mrec ctx root).initial

theorem mrec_meaning (d : D.I) (bL bR : Bool) :
    eqit Eq bL bR (mrec ctx d).meaning (CTree.mrec (fun d ↦ (ctx d).meaning) d) :=
  interp_mrec_meaning ctx (ctx d) bL bR

section

private inductive Call | flag | count
private abbrev Calls : Effect := ⟨Call, fun | .flag => Bool | .count => Nat⟩
private abbrev External : Effect := ⟨Unit, fun _ ↦ Nat⟩

/-- Two calls push different answer types. Both returns pop silently after the external guard. -/
example (B : Effect) :
    let calls : (d : Call) → Producer (Calls ⊕ₑ External) B (Calls.O d)
      | .flag => bind (trigger (E := Calls ⊕ₑ External) (.inl Call.count))
          fun (n : Nat) ↦ ret (n == 42)
      | .count => bind (trigger (E := Calls ⊕ₑ External) (.inr ()))
          fun (n : Nat) ↦ ret (n + 1)
    let nested := interp_mrec calls (bind (trigger (E := Calls ⊕ₑ External) (.inl Call.flag))
      fun (b : Bool) ↦ ret (if b then 7 else 0 : Nat))
    nested.observePrefix nested.initial 5 =
      .guard (.guard (.vis () fun n ↦ .guard (.ret (if n + 1 == 42 then 7 else 0)))) := rfl

end

end Vellvm.Tree.Producer
