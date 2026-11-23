module

public import Vellvm.Semantics.Simulation
public import Vellvm.Tree.Catch

@[expose] public section
namespace Vellvm.Semantics.Instrumentation
open Tree Interfaces.Params
open CTree (CTree)
open ITree (Effect)

variable [Pa : Params]

/-- The quiet cursor is a presentation of the public tree, including every administrative guard. -/
def producerSimulation : Simulation Producer CTree where
  R l r := l.meaning = r
  pure := Producer.meaning_ret_eq
  trigger := Producer.meaning_trigger_eq
  branch := Producer.meaning_branch_eq
  bind {E B X Y l r k j} hl hk := by
    change (Producer.bind l k).meaning = (r >>= j)
    simp only [Producer.meaning_bind_eq, hl, hk]
  map {E B X Y} f {l r} hl := by
    change (Producer.bind l (fun a ↦ Producer.ret (f a))).meaning = (r >>= fun a ↦ pure (f a))
    simp only [Producer.meaning_bind_eq, Producer.meaning_ret_eq, hl]
    rfl
  iter {E B X Y l r} x h := by
    change (Producer.iter l x).meaning = CTree.iter r x
    simp only [Producer.meaning_iter_eq, h]
  translate {E F B X} h {l r} hl := by
    change (Producer.translate h l).meaning = CTree.translate h r
    simp only [Producer.meaning_translate_eq, hl]
  interp {E F B D X} sub {h g l r} hh hl := by
    change (Producer.interp h l).meaning = CTree.interp g r
    simp only [Producer.meaning_interp_eq, hh, hl]
  state {E F B D X S} sub {h g l r} st hh hl := by
    change (Producer.interp_state h l st).meaning = CTree.interp_state g r st
    simp only [Producer.meaning_interp_state_eq, hh, hl]
  mrec {D E B X h g l r} hh hl := by
    change (Producer.interp_mrec h l).meaning = CTree.interp_mrec g r
    simp only [Producer.meaning_interp_mrec_eq, hh, hl]
  loc _ := Producer.meaning_ret_eq ()
  msg _ := Producer.meaning_ret_eq ()
  record _ := Producer.meaning_ret_eq ()

theorem producerCatchCompatible {E B : Effect} {X A : Type} (sel : E.I → Option X)
    {l : Producer E B A} {r : CTree E B A} (h : producerSimulation.R l r) :
    producerSimulation.R (Catch.run sel l) (Catch.run sel r) := by
  change l.meaning = r at h
  change (Catch.producerRun sel l).meaning = Catch.ctreeRun sel r
  rw [Catch.meaning_producerRun, h]

end Vellvm.Semantics.Instrumentation
