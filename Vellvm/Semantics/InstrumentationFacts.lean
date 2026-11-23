module

public import Vellvm.Semantics.InstrumentationFacts.Operations
public import Vellvm.Semantics.InstrumentationFacts.Interp
public import Vellvm.Semantics.InstrumentationFacts.Mrec
public import Vellvm.Semantics.InstrumentationFacts.Catch
public import Vellvm.Semantics.InstrumentationFacts.Cursor
public import Vellvm.Semantics.InstrumentationFacts.Producer

@[expose] public section
namespace Vellvm.Semantics.Instrumentation
open Tree Interfaces.Params
open CTree (CTree)
open ITree (Effect)

variable [Pa : Params] {E B : Effect} {X Y : Type}

/-- Relation used by all shared worker proofs. Neither events nor semantic state are quotiented. -/
abbrev Agrees (l : Logged E B X) (r : CTree E B X) := eutt Eq (erase l.meaning) r

theorem agrees_pure (x : X) : Agrees (E := E) (B := B) (pure x) (pure x) := by
  change eutt Eq (erase (Producer.ret x).meaning) (pure x : CTree E B X)
  rw [Producer.meaning_ret_eq, CTree.ret_eq_pure, erase_ret]
  exact eqit_refl true true _

theorem agrees_bind {l : Logged E B X} {r : CTree E B X}
    {k : X → Logged E B Y} {j : X → CTree E B Y} (hl : Agrees l r)
    (hk : ∀ x, Agrees (k x) (j x)) : Agrees (l >>= k) (r >>= j) := by
  change eutt Eq (erase (Producer.bind l k).meaning) (r >>= j)
  rw [Producer.meaning_bind_eq (E := E ⊕ₑ Trace) l k, erase_bind]
  exact Utils.rutt_cutoff.ruttc_bind _ _ _ _ Eq Eq _ _ _ _ hl (fun x _ p ↦ p ▸ hk x)

theorem agrees_private (q : TraceRequest) : Agrees (E := E) (B := B) (Logged.trace q) (pure ()) := by
  change eutt Eq (erase (Producer.trigger (E := E ⊕ₑ Trace) (B := B) (.inr q)).meaning) (pure ())
  simp only [Producer.meaning_trigger_eq, CTree.trigger, erase_trace, erase_ret]
  exact Related.guard_left rfl (eqit_refl true true _)

/-- Erasing the private trace commutes with the complete worker interface. -/
def loggedSimulation : Simulation (Logged (Pa := Pa)) CTree where
  R := Agrees
  pure := agrees_pure
  bind := agrees_bind
  map {E B X Y} f {l r} hl := agrees_bind hl (fun a ↦ agrees_pure (f a))
  trigger {E B} e := by
    change eutt Eq (erase (Producer.trigger (E := E ⊕ₑ Trace) (B := B) (.inl e)).meaning)
      (CTree.trigger e)
    simp only [Producer.meaning_trigger_eq, CTree.trigger, erase_vis, erase_ret]
    exact eqit_refl true true _
  branch {E B} b := by
    change eutt Eq (erase (Producer.branch (E := E ⊕ₑ Trace) b).meaning) (CTree.branch b)
    simp only [Producer.meaning_branch_eq, CTree.branch, erase_br, erase_ret]
    exact eqit_refl true true _
  iter {E B X Y l r} x h := by
    change eutt Eq (erase (Producer.iter l x).meaning) (CTree.iter r x)
    rw [Producer.meaning_iter_eq (E := E ⊕ₑ Trace) l x]
    exact agrees_iter _ r h x
  translate {E F B X} h {l r} hl := by
    change eutt Eq (erase (Producer.translate (Logged.liftMap h) l).meaning) (CTree.translate h r)
    rw [Producer.meaning_translate_eq (E := E ⊕ₑ Trace) (Logged.liftMap h) l]
    exact agrees_translate h hl
  interp hh hl := agrees_interp hh hl
  state {E F B D X S} sub {h g l r} st hh hl := by
    have hp : (fun (a b : X × S) ↦ a.1 = b.1 ∧ a.2 = b.2) = Eq := by
      funext a b; exact propext ⟨fun h ↦ Prod.ext h.1 h.2, fun | rfl => ⟨rfl, rfl⟩⟩
    change eutt Eq (erase (Producer.interp_state (Logged.forwardState h) l st).meaning)
      (CTree.interp_state g r st)
    simpa only [hp] using agrees_interp_state (Q := Eq) st hh hl
  mrec := agrees_interp_mrec
  loc loc := agrees_private (.setLoc loc)
  msg msg := agrees_private (.diagnostic msg)
  record := agrees_private

theorem loggedCatchCompatible {E B : Effect} {X A : Type} (sel : E.I → Option X)
    {l : Logged E B A} {r : CTree E B A} (h : loggedSimulation.R l r) :
    loggedSimulation.R (Catch.run sel l) (Catch.run sel r) := agrees_catch sel h

/-- The same observation at an executable cursor, without unfolding its cofix to run it. -/
theorem agrees_cursor {l : Logged E B X} {r : CTree E B X} (h : loggedSimulation.R l r) :
    eutt Eq (eraseCursor l).meaning r := by
  change eutt Eq ((eraseCursor l).meaningAt l.initial) r
  rw [eraseCursor_meaningAt]; exact h

/-- Erasing side data observationally restores the *whole* public result of any related worker. -/
theorem agrees_tracked_cursor {l : Logged E B X} {r : CTree E B X} (h : loggedSimulation.R l r)
    {S : Type} (update : S → TraceRequest → S) (s : S) :
    eutt Eq (erase (Producer.meaning (track update l s)) >>= fun xs ↦ pure xs.1) r := by
  change eutt Eq (erase ((track update l s).meaningAt (l.initial, s)) >>= fun xs ↦ pure xs.1) r
  rw [forget_tracker]; exact h

end Vellvm.Semantics.Instrumentation
