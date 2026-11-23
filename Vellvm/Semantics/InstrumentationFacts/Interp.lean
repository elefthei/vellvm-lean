module

public import Vellvm.Semantics.InstrumentationFacts.Core

/-! Interpretation respects weak equivalence, including when a private trace row is erased. -/

@[expose] public section
namespace Vellvm.Semantics.Instrumentation
open ITree (Effect Subeffect)
open CTree Coinduction Vellvm.Tree Utils.rutt_cutoff

variable {E F B D : Effect} {X Y S : Type} {Q : X → Y → Prop}

private theorem guard_chain {C : Coinduction.Rel (CTree F D X) (CTree F D Y)}
    (hc : Chain (layerMon D (eqitComparison F Q true true)) C) {t s} (h : C t s) :
    C t.guard s.guard := by
  apply b_chain hc
  change Layer _ C _ _
  rw [unfold_guard, unfold_guard]
  exact .guard h

private theorem bind_guard_layer {C : Coinduction.Rel (CTree F D X) (CTree F D Y)}
    (hc : Chain (layerMon D (eqitComparison F Q true true)) C) {A : Type}
    {t s : CTree F D A} {k : A → CTree F D X} {l : A → CTree F D Y}
    (h : eutt Eq t s) (hk : ∀ a, C (k a) (l a)) :
    Layer (eqitComparison F Q true true) C
      (t >>= fun a ↦ (k a).guard).unfold (s >>= fun a ↦ (l a).guard).unfold := by
  apply ruttc_bind_bchain _ _ _ _ Q C hc _ _ Eq _ _ _ _ h
  rintro a _ rfl
  change Layer _ C _ _
  rw [unfold_guard, unfold_guard]
  exact .guard (hk a)

/-- Interpreters may change the event row and inject branches into a larger row. -/
theorem eutt_interp [B -< D] {h g : (e : E.I) → CTree F D (E.O e)}
    (hh : ∀ e, eutt Eq (h e) (g e)) : ∀ {t : CTree E B X} {s : CTree E B Y},
    eutt Q t s → eutt Q (interp h t) (interp g s) := by
  coinduction C hc ih
  intro t s hts
  suffices go : ∀ u v, Layer (eqitComparison E Q true true) (eutt Q) u v →
      Layer (eqitComparison F Q true true) C (interp h (.fold u)).unfold
        (interp g (.fold v)).unfold by
    simpa only [layerMon, fold_unfold] using go _ _ (related_iff.mp hts)
  intro u v hrel
  induction hrel with
  | ret hr => simp only [fold_ret, ret_eq_pure, interp_ret, unfold_pure]; exact .ret hr
  | stuck => simp only [fold_stuck, interp_stuck, unfold_stuck]; exact .stuck
  | guard hr => simp only [fold_guard, interp_guard, unfold_guard]; exact .guard (ih hr)
  | step hr => simp only [fold_step, interp_step, unfold_step]; exact .step (guard_chain hc (ih hr))
  | br hk =>
    simp only [fold_br, interp_br', CTree.br', unfold_br]
    exact .br fun a ↦ guard_chain hc (ih (hk _))
  | vis he hk =>
    cases he
    simp only [fold_vis, interp_vis]
    exact bind_guard_layer hc (hh _) fun a ↦ ih (hk a a HEq.rfl)
  | skipL _ _ hi =>
    simp only [fold_guard, interp_guard, unfold_guard]
    exact .skipL rfl (by simpa only [fold_unfold] using hi)
  | skipR _ _ hi =>
    simp only [fold_guard, interp_guard, unfold_guard]
    exact .skipR rfl (by simpa only [fold_unfold] using hi)
  | cutL hf | cutR hf => exact hf.elim

/-- Related source results are paired with identical final states, for every initial state. -/
theorem eutt_interp_state [B -< D] {h g : (e : E.I) → S → CTree F D (E.O e × S)}
    (hh : ∀ e st, eutt Eq (h e st) (g e st)) : ∀ {t : CTree E B X} {s : CTree E B Y} (st : S),
    eutt Q t s → eutt (fun xs ys ↦ Q xs.1 ys.1 ∧ xs.2 = ys.2)
      (interp_state h t st) (interp_state g s st) := by
  coinduction C hc ih
  intro t s st hts
  suffices go : ∀ u v, Layer (eqitComparison E Q true true) (eutt Q) u v →
      Layer (eqitComparison F (fun xs ys ↦ Q xs.1 ys.1 ∧ xs.2 = ys.2) true true) C
        (interp_state h (.fold u) st).unfold (interp_state g (.fold v) st).unfold by
    simpa only [layerMon, fold_unfold] using go _ _ (related_iff.mp hts)
  intro u v hrel
  induction hrel with
  | ret hr => simp only [fold_ret, ret_eq_pure, interp_state_ret, unfold_pure]; exact .ret ⟨hr, rfl⟩
  | stuck => simp only [fold_stuck, interp_state_stuck, unfold_stuck]; exact .stuck
  | guard hr => simp only [fold_guard, interp_state_guard, unfold_guard]; exact .guard (ih st hr)
  | step hr =>
    simp only [fold_step, interp_state_step, unfold_step]; exact .step (guard_chain hc (ih st hr))
  | br hk =>
    simp only [fold_br, interp_state_br, CTree.branch', CTree.br', br_bind, pure_bind, unfold_br]
    exact .br fun a ↦ guard_chain hc (ih st (hk _))
  | vis he hk =>
    cases he
    simp only [fold_vis, interp_state_vis]
    exact bind_guard_layer hc (hh _ st) fun xs ↦ ih xs.2 (hk xs.1 xs.1 HEq.rfl)
  | skipL _ _ hi =>
    simp only [fold_guard, interp_state_guard, unfold_guard]
    exact .skipL rfl (by simpa only [fold_unfold] using hi)
  | skipR _ _ hi =>
    simp only [fold_guard, interp_state_guard, unfold_guard]
    exact .skipR rfl (by simpa only [fold_unfold] using hi)
  | cutL hf | cutR hf => exact hf.elim

variable [Pa : Interfaces.Params.Params]

/-- Forwarding a trace spends one additional interpreter guard, erased up to `eutt`. -/
theorem erase_interp [B -< D] (h : (e : E.I) → Logged F D (E.O e)) :
    ∀ t : CTree (E ⊕ₑ Trace) B X,
      eutt Eq (erase (interp (fun e ↦ (Logged.forward h e).meaning) t))
        (interp (fun e ↦ erase (h e).meaning) (erase t)) := by
  coinduction C hc ih
  intro t
  change Layer _ C _ _
  cases t with
  | ret x => simp only [interp_ret, erase_ret, unfold_pure]; exact .ret rfl
  | stuck => simp only [interp_stuck, erase_stuck, unfold_stuck]; exact .stuck
  | guard t => simp only [interp_guard, erase_guard, unfold_guard]; exact .guard (ih t)
  | step t =>
    simp only [interp_step, erase_step, erase_guard, unfold_step]
    exact .step (guard_chain hc (ih t))
  | br b k =>
    simp only [interp_br', CTree.br', erase_br, erase_guard, unfold_br]
    exact .br fun a ↦ guard_chain hc (ih _)
  | vis e k =>
    cases e with
    | inl e =>
      simp only [interp_vis, erase_vis, erase_bind, erase_guard, Logged.forward]
      exact bind_guard_layer hc (eqit_refl true true _) fun a ↦ ih (k a)
    | inr r =>
      simp only [interp_vis, Logged.forward, Logged.trace, Producer.meaning_trigger_eq,
        CTree.trigger, vis_bind, pure_bind, erase_trace, erase_guard, interp_guard, unfold_guard]
      exact .skipL rfl (by rw [unfold_guard]; exact .guard (ih (k ())))

/-- Forwarding a private request returns its original state before resuming the continuation. -/
theorem erase_interp_state [B -< D] (h : (e : E.I) → S → Logged F D (E.O e × S)) :
    ∀ (t : CTree (E ⊕ₑ Trace) B X) (st : S),
      eutt Eq (erase (interp_state (fun e s ↦ (Logged.forwardState h e s).meaning) t st))
        (interp_state (fun e s ↦ erase (h e s).meaning) (erase t) st) := by
  coinduction C hc ih
  intro t st
  change Layer _ C _ _
  cases t with
  | ret x => simp only [interp_state_ret, erase_ret, unfold_pure]; exact .ret rfl
  | stuck => simp only [interp_state_stuck, erase_stuck, unfold_stuck]; exact .stuck
  | guard t => simp only [interp_state_guard, erase_guard, unfold_guard]; exact .guard (ih t st)
  | step t =>
    simp only [interp_state_step, erase_step, erase_guard, unfold_step]
    exact .step (guard_chain hc (ih t st))
  | br b k =>
    simp only [interp_state_br, CTree.branch', CTree.br', br_bind, pure_bind, erase_br,
      erase_guard, unfold_br]
    exact .br fun a ↦ guard_chain hc (ih _ st)
  | vis e k =>
    cases e with
    | inl e =>
      simp only [interp_state_vis, erase_vis, erase_bind, erase_guard, Logged.forwardState]
      exact bind_guard_layer hc (eqit_refl true true _) fun xs ↦ ih (k xs.1) xs.2
    | inr r =>
      simp only [interp_state_vis, Logged.forwardState, Logged.trace, Producer.meaning_bind_eq,
        Producer.meaning_ret_eq, Producer.meaning_trigger_eq (E := F ⊕ₑ Trace) (B := D) (Sum.inr r),
        CTree.trigger, vis_bind, ret_eq_pure, pure_bind, erase_trace, erase_guard, interp_state_guard,
        unfold_guard]
      exact .skipL rfl (by rw [unfold_guard]; exact .guard (ih (k ()) st))

/-- Agreement of a logged interpreter with a plain interpreter on related input trees. -/
theorem agrees_interp [B -< D] {h : (e : E.I) → Logged F D (E.O e)}
    {g : (e : E.I) → CTree F D (E.O e)} {t : Logged E B X} {s : CTree E B Y}
    (hh : ∀ e, eutt Eq (erase (h e).meaning) (g e)) (ht : eutt Q (erase t.meaning) s) :
    eutt Q (erase (Producer.interp (Logged.forward h) t).meaning) (interp g s) := by
  rw [Producer.meaning_interp_eq (Logged.forward h) t]
  exact ruttc_eutt_l _ _ _ (erase_interp h _) (eutt_interp hh ht)

/-- The same agreement for stateful handlers, including equality of the returned states. -/
theorem agrees_interp_state [B -< D] {h : (e : E.I) → S → Logged F D (E.O e × S)}
    {g : (e : E.I) → S → CTree F D (E.O e × S)} {t : Logged E B X} {s : CTree E B Y}
    (st : S) (hh : ∀ e a, eutt Eq (erase (h e a).meaning) (g e a))
    (ht : eutt Q (erase t.meaning) s) :
    eutt (fun xs ys ↦ Q xs.1 ys.1 ∧ xs.2 = ys.2)
      (erase (Producer.interp_state (Logged.forwardState h) t st).meaning) (interp_state g s st) := by
  rw [Producer.meaning_interp_state_eq (Logged.forwardState h) t st]
  exact ruttc_eutt_l _ _ _ (erase_interp_state h _ st) (eutt_interp_state hh st ht)

end Vellvm.Semantics.Instrumentation
