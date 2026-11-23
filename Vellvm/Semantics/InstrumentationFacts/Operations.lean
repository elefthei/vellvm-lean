module

public import Vellvm.Semantics.InstrumentationFacts.Core

@[expose] public section
namespace Vellvm.Semantics.Instrumentation
open Tree Interfaces.Params
open ITree (Effect)
open CTree Coinduction
open Utils.rutt_cutoff (ruttc_bind_bchain ruttc_eutt_l)

variable {E F B : Effect} {X Y Z : Type}

private theorem translate_congr (h : (e : E.I) → (f : F.I) × (F.O f → E.O e)) :
    ∀ t s : CTree E B X, eutt Eq t s → eutt Eq (translate h t) (translate h s) := by
  coinduction C hc ih
  intro t s ts
  suffices go : ∀ l r, Layer (eqitComparison E Eq true true) (eutt Eq) l r →
      Layer (eqitComparison F Eq true true) C (translate h (CTree.fold l)).unfold
        (translate h (CTree.fold r)).unfold by
    simpa only [layerMon, fold_unfold] using go _ _ (related_iff.mp ts)
  intro l r hl
  induction hl with
  | ret h => simp only [fold_ret, ret_eq_pure, translate_ret, unfold_pure]; exact .ret h
  | guard h => simp only [fold_guard, translate_guard, unfold_guard]; exact .guard (ih _ _ h)
  | skipL _ _ inner => simp only [fold_guard, translate_guard, unfold_guard]; exact .skipL rfl (by simpa only [fold_unfold] using inner)
  | skipR _ _ inner => simp only [fold_guard, translate_guard, unfold_guard]; exact .skipR rfl (by simpa only [fold_unfold] using inner)
  | cutL h | cutR h => exact h.elim
  | stuck => simp only [fold_stuck, translate_stuck, unfold_stuck]; exact .stuck
  | step h => simp only [fold_step, translate_step, unfold_step]; exact .step (ih _ _ h)
  | br hk => simp only [fold_br, translate_br, unfold_br]; exact .br fun a ↦ ih _ _ (hk a)
  | vis he hk =>
    cases he
    simp only [fold_vis, translate_vis, unfold_vis]
    refine .vis rfl fun a b ab ↦ ?_
    cases eq_of_heq ab
    exact ih _ _ (hk _ _ HEq.rfl)

variable [Pa : Params]

private theorem translate_strict (h : (e : E.I) → (f : F.I) × (F.O f → E.O e)) :
    ∀ (t : CTree (E ⊕ₑ Trace) B X), eqit Eq false false (erase (translate (Logged.liftMap h) t))
      (translate h (erase t)) := by
  coinduction C hc ih
  intro t
  change Layer _ C _ _
  cases t with
  | ret x => simp only [translate_ret, erase_ret, unfold_pure]; exact .ret rfl
  | stuck => simp only [translate_stuck, erase_stuck, unfold_stuck]; exact .stuck
  | guard t => simp only [translate_guard, erase_guard, unfold_guard]; exact .guard (ih t)
  | step t => simp only [translate_step, erase_step, unfold_step]; exact .step (ih t)
  | br b k => simp only [translate_br, erase_br, unfold_br]; exact .br fun a ↦ ih _
  | vis e k =>
    cases e with
    | inr r => simp only [translate_vis, Logged.liftMap, erase_trace, translate_guard, unfold_guard]; exact .guard (ih _)
    | inl e =>
      cases hh : h e with | mk f back =>
        simp only [translate_vis, Logged.liftMap, hh, erase_vis, unfold_vis]
        refine .vis rfl fun a b ab ↦ ?_
        cases eq_of_heq ab; exact ih _

theorem agrees_translate (h : (e : E.I) → (f : F.I) × (F.O f → E.O e))
    {t : CTree (E ⊕ₑ Trace) B X} {s : CTree E B X} (ts : eutt Eq (erase t) s) :
    eutt Eq (erase (translate (Logged.liftMap h) t)) (translate h s) := by
  rw [eqit_strict_iff_eq.mp (translate_strict h t)]
  exact translate_congr h _ _ ts

/-- Guarded backedges compare immediately in the tower, even on an infinite loop. -/
theorem agrees_iter (l : X → CTree (E ⊕ₑ Trace) B (X ⊕ Y)) (r : X → CTree E B (X ⊕ Y))
    (body : ∀ x, eutt Eq (erase (l x)) (r x)) :
    ∀ x, eutt Eq (erase (CTree.iter l x)) (CTree.iter r x) := by
  coinduction C hc ih
  intro x
  rw [unfold_iter l, erase_bind, unfold_iter r]
  apply ruttc_bind_bchain _ _ _ _ Eq C hc _ _ Eq _ _ _ _ (body x)
  rintro (x | y) _ rfl
  · change Layer _ C (erase (CTree.guard _)).unfold (CTree.guard _).unfold
    rw [erase_guard, unfold_guard, unfold_guard]; exact .guard (ih x)
  · change Layer _ C (erase (pure y)).unfold (pure y : CTree E B Y).unfold
    rw [erase_ret, unfold_pure]; exact .ret rfl

end Vellvm.Semantics.Instrumentation
