module

public import Vellvm.Semantics.InstrumentationFacts.Core
import Logic.Yield.Policy

@[expose] public section
namespace Vellvm.Semantics.Instrumentation
open ITree (Effect)
open Vellvm.Tree CTree Coinduction
open Utils.rutt_cutoff (FF1 ruttc_weaken ruttc_interp_mrec ruttc_eutt_l
  sum_pred1 sum_prerel sum_postrel)

variable {D E B : Effect} {X Y : Type} {Q : X → Y → Prop}

private abbrev sameAnswer (E : Effect) (e : E.I) (a : E.O e) (f : E.I) (b : E.O f) := HEq a b

/-- Re-express ordinary equality of requests in the sum-row vocabulary of `ruttc_interp_mrec`. -/
private theorem split_eutt {P : X → Y → Prop} (hp : ∀ x y, Q x y → P x y)
    {t : CTree (D ⊕ₑ E) B X} {s : CTree (D ⊕ₑ E) B Y} (h : eutt Q t s) :
    Tree.ruttc (sum_pred1 FF1 FF1) (sum_pred1 FF1 FF1) (sum_prerel Eq Eq)
      (sum_postrel (sameAnswer D) (sameAnswer E)) P t s := by
  apply ruttc_weaken FF1 _ FF1 _ Eq _ (sameAnswer (D ⊕ₑ E)) _ Q P
    (fun _ hf ↦ hf.elim) (fun _ hf ↦ hf.elim) _ _ hp t s h
  · rintro (d | e) _ rfl
    · exact .inl rfl
    · exact .inr rfl
  · rintro (d | e) a (d' | e') b hab <;> first | exact hab | exact False.elim hab

/-- Mutually recursive bodies can differ by finite stuttering, with no termination assumption. -/
theorem eutt_interp_mrec {h g : (d : D.I) → CTree (D ⊕ₑ E) B (D.O d)}
    {t : CTree (D ⊕ₑ E) B X} {s : CTree (D ⊕ₑ E) B Y}
    (hh : ∀ d, eutt Eq (h d) (g d)) (ht : eutt Q t s) :
    eutt Q (interp_mrec h t) (interp_mrec g s) := by
  apply ruttc_interp_mrec FF1 FF1 Eq Eq (sameAnswer D) (sameAnswer E) Q h g
  · rintro d _ rfl
    exact split_eutt (fun _ _ he ↦ heq_of_eq he) (hh d)
  · exact split_eutt (fun _ _ hq ↦ hq) ht

variable [Pa : Interfaces.Params.Params]

/-- Erasing after a private event leaves one extra interpreter guard, not a new observation. -/
private theorem erase_mrec (h : (d : D.I) → CTree ((D ⊕ₑ E) ⊕ₑ Trace) B (D.O d)) :
    ∀ t : CTree ((D ⊕ₑ E) ⊕ₑ Trace) B X,
    eutt Eq (erase (interp_mrec (fun d ↦ translate Logged.reassoc (h d))
      (translate Logged.reassoc t))) (interp_mrec (fun d ↦ erase (h d)) (erase t)) := by
  coinduction R hR ih
  intro t
  have guards {u v : CTree E B X} (huv : R u v) : R u.guard v.guard := by
    apply b_chain hR
    change Layer _ R _ _
    rw [unfold_guard, unfold_guard]
    exact .guard huv
  change Layer _ R _ _
  cases t with
  | ret x => simp only [translate_ret, interp_mrec_ret, erase_ret, unfold_pure]; exact .ret rfl
  | stuck => simp only [translate_stuck, interp_mrec_stuck, erase_stuck, unfold_stuck]; exact .stuck
  | guard t =>
    simp only [translate_guard, interp_mrec_guard_eq, erase_guard, unfold_guard]
    exact .guard (ih t)
  | step t =>
    simp only [translate_step, interp_mrec_step, erase_step, erase_guard, unfold_step]
    exact .step (guards (ih t))
  | br b k =>
    simp only [translate_br, interp_mrec_br, erase_br, erase_guard, unfold_br]
    exact .br fun a ↦ guards (ih (k a))
  | vis e k =>
    cases e with
    | inl e =>
      cases e with
      | inl d =>
        simp only [translate_vis, Logged.reassoc, id_eq, erase_vis, interp_mrec_vis_inl,
          erase_guard, unfold_guard]
        exact .guard (by simpa only [Tisl.Yield.translate_bind, erase_bind] using ih (h d >>= k))
      | inr e =>
        simp only [translate_vis, Logged.reassoc, id_eq, erase_vis, interp_mrec_vis_inr,
          erase_guard, unfold_vis]
        refine .vis rfl fun a b hab ↦ ?_
        cases eq_of_heq hab
        exact guards (ih (k a))
    | inr r =>
      simp only [translate_vis, Logged.reassoc, id_eq, interp_mrec_vis_inr, erase_trace,
        erase_guard, interp_mrec_guard_eq, unfold_guard]
      exact .skipL rfl (by rw [unfold_guard]; exact .guard (ih (k ())))

/-- The logged recursive runtime simulates plain recursion for every relation on root results. -/
theorem agrees_interp_mrec {h : (d : D.I) → Logged (D ⊕ₑ E) B (D.O d)}
    {g : (d : D.I) → CTree (D ⊕ₑ E) B (D.O d)} {t : Logged (D ⊕ₑ E) B X}
    {s : CTree (D ⊕ₑ E) B Y} (hh : ∀ d, eutt Eq (erase (h d).meaning) (g d))
    (ht : eutt Q (erase t.meaning) s) :
    eutt Q (erase (Runtime.interp_mrec h t).meaning) (interp_mrec g s) := by
  change eutt Q (erase (Producer.interp_mrec (fun d ↦ Producer.translate Logged.reassoc (h d))
    (Producer.translate Logged.reassoc t)).meaning) _
  unfold Logged at h t
  simp only [Producer.meaning_interp_mrec_eq, Producer.meaning_translate_eq]
  exact ruttc_eutt_l _ _ _ (erase_mrec (fun d ↦ (h d).meaning) t.meaning) (eutt_interp_mrec hh ht)

end Vellvm.Semantics.Instrumentation
