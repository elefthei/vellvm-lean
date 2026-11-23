module

public import Vellvm.Tree.Runtime
public import Vellvm.Utils.rutt_cutoff

/-! Refining the outputs of a state interpreter on an input with no branch requests. -/
@[expose] public section
namespace Vellvm.Semantics.Resolution
open CTree Coinduction Vellvm.Tree
open ITree (Effect)

variable {E F G B D : Effect} {X S : Type} [F -< G] [NoChoice -< B] [NoChoice -< D]

theorem refine_state_handler (schedule : (c : B.I) → CTree G D (B.O c))
    (model : (e : E.I) → S → CTree F B (E.O e × S))
    (reference : (e : E.I) → S → CTree G D (E.O e × S))
    (handle : ∀ e s, eutt Eq (refine schedule (model e s)) (reference e s)) :
    ∀ (t : CTree E NoChoice X) (s : S),
      eutt Eq (refine schedule (interp_state model t s)) (interp_state reference t s) := by
  coinduction C hc ih
  intro t s
  change Layer _ C _ _
  cases t with
  | ret x => simp only [interp_state_ret, refine_ret, unfold_pure]; exact .ret rfl
  | stuck =>
    simp only [interp_state_stuck]
    rw [unfold_refine, unfold_stuck]
    exact .stuck
  | br b _ => exact PEmpty.elim b
  | guard t =>
    simp only [interp_state_guard, refine_guard, unfold_guard]
    exact .guard (ih t s)
  | step t =>
    simp only [interp_state_step, refine_step, refine_guard, unfold_step]
    apply Layer.step
    apply b_chain hc
    change Layer _ C _ _
    rw [unfold_guard, unfold_guard]
    exact .skipL rfl (by rw [unfold_guard]; exact .guard (ih t s))
  | vis e k =>
    simp only [interp_state_vis, refine_bind, refine_guard]
    apply Utils.rutt_cutoff.ruttc_bind_bchain _ _ _ _ Eq C hc _ _ Eq _ _ _ _ (handle e s)
    rintro ⟨a, s'⟩ _ rfl
    change Layer _ C _ _
    rw [unfold_guard, unfold_guard]
    exact .guard (ih (k a) s')

end Vellvm.Semantics.Resolution
