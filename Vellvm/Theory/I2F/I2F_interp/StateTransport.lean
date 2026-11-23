module

public import Vellvm.Utils.rutt_cutoff
public import Vellvm.Utils.RelationsUtil
public import CTree.Interp.FoldStateT

@[expose] public section
namespace Vellvm.Theory.I2F.I2F_interp
open ITree (Effect)
open CTree Coinduction Tree Utils.rutt_cutoff
open Utils.RelationsUtil (prod_rel)

/-- Transport a cutoff simulation through two state handlers, possibly changing both event rows.
A cut request must expose another cut head; a related request must relate every returned answer
and the state with which its continuation resumes. -/
theorem interp_state_related {E F G H B : Effect.{u}} {X Y S T : Type u}
    {L : pred1 E} {K : pred1 F} {P : prerel E F} {A : postrel E F}
    {L' : pred1 G} {K' : pred1 H} {P' : prerel G H} {A' : postrel G H}
    (R : X → Y → Prop) (RS : S → T → Prop)
    (h : (e : E.I) → S → CTree G B (E.O e × S))
    (g : (f : F.I) → T → CTree H B (F.O f × T))
    (cutL : ∀ e, L e → ∀ s, ∃ d k, L' d ∧ h e s = .vis d k)
    (cutR : ∀ f, K f → ∀ t, ∃ d k, K' d ∧ g f t = .vis d k)
    (events : ∀ e f, P e f → ∀ s t, RS s t → Tree.ruttc L' K' P' A'
      (prod_rel (fun a b ↦ A e a f b) RS) (h e s) (g f t)) :
    ∀ (p : CTree E B X) (q : CTree F B Y), Tree.ruttc L K P A R p q → ∀ s t, RS s t →
      Tree.ruttc L' K' P' A' (prod_rel R RS) (interp_state h p s) (interp_state g q t) := by
  coinduction C hc ih
  intro p q hpq s t hst
  suffices go : ∀ u v, ruttcF L K P A R (Tree.ruttc L K P A R) u v →
      ruttcF L' K' P' A' (prod_rel R RS) C
        (interp_state h (.fold u) s).unfold (interp_state g (.fold v) t).unfold by
    simpa only [layerMon, fold_unfold] using go _ _ (related_iff.mp hpq)
  intro u v hlayer
  induction hlayer with
  | ret hxy =>
    simp only [fold_ret, ret_eq_pure, interp_state_ret, unfold_pure]
    exact .ret ⟨hxy, hst⟩
  | guard hpq =>
    simp only [fold_guard, interp_state_guard, unfold_guard]
    exact .guard (ih _ _ hpq _ _ hst)
  | vis hef hk =>
    simp only [fold_vis, interp_state_vis]
    apply ruttc_bind_bchain L' K' P' A' (prod_rel R RS) C hc _ _ _ _ _ _ _
      (events _ _ hef s t hst)
    rintro ⟨a, s'⟩ ⟨b, t'⟩ ⟨hab, hst'⟩
    change Layer _ C _ _
    rw [unfold_guard, unfold_guard]
    exact .guard (ih _ _ (hk a b hab) s' t' hst')
  | skipL _ _ inner =>
    simp only [fold_guard, interp_state_guard, unfold_guard]
    exact .skipL rfl (by simpa only [fold_unfold] using inner)
  | skipR _ _ inner =>
    simp only [fold_guard, interp_state_guard, unfold_guard]
    exact .skipR rfl (by simpa only [fold_unfold] using inner)
  | cutL he =>
    obtain ⟨d, k, hd, heq⟩ := cutL _ he s
    simp only [fold_vis, interp_state_vis, heq, vis_bind, unfold_vis]
    exact .cutL hd
  | cutR hf =>
    obtain ⟨d, k, hd, heq⟩ := cutR _ hf t
    simp only [fold_vis, interp_state_vis, heq, vis_bind, unfold_vis]
    exact .cutR hd
  | stuck => simp only [fold_stuck, interp_state_stuck, unfold_stuck]; exact .stuck
  | step hpq =>
    simp only [fold_step, interp_state_step, unfold_step]
    apply Layer.step
    apply b_chain hc
    change Layer _ C _ _
    rw [unfold_guard, unfold_guard]
    exact .guard (ih _ _ hpq _ _ hst)
  | br hk =>
    simp only [fold_br, interp_state_br, CTree.branch', CTree.br', br_bind, pure_bind, unfold_br]
    apply Layer.br
    intro a
    apply b_chain hc
    change Layer _ C _ _
    rw [unfold_guard, unfold_guard]
    exact .guard (ih _ _ (hk _) _ _ hst)

end Vellvm.Theory.I2F.I2F_interp
