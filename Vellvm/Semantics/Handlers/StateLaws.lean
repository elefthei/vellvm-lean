module

public import Vellvm.Tree.Runtime
public import Vellvm.Tree.StrictEq
public import Vellvm.Utils.rutt_cutoff

/-! State interpretation preserves head-sensitive equality; only weak equality erases the
administrative guard after a handled event. -/
@[expose] public section
namespace Vellvm.Semantics.Handlers.StateLaws

open ITree (Effect)
open CTree Coinduction Vellvm.Tree
open Vellvm.Utils.ListUtil (eqit_bind)
open Vellvm.Utils.rutt_cutoff (ruttc_bind_bchain)

universe u v
variable {E F B : Effect.{u}} {S X : Type u}

def Worker.forward {M : Effect.{u} → Effect.{u} → Type u → Type v} [Runtime M]
    {E B : Effect.{u}} {S : Type u} (e : E.I) (s : S) : M E B (E.O e × S) := do
  let x ← Runtime.trigger e
  pure (x, s)

variable (h : (e : E.I) → S → CTree F B (E.O e × S))

private theorem interp_eutt : ∀ (t u : CTree E B X), eutt Eq t u → ∀ s,
    eutt Eq (interp_state h t s) (interp_state h u s) := by
  coinduction C hc ih
  intro t u ht s
  have bindGuard {A : Type u} (p : CTree F B A) (k l : A → CTree F B (X × S))
      (hk : ∀ a, C (k a) (l a)) :
      Layer (eqitComparison F Eq true true) C
        (p >>= fun a ↦ (k a).guard).unfold (p >>= fun a ↦ (l a).guard).unfold := by
    apply ruttc_bind_bchain _ _ _ _ Eq C hc A A Eq _ _ _ _ (eqit_refl true true p)
    rintro a _ rfl
    change Layer _ C _ _
    simp only [unfold_guard]
    exact .guard (hk a)
  suffices ∀ l r, Layer (eqitComparison E Eq true true) (eutt Eq) l r →
      Layer (eqitComparison F Eq true true) C (interp_state h (CTree.fold l) s).unfold
        (interp_state h (CTree.fold r) s).unfold by
    simpa only [layerMon, fold_unfold] using this _ _ (related_iff.mp ht)
  intro l r hr
  induction hr with
  | ret he => cases he; simp only [fold_ret, ret_eq_pure, interp_state_ret, unfold_pure]; exact .ret rfl
  | stuck => simp only [fold_stuck, interp_state_stuck, unfold_stuck]; exact .stuck
  | guard ht => simp only [fold_guard, interp_state_guard, unfold_guard]; exact .guard (ih _ _ ht s)
  | skipL flag _ hi =>
    simp only [fold_guard, interp_state_guard, unfold_guard]
    exact .skipL flag (by simpa only [fold_unfold] using hi)
  | skipR flag _ hi =>
    simp only [fold_guard, interp_state_guard, unfold_guard]
    exact .skipR flag (by simpa only [fold_unfold] using hi)
  | step ht =>
    simp only [fold_step, interp_state_step, unfold_step]
    apply Layer.step (b_chain hc _ _ ?_)
    change Layer _ C _ _
    simp only [unfold_guard]
    exact .guard (ih _ _ ht s)
  | vis he hk =>
    cases he
    simp only [fold_vis, interp_state_vis]
    exact bindGuard _ _ _ fun a ↦ ih _ _ (hk a.1 a.1 HEq.rfl) a.2
  | br hk =>
    simp only [fold_br, interp_state_br]
    exact bindGuard _ _ _ fun a ↦ ih _ _ (hk a) s
  | cutL hf | cutR hf => exact hf.elim

theorem interp_congr {b : Bool} {t u : CTree E B X} (ht : eqit Eq b b t u) (s : S) :
    eqit Eq b b (interp_state h t s) (interp_state h u s) := by
  cases b with
  | false => exact eqit_strict_iff_eq.mpr (congrArg (fun q ↦ interp_state h q s) (eqit_strict_iff_eq.mp ht))
  | true => exact interp_eutt h t u ht s

theorem vis_eutt (e : E.I) (k : E.O e → CTree E B X) (s : S) :
    eutt Eq (interp_state h (.vis e k) s) (h e s >>= fun a ↦ interp_state h (k a.1) a.2) := by
  rw [interp_state_vis]
  apply eqit_bind _ _ _ (eqit_refl true true _)
  rintro a _ rfl
  exact Related.guard_left rfl (eqit_refl true true _)

theorem trigger_eutt (e : E.I) (s : S) :
    eutt Eq (interp_state h (CTree.trigger e : CTree E B (E.O e)) s) (h e s) := by
  rw [interp_state_trigger]
  conv => rhs; rw [← bind_pure (h e s)]
  apply eqit_bind _ _ _ (eqit_refl true true _)
  rintro a _ rfl
  exact Related.guard_left rfl (eqit_refl true true _)

end Vellvm.Semantics.Handlers.StateLaws
