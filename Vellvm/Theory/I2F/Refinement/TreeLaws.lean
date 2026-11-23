module

public import Vellvm.Theory.I2F.Refinement.Basic

@[expose] public section
namespace Vellvm.Theory.I2F.Refinement
open ITree (Effect Subeffect)
open CTree (CTree)
open Semantics.LLVMEvents Semantics.DynamicValues Semantics.EOU
open Utils.rutt_cutoff (pred1 prerel postrel eqp1 sum_pred1 FF1 ruttc_ret ruttc_bind)
open Tree (ruttc)

theorem I2F_cutUB_CFG : eqp1 (E := @CFGEtop PInf) cutUB
    (sum_pred1 FF1 (cutUB (E := @MCFGEtop PInf))) := by
  intro e
  constructor
  · rintro ⟨u⟩; exact .inr _ (.CutUB u)
  · rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact h.elim
    · cases h with | CutUB u => exact .CutUB u

theorem I2F_cutOOM_CFG : eqp1 (E := @CFGEtop PFin) cutOOM
    (sum_pred1 FF1 (cutOOM (E := @MCFGEtop PFin))) := by
  intro e
  constructor
  · rintro ⟨u⟩; exact .inr _ (.CutOOM u)
  · rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact h.elim
    · cases h with | CutOOM u => exact .CutOOM u

theorem I2FE_CFG_sum (e : (@CFGEtop PInf).I) (f : (@CFGEtop PFin).I) :
    I2FE_CFG e f → Utils.rutt_cutoff.sum_prerel I2FE_Call I2FE_MCFG e f := by
  cases e <;> cases f <;> intro h <;> first | exact .inl h | exact .inr h | exact False.elim h

theorem I2FA_CFG_sum (e : (@CFGEtop PInf).I) (x : (@CFGEtop PInf).O e)
    (f : (@CFGEtop PFin).I) (y : (@CFGEtop PFin).O f) :
    Utils.rutt_cutoff.sum_postrel I2FA_Call I2FA_MCFG e x f y → I2FA_CFG e x f y := id

theorem refine_dvalue_base_map_gen {E F B : Effect} {L : pred1 E} {R : pred1 F}
    {P : prerel E F} {Q : postrel E F} (l : CTree E B (@dvalue_base PInf))
    (r : CTree F B (@dvalue_base PFin)) (h : ruttc L R P Q I2F_dvalue_base l r) :
    ruttc L R P Q I2F_dvalue ((@DVALUE_Base PInf) <$> l) ((@DVALUE_Base PFin) <$> r) :=
  ruttc_bind L R P Q I2F_dvalue_base I2F_dvalue l r _ _ h
    fun _ _ hv ↦ ruttc_ret _ _ (.I2F_dvalue_Base hv)

/-- Project the empty-answer witness through a subeffect; its answer type need not equal `Empty`. -/
private theorem abort_head {E B D : Effect} {X : Type} [s : D -< E] (d : D.I)
    (abs : D.O d → Empty) (msg : IRString) :
    (do Semantics.Instrumentation.Diagnostics.diagnostic (M := CTree) msg
        let a ← Tree.Runtime.emit (E := D) d
        nomatch abs a : CTree E B X) =
      .vis (requestIn (E := E) d) (fun a ↦ (abs ((s.map d).2 a)).elim) := by
  change ((pure () : CTree E B Unit) >>= fun _ ↦
    ((CTree.trigger (requestIn (E := E) d) >>= fun x ↦ pure ((s.map d).2 x)) >>=
      fun a ↦ (nomatch abs a : CTree E B X))) = _
  simp only [CTree.pure_bind', CTree.CTree.trigger, CTree.vis_bind]
  congr 1; funext a; exact (abs ((s.map d).2 a)).elim

theorem I2F_refine_lift_gen {E F B : Effect} [ef : FailureE -< E] [eo : OOME -< E] [eu : UBE -< E]
    [ff : FailureE -< F] [fo : OOME -< F] [fu : UBE -< F] {P : prerel E F} {Q : postrel E F}
    (hthrow : ∀ u v : Unit, P (requestIn (D := FailureE) (Throw u)) (requestIn (D := FailureE) (Throw v)))
    {X Y : Type} (RR : X → Y → Prop) (l : EOU X) (r : EOU Y) (h : I2F_EOU RR l r) :
    ruttc (B := B) cutUB cutOOM P Q RR (EOU_to_itree l) (EOU_to_itree r) := by
  cases h with
  | I2F_EOU_ret x y h => exact ruttc_ret _ _ h
  | I2F_EOU_error s t =>
    rw [show (EOU_to_itree (raise_error s) : CTree E B X) = _ from abort_head (D := FailureE) (Throw ()) id s,
        show (EOU_to_itree (raise_error t) : CTree F B Y) = _ from abort_head (D := FailureE) (Throw ()) id t]
    apply Tree.related_iff.mpr
    rw [CTree.unfold_vis, CTree.unfold_vis]
    exact .vis (hthrow () ()) fun a _ _ ↦ Empty.elim ((ef.map (Throw ())).2 a)
  | I2F_EOU_ub s m =>
    rw [show (EOU_to_itree (raise_ub s) : CTree E B X) = _ from abort_head (D := UBE) (ThrowUB ()) id s]
    exact Tree.Related.cut_left _ _ _ (.CutUB ())
  | I2F_EOU_oom m t =>
    rw [show (EOU_to_itree (raise_oom t) : CTree F B Y) = _ from abort_head (D := OOME) (ThrowOOM ()) id t]
    exact Tree.Related.cut_right _ _ _ (.CutOOM ())

theorem I2FE_MCFG_Throw (u v : Unit) : I2FE_MCFG
    (requestIn (D := FailureE) (Throw u)) (requestIn (D := FailureE) (Throw v)) := trivial

theorem I2FE_MCFGbot_Throw (u v : Unit) : I2FE_MCFGbot
    (requestIn (D := FailureE) (Throw u)) (requestIn (D := FailureE) (Throw v)) := trivial

theorem I2FE_CFG_Throw (u v : Unit) : I2FE_CFG
    (requestIn (D := FailureE) (Throw u)) (requestIn (D := FailureE) (Throw v)) := trivial

theorem I2F_refine_lift {X Y : Type} (RR : X → Y → Prop) (l : EOU X) (r : EOU Y) :
    I2F_EOU RR l r → I2F_refine_MCFG RR (EOU_to_itree l) (EOU_to_itree r) :=
  I2F_refine_lift_gen I2FE_MCFG_Throw RR l r

theorem I2F_refine_lift_bot {X Y : Type} (RR : X → Y → Prop) (l : EOU X) (r : EOU Y) :
    I2F_EOU RR l r → I2F_refine_MCFGbot RR (EOU_to_itree l) (EOU_to_itree r) :=
  I2F_refine_lift_gen I2FE_MCFGbot_Throw RR l r

end Vellvm.Theory.I2F.Refinement
