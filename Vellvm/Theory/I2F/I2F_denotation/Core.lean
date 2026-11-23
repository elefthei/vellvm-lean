module

public import Vellvm.Theory.I2F.I2F_denotation.Context
public import Vellvm.Theory.I2F.Refinement.TreeLaws

@[expose] public section
namespace Vellvm.Theory.I2F.I2F_denotation
open Semantics.DynamicValues Semantics.LLVMEvents Semantics.EOU Syntax.DynamicTypes Refinement
open Utils.rutt_cutoff (ruttc_bind ruttc_trigger ruttc_ret)
open Tree (Runtime NoChoice)
open ITree (Effect Subeffect)

/-- The CFG specialization keeps the event and answer relations fixed across both sides of bind. -/
theorem cfg_bind {X Y U V : Type} {RR : X → Y → Prop} {SR : U → V → Prop}
    {t : @CFGtop PInf X} {s : @CFGtop PFin Y} {f : X → @CFGtop PInf U} {g : Y → @CFGtop PFin V}
    (h : I2F_refine_CFG RR t s) (k : ∀ x y, RR x y → I2F_refine_CFG SR (f x) (g y)) :
    I2F_refine_CFG SR (t >>= f) (s >>= g) := ruttc_bind _ _ _ _ RR SR t s f g h k

/-- A request is embedded before it is triggered; its subeffect maps each answer back. -/
theorem cfg_emit {D₁ D₂ : Effect} [i : D₁ -< @CFGEtop PInf] [j : D₂ -< @CFGEtop PFin]
    (e : D₁.I) (f : D₂.I) {RR : D₁.O e → D₂.O f → Prop}
    (pre : I2FE_CFG (i.map e).1 (j.map f).1)
    (post : ∀ a b, I2FA_CFG (i.map e).1 a (j.map f).1 b → RR ((i.map e).2 a) ((j.map f).2 b)) :
    I2F_refine_CFG RR (Runtime.emit (E := D₁) e) (Runtime.emit (E := D₂) f) := by
  apply cfg_bind (RR := fun a b ↦ I2FA_CFG (i.map e).1 a (j.map f).1 b)
    (ruttc_trigger (i.map e).1 (j.map f).1 pre (fun _ _ h ↦ h))
  intro a b h
  exact ruttc_ret _ _ (post a b h)

theorem refine_dvalue_base_map' {l : @CFGtop PInf (@dvalue_base PInf)}
    {r : @CFGtop PFin (@dvalue_base PFin)} (h : I2F_refine_CFG I2F_dvalue_base l r) :
    I2F_refine_CFG I2F_dvalue ((@DVALUE_Base PInf) <$> l) ((@DVALUE_Base PFin) <$> r) :=
  refine_dvalue_base_map_gen l r h

theorem I2F_draw_CFG (dt : dtyp) :
    I2F_refine_CFG I2F_dvalue (draw (Pa := PInf) dt) (draw (Pa := PFin) dt) :=
  cfg_emit (D₁ := @DrawE PInf) (D₂ := @DrawE PFin) (.Draw dt) (.Draw dt) rfl (fun _ _ h ↦ h)

theorem I2F_refine_lift' {X Y : Type} (RR : X → Y → Prop) (l : EOU X) (r : EOU Y) :
    I2F_EOU RR l r → I2F_refine_CFG RR (EOU_to_itree l) (EOU_to_itree r) :=
  I2F_refine_lift_gen I2FE_CFG_Throw RR l r

theorem cfg_raise {X Y : Type} (R : X → Y → Prop) (l r : IRString) :
    I2F_refine_CFG R («raise» l) («raise» r) :=
  I2F_refine_lift' R _ _ (I2F_EOU_error l r)

end Vellvm.Theory.I2F.I2F_denotation
