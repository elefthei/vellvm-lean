module

public import Vellvm.Theory.I2F.Refinement.Events
public import Vellvm.Theory.I2F.Refinement.EOU

@[expose] public section
namespace Vellvm.Theory.I2F.Refinement
open Semantics.LLVMEvents Semantics.DynamicValues
open ITree (Effect Subeffect)
open Utils.rutt_cutoff (prerel postrel pred1)

def I2FE_MCFG : prerel (@MCFGEtop PInf) (@MCFGEtop PFin) :=
  sum_prerel I2FE_ExternalCall (sum_prerel I2FE_Intrinsic (sum_prerel I2FE_Global
    (sum_prerel (sum_prerel I2FE_Local I2FE_Stack) (sum_prerel I2FE_Memory
      (sum_prerel I2FE_Draw (sum_prerel I2FE_OOM (sum_prerel I2FE_Exc
        (sum_prerel I2FE_UB (sum_prerel I2FE_Debug I2FE_Failure)))))))))

def I2FA_MCFG : postrel (@MCFGEtop PInf) (@MCFGEtop PFin) :=
  sum_postrel I2FA_ExternalCall (sum_postrel I2FA_Intrinsic (sum_postrel I2FA_Global
    (sum_postrel (sum_postrel I2FA_Local I2FA_Stack) (sum_postrel I2FA_Memory
      (sum_postrel I2FA_Draw (sum_postrel I2FA_OOM (sum_postrel I2FA_Exc
        (sum_postrel I2FA_UB (sum_postrel I2FA_Debug I2FA_Failure)))))))))

def I2FE_CFG : prerel (@CFGEtop PInf) (@CFGEtop PFin) := sum_prerel I2FE_Call I2FE_MCFG
def I2FA_CFG : postrel (@CFGEtop PInf) (@CFGEtop PFin) := sum_postrel I2FA_Call I2FA_MCFG

def I2FE_MCFGbot : prerel (@MCFGEbot PInf) (@MCFGEbot PFin) :=
  sum_prerel I2FE_ExternalCall (sum_prerel I2FE_OOM (sum_prerel I2FE_Exc
    (sum_prerel I2FE_UB (sum_prerel I2FE_Debug I2FE_Failure))))

def I2FA_MCFGbot : postrel (@MCFGEbot PInf) (@MCFGEbot PFin) :=
  sum_postrel I2FA_ExternalCall (sum_postrel I2FA_OOM (sum_postrel I2FA_Exc
    (sum_postrel I2FA_UB (sum_postrel I2FA_Debug I2FA_Failure))))

abbrev requestIn {D E : Effect} [s : D -< E] (d : D.I) : E.I := (s.map d).1

inductive cutUB {E : Effect} [UBE -< E] : pred1 E where
  | CutUB (u : Unit) : cutUB (requestIn (D := UBE) (ThrowUB u))

inductive cutOOM {E : Effect} [OOME -< E] : pred1 E where
  | CutOOM (u : Unit) : cutOOM (requestIn (D := OOME) (ThrowOOM u))

export cutUB (CutUB)
export cutOOM (CutOOM)

def I2F_refine_MCFG {X Y : Type} (RR : X → Y → Prop) : @MCFGtop PInf X → @MCFGtop PFin Y → Prop :=
  Tree.ruttc cutUB cutOOM I2FE_MCFG I2FA_MCFG RR

def I2F_refine_CFG {X Y : Type} (RR : X → Y → Prop) : @CFGtop PInf X → @CFGtop PFin Y → Prop :=
  Tree.ruttc cutUB cutOOM I2FE_CFG I2FA_CFG RR

def I2F_refine_MCFGbot {X Y : Type} (RR : X → Y → Prop) : @MCFGbot PInf X → @MCFGbot PFin Y → Prop :=
  Tree.ruttc cutUB cutOOM I2FE_MCFGbot I2FA_MCFGbot RR

def I2F_refine : @MCFGtop PInf (@dvalue PInf) → @MCFGtop PFin (@dvalue PFin) → Prop :=
  I2F_refine_MCFG I2F_dvalue

end Vellvm.Theory.I2F.Refinement
