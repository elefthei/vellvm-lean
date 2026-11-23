import PortChecks.SourceType
import Vellvm.Theory.I2F.Refinement.TreeLaws

namespace PortChecks.RefinementTree
open Vellvm Vellvm.Tree Vellvm.Theory.I2F.Refinement Vellvm.Semantics.DynamicValues
open Vellvm.Utils.rutt_cutoff (pred1 prerel postrel eqp1 sum_pred1 FF1)
open Vellvm.Semantics.LLVMEvents Vellvm.Semantics.EOU
open ITree (Effect Subeffect)
open CTree (CTree)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_cutUB_CFG"
  I2F_cutUB_CFG : eqp1 (E := @CFGEtop PInf) cutUB (sum_pred1 FF1 (cutUB (E := @MCFGEtop PInf)))

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_cutOOM_CFG"
  I2F_cutOOM_CFG : eqp1 (E := @CFGEtop PFin) cutOOM (sum_pred1 FF1 (cutOOM (E := @MCFGEtop PFin)))

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_CFG_sum"
  I2FE_CFG_sum : ∀ (l : (@CFGEtop PInf).I) (r : (@CFGEtop PFin).I), I2FE_CFG l r →
    Utils.rutt_cutoff.sum_prerel I2FE_Call I2FE_MCFG l r

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_CFG_sum"
  I2FA_CFG_sum : ∀ (l : (@CFGEtop PInf).I) (a : (@CFGEtop PInf).O l)
    (r : (@CFGEtop PFin).I) (b : (@CFGEtop PFin).O r),
    Utils.rutt_cutoff.sum_postrel I2FA_Call I2FA_MCFG l a r b → I2FA_CFG l a r b

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|refine_dvalue_base_map_gen"
  refine_dvalue_base_map_gen : ∀ {E F B : Effect} {L : pred1 E} {R : pred1 F}
    {P : prerel E F} {Q : postrel E F}
    (l : CTree E B (@dvalue_base PInf)) (r : CTree F B (@dvalue_base PFin)),
    ruttc L R P Q I2F_dvalue_base l r → ruttc L R P Q I2F_dvalue
      ((@DVALUE_Base PInf) <$> l) ((@DVALUE_Base PFin) <$> r)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_refine_lift_gen"
  I2F_refine_lift_gen : ∀ {E F B : Effect} [FailureE -< E] [OOME -< E] [UBE -< E]
    [FailureE -< F] [OOME -< F] [UBE -< F] {P : prerel E F} {Q : postrel E F},
    (∀ u v : Unit, P (requestIn (D := FailureE) (Throw u)) (requestIn (D := FailureE) (Throw v))) →
    ∀ {X Y : Type} (RR : X → Y → Prop) (l : EOU X) (r : EOU Y),
    I2F_EOU RR l r → ruttc (B := B) cutUB cutOOM P Q RR (EOU_to_itree l) (EOU_to_itree r)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_MCFG_Throw"
  I2FE_MCFG_Throw : ∀ u v : Unit, I2FE_MCFG
    (requestIn (D := FailureE) (Throw u)) (requestIn (D := FailureE) (Throw v))

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_MCFGbot_Throw"
  I2FE_MCFGbot_Throw : ∀ u v : Unit, I2FE_MCFGbot
    (requestIn (D := FailureE) (Throw u)) (requestIn (D := FailureE) (Throw v))

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_CFG_Throw"
  I2FE_CFG_Throw : ∀ u v : Unit, I2FE_CFG
    (requestIn (D := FailureE) (Throw u)) (requestIn (D := FailureE) (Throw v))

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_refine_lift"
  I2F_refine_lift : ∀ {X Y : Type} (RR : X → Y → Prop) (l : EOU X) (r : EOU Y),
    I2F_EOU RR l r → I2F_refine_MCFG RR (EOU_to_itree l) (EOU_to_itree r)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_refine_lift_bot"
  I2F_refine_lift_bot : ∀ {X Y : Type} (RR : X → Y → Prop) (l : EOU X) (r : EOU Y),
    I2F_EOU RR l r → I2F_refine_MCFGbot RR (EOU_to_itree l) (EOU_to_itree r)

end PortChecks.RefinementTree
