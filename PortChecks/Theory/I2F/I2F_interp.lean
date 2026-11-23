import PortChecks.SourceType
import PortChecks.Theory.I2F.I2F_interp.State
import PortChecks.Theory.I2F.I2F_interp.Environment
import PortChecks.Theory.I2F.I2F_interp.Intrinsics
import PortChecks.Theory.I2F.I2F_interp.Memory
import Vellvm.Theory.I2F.I2F_interp

open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_interp
open Vellvm.Semantics.InterpretationStack Vellvm.Semantics.Handlers.Intrinsics Vellvm.Semantics.LLVMEvents
open Vellvm.Utils.RelationsUtil (prod_rel)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_interp_intrinsics"
  I2F_interp_intrinsics : ∀ {X Y : Type} (RR : X → Y → Prop) (t : @MCFGtop PInf X) (u : @MCFGtop PFin Y),
    I2F_refine_MCFG RR t u → I2F_refine_MCFG RR (interp_intrinsics (Pa := PInf) t) (interp_intrinsics (Pa := PFin) u)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_interp_vellvm_h"
  I2F_interp_vellvm_h : ∀ (e : (@MCFGEtop PInf).I) (f : (@MCFGEtop PFin).I), I2FE_MCFG e f →
    ∀ (s : @FusedS PInf) (t : @FusedS PFin), I2F_FusedS s t →
    I2F_refine_MCFGbot (prod_rel (fun a b ↦ I2FA_MCFG e a f b) I2F_FusedS)
      (@interp_vellvm_h PInf e s) (@interp_vellvm_h PFin f t)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|ruttc_interp_state_specialized"
  ruttc_interp_state_specialized : ∀ {X Y : Type} (RR : X → Y → Prop) (t : @MCFGtop PInf X) (u : @MCFGtop PFin Y),
    I2F_refine_MCFG RR t u → ∀ (s : @FusedS PInf) (z : @FusedS PFin), I2F_FusedS s z →
    I2F_refine_MCFGbot (prod_rel RR I2F_FusedS)
      (CTree.interp_state (@interp_vellvm_h PInf) t s) (CTree.interp_state (@interp_vellvm_h PFin) u z)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_interp_mcfg"
  I2F_interp_mcfg : ∀ {X : Type} (t : @MCFGtop PInf X) (u : @MCFGtop PFin X),
    I2F_refine_MCFG Eq t u → ∀ (s : @FusedS PInf) (z : @FusedS PFin), I2F_FusedS s z →
    I2F_refine_MCFGbot (prod_rel Eq I2F_FusedS) (interp_mcfg (Pa := PInf) t s) (interp_mcfg (Pa := PFin) u z)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_interp_mcfg_bind"
  I2F_interp_mcfg_bind : ∀ {X Y T U : Type} (RR : X → Y → Prop) (RT : T → U → Prop)
    (p : @MCFGtop PInf X) (q : @MCFGtop PFin Y) (k : X → @MCFGtop PInf T) (l : Y → @MCFGtop PFin U),
    I2F_refine_MCFG RR p q → (∀ a b, RR a b → I2F_refine_MCFG RT (k a) (l b)) →
    ∀ (s : @FusedS PInf) (z : @FusedS PFin), I2F_FusedS s z →
      I2F_refine_MCFGbot (prod_rel RT I2F_FusedS)
        (interp_mcfg (Pa := PInf) (p >>= k) s) (interp_mcfg (Pa := PFin) (q >>= l) z)
