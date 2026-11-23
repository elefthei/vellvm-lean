import Vellvm.Theory.I2F.I2F_interp.Intrinsics
import Vellvm.Theory.I2F.I2F_interp.Environment
import Vellvm.Theory.I2F.I2F_interp.Memory
import Vellvm.Theory.I2F.I2F_interp.Forward
import Vellvm.Theory.I2F.I2F_interp.StateTransport

namespace Vellvm.Theory.I2F.I2F_interp
open Refinement Semantics.LLVMEvents Semantics.InterpretationStack Semantics.Handlers.Intrinsics
open Utils.rutt_cutoff (ruttc_interp_itree ruttc_trigger ruttc_bind)
open Utils.RelationsUtil (prod_rel)

theorem I2F_interp_intrinsics {X Y : Type} (RR : X → Y → Prop) (p : @MCFGtop PInf X)
    (q : @MCFGtop PFin Y) (hr : I2F_refine_MCFG RR p q) :
    I2F_refine_MCFG RR (interp_intrinsics (Pa := PInf) p) (interp_intrinsics (Pa := PFin) q) := by
  apply ruttc_interp_itree (interp_intrinsics_h (Pa := PInf)) (interp_intrinsics_h (Pa := PFin))
    _ _ _ p q hr
  · rintro _ ⟨u⟩; exact Tree.eqit_refl false false _
  · rintro _ ⟨u⟩; exact Tree.eqit_refl false false _
  · intro e f he
    rcases e with e | e | e <;> rcases f with f | f | f <;> try exact False.elim he
    · exact ruttc_trigger _ _ he fun _ _ h ↦ h
    · exact I2F_handle_intrinsics e f he
    · exact ruttc_trigger _ _ he fun _ _ h ↦ h

theorem I2F_interp_vellvm_h (e : (@MCFGEtop PInf).I) (f : (@MCFGEtop PFin).I)
    (he : I2FE_MCFG e f) (s : @FusedS PInf) (t : @FusedS PFin) (hs : I2F_FusedS s t) :
    I2F_refine_MCFGbot (prod_rel (fun a b ↦ I2FA_MCFG e a f b) I2F_FusedS)
      (@interp_vellvm_h PInf e s) (@interp_vellvm_h PFin f t) := by
  rcases e with e | e | e | (e | e) | e | e | e <;>
    rcases f with f | f | f | (f | f) | f | f | f <;> try exact False.elim he
  · exact forward_external e f he s t hs
  · exact I2F_fused_intrinsic e f he s t hs
  · exact I2F_fused_global e f he s t hs
  · exact I2F_fused_local e f he s t hs
  · exact I2F_fused_stack e f he s t hs
  · exact I2F_fused_memory e f he s t hs
  · exact I2F_fused_draw e f he s t hs
  · exact forward_residual e f he s t hs

theorem ruttc_interp_state_specialized {X Y : Type} (RR : X → Y → Prop)
    (p : @MCFGtop PInf X) (q : @MCFGtop PFin Y) (hpq : I2F_refine_MCFG RR p q)
    (s : @FusedS PInf) (t : @FusedS PFin) (hst : I2F_FusedS s t) :
    I2F_refine_MCFGbot (prod_rel RR I2F_FusedS)
      (CTree.interp_state (@interp_vellvm_h PInf) p s) (CTree.interp_state (@interp_vellvm_h PFin) q t) :=
  interp_state_related RR I2F_FusedS _ _ forward_cutUB forward_cutOOM I2F_interp_vellvm_h p q hpq s t hst

theorem I2F_interp_mcfg {R : Type} (p : @MCFGtop PInf R) (q : @MCFGtop PFin R)
    (hpq : I2F_refine_MCFG Eq p q) (s : @FusedS PInf) (t : @FusedS PFin) (hst : I2F_FusedS s t) :
    I2F_refine_MCFGbot (prod_rel Eq I2F_FusedS) (interp_mcfg (Pa := PInf) p s) (interp_mcfg (Pa := PFin) q t) :=
  ruttc_interp_state_specialized Eq _ _ (I2F_interp_intrinsics Eq p q hpq) s t hst

theorem I2F_interp_mcfg_bind {X Y T U : Type} (RR : X → Y → Prop) (RT : T → U → Prop)
    (p : @MCFGtop PInf X) (q : @MCFGtop PFin Y) (k : X → @MCFGtop PInf T) (l : Y → @MCFGtop PFin U)
    (hpq : I2F_refine_MCFG RR p q) (hkl : ∀ a b, RR a b → I2F_refine_MCFG RT (k a) (l b))
    (s : @FusedS PInf) (t : @FusedS PFin) (hst : I2F_FusedS s t) :
    I2F_refine_MCFGbot (prod_rel RT I2F_FusedS)
      (interp_mcfg (Pa := PInf) (p >>= k) s) (interp_mcfg (Pa := PFin) (q >>= l) t) :=
  ruttc_interp_state_specialized RT _ _
    (I2F_interp_intrinsics RT _ _ (ruttc_bind _ _ _ _ RR RT p q k l hpq hkl)) s t hst

end Vellvm.Theory.I2F.I2F_interp
