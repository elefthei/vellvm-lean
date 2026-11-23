import Vellvm.Semantics.InterpretationStack
import Vellvm.Theory.I2F.Refinement.Basic

namespace Vellvm.Theory.I2F.I2F_interp
open ITree (Effect Subeffect)
open Vellvm.Tree CTree Refinement Semantics.LLVMEvents
open Semantics.InterpretationStack Semantics.Interfaces.Params
open Utils.rutt_cutoff (ruttc_trigger ruttc_ret)
open Utils.RelationsUtil (prod_rel)

private abbrev Residual [Params] := OOME ⊕ₑ LLVMExcE ⊕ₑ UBE ⊕ₑ DebugE ⊕ₑ FailureE

private def residualIn [Pa : Params] (d : Residual.I) : MCFGEtop.I :=
  .inr (.inr (.inr (.inr (.inr (.inr d)))))

/-- Forwarding preserves the return state and maps the dependent answer back along the subeffect. -/
private theorem forward_head [Pa : Params] {F : Effect} [i : F -< MCFGEbot] (e : F.I)
    (s : FusedS) : fused_trigger (F := F) e s =
      .vis (i.map e).1 (fun a ↦ .ret ((i.map e).2 a, s)) := by
  change ((CTree.trigger (i.map e).1 >>= fun a ↦ pure ((i.map e).2 a)) >>=
    fun x ↦ pure (x, s)) = _
  simp only [CTree.trigger, vis_bind, pure_bind']
  rfl

private theorem external_head [Pa : Params] (e : ExternalCallE.I) (s : FusedS) :
    interp_vellvm_h (.inl e) s = .vis (.inl e) (fun a ↦ .ret (a, s)) :=
  forward_head (F := ExternalCallE) e s

private theorem residual_head [Pa : Params] (e : Residual.I) (s : FusedS) :
    interp_vellvm_h (residualIn e) s = .vis (.inr e) (fun a ↦ .ret (a, s)) := by
  rcases e with e | e | e | e | e <;> exact forward_head (F := Residual) _ s

theorem forward_external {RS : @FusedS PInf → @FusedS PFin → Prop}
    (e : (@ExternalCallE PInf).I) (f : (@ExternalCallE PFin).I) (he : I2FE_ExternalCall e f)
    (s : @FusedS PInf) (t : @FusedS PFin) (hs : RS s t) :
    I2F_refine_MCFGbot (prod_rel (fun a b ↦ I2FA_ExternalCall e a f b) RS)
      (@interp_vellvm_h PInf (.inl e) s) (@interp_vellvm_h PFin (.inl f) t) := by
  rw [@external_head PInf e s, @external_head PFin f t]
  refine (related_vis_iff _ _ _ _).mpr (.inr (.inr ⟨he, ?_⟩))
  exact fun _ _ hab ↦ ruttc_ret _ _ ⟨hab, hs⟩

theorem forward_residual {RS : @FusedS PInf → @FusedS PFin → Prop}
    (e : (@Residual PInf).I) (f : (@Residual PFin).I)
    (he : I2FE_MCFG (@residualIn PInf e) (@residualIn PFin f))
    (s : @FusedS PInf) (t : @FusedS PFin) (hs : RS s t) :
    I2F_refine_MCFGbot (prod_rel (fun a b ↦ I2FA_MCFG (@residualIn PInf e) a (@residualIn PFin f) b) RS)
      (@interp_vellvm_h PInf (@residualIn PInf e) s) (@interp_vellvm_h PFin (@residualIn PFin f) t) := by
  rw [@residual_head PInf e s, @residual_head PFin f t]
  refine (related_vis_iff _ _ _ _).mpr (.inr (.inr ⟨he, ?_⟩))
  exact fun _ _ hab ↦ ruttc_ret _ _ ⟨hab, hs⟩

theorem forward_cutUB (e : (@MCFGEtop PInf).I) (cut : cutUB e) (s : @FusedS PInf) :
    ∃ d k, cutUB d ∧ @interp_vellvm_h PInf e s = .vis d k := by
  cases cut with
  | CutUB u => exact ⟨_, _, CutUB u, @residual_head PInf (.inr (.inr (.inl (ThrowUB u)))) s⟩

theorem forward_cutOOM (e : (@MCFGEtop PFin).I) (cut : cutOOM e) (s : @FusedS PFin) :
    ∃ d k, cutOOM d ∧ @interp_vellvm_h PFin e s = .vis d k := by
  cases cut with
  | CutOOM u => exact ⟨_, _, CutOOM u, @residual_head PFin (.inl (ThrowOOM u)) s⟩

end Vellvm.Theory.I2F.I2F_interp
