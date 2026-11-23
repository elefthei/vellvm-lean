import Vellvm.Semantics.Denotation
import Vellvm.Theory.I2F.I2F_denotation.Core
import Vellvm.Theory.I2F.I2F_attributes

namespace Vellvm.Theory.I2F.I2F_denotation
open Semantics.Denotation Syntax.DynamicTypes Refinement I2F_attributes
open Semantics.DynamicValues (dvalue_ptr_address)
open Semantics.LLVMEvents (CallE ExternalCallE Call ExternalCall)
open Numeric.Rocqlib (option_rel)
open Utils.rutt_cutoff (ruttc_mrec ruttc_weaken ruttc_ret)

theorem I2F_lookup_defn {l r v w} (hm : I2F_ctx l r) (hv : I2F_dvalue v w) :
    option_rel I2F_function_denotation (@lookup_defn PInf v l) (@lookup_defn PFin w r) := by
  unfold lookup_defn Worker.lookup_defn
  rw [I2F_dvalue_ptr_address hv]
  cases @dvalue_ptr_address PFin w with
  | none => exact .none
  | some k => exact hm k

private theorem callBody {l r} (hm : I2F_ctx l r) (d : (@CallE PInf).I) (e : (@CallE PFin).I)
    (he : I2FE_Call d e) : I2F_refine_CFG (fun x y ↦ I2FA_Call d x e y)
      (Worker.call_body (Pa := PInf) l d) (Worker.call_body (Pa := PFin) r e) := by
  rcases d with ⟨t, cc, v, xs⟩
  rcases e with ⟨t', cc', w, ys⟩
  obtain ⟨rfl, rfl, hv, ha⟩ := he
  unfold Worker.call_body
  refine cfg_bind (I2F_refine_lift' _ _ _ (I2F_check_callee hv)) (fun _ _ _ ↦ ?_)
  have hl : option_rel I2F_function_denotation (Worker.lookup_defn (Pa := PInf) (M := CTree.CTree) v l)
      (Worker.lookup_defn (Pa := PFin) (M := CTree.CTree) w r) :=
    I2F_lookup_defn hm hv
  generalize Worker.lookup_defn (Pa := PInf) (M := CTree.CTree) v l = f,
    Worker.lookup_defn (Pa := PFin) (M := CTree.CTree) w r = g at hl ⊢
  cases hl with
  | some f g hf => exact hf _ _ _ _ ha
  | none =>
    refine cfg_bind (RR := I2F_dvalue) (cfg_emit (D₁ := @ExternalCallE PInf) (D₂ := @ExternalCallE PFin)
      (@ExternalCall PInf _ v xs) (@ExternalCall PFin _ w ys) ⟨rfl, hv, ha⟩ (fun _ _ h ↦ h)) ?_
    exact fun _ _ h ↦ ruttc_ret _ _ (Sum.LiftRel.inr h)

theorem I2F_denote_mcfg (t : dtyp) {l r v w xs ys} (hv : I2F_dvalue v w) (ha : I2F_targs xs ys)
    (hm : I2F_ctx l r) : I2F_refine_MCFG (Sum.LiftRel I2F_dvalue I2F_dvalue)
      (@denote_mcfg PInf l t v xs) (@denote_mcfg PFin r t w ys) := by
  refine ruttc_mrec cutUB cutOOM I2FE_MCFG I2FA_MCFG I2FE_Call I2FA_Call
    (Worker.call_body (Pa := PInf) l) (Worker.call_body (Pa := PFin) r) ?_
    (@Call PInf t .CC_Ccc v xs) (@Call PFin t .CC_Ccc w ys)
    ⟨rfl, rfl, hv, ha⟩
  intro d e de
  exact ruttc_weaken cutUB _ cutOOM _ I2FE_CFG _ I2FA_CFG _ _ _
    (fun i ↦ (I2F_cutUB_CFG i).mp) (fun j ↦ (I2F_cutOOM_CFG j).mp) I2FE_CFG_sum
    I2FA_CFG_sum (fun _ _ h ↦ h) _ _ (callBody hm d e de)

end Vellvm.Theory.I2F.I2F_denotation
