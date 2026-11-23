import Vellvm.Theory.I2F.I2F_denotation.CFG
import Vellvm.Theory.I2F.I2F_denotation.Frames
import Vellvm.Theory.I2F.I2F_denotation.Exceptions
import Vellvm.Theory.I2F.I2F_denotation.Mrec

namespace Vellvm.Theory.I2F.I2F_denotation
open Semantics.Denotation Syntax.LLVMAst Syntax.CFG Syntax.DynamicTypes Refinement
open Semantics.LLVMEvents (MemoryE StackE StackPop MemPop)
open Utils.RelationsUtil (TT)

private theorem popFrame : I2F_refine_CFG TT (pop_call_frame (Pa := PInf))
    (pop_call_frame (Pa := PFin)) := by
  unfold pop_call_frame Worker.pop_call_frame
  refine cfg_bind (RR := TT) (cfg_emit (D₁ := @StackE PInf) (D₂ := @StackE PFin)
    (@StackPop PInf) (@StackPop PFin) trivial (fun _ _ _ ↦ trivial)) (fun _ _ _ ↦ ?_)
  exact cfg_emit (D₁ := @MemoryE PInf) (D₂ := @MemoryE PFin)
    (@MemPop PInf) (@MemPop PFin) trivial (fun _ _ _ ↦ trivial)

theorem I2F_denote_function (d : definition dtyp (cfg dtyp)) :
    I2F_function_denotation (@denote_function PInf d) (@denote_function PFin d) := by
  intro cc t xs ys h
  unfold denote_function Worker.denote_function
  apply cfg_bind (I2F_refine_lift' Eq _ _ (I2F_EOU_refl _))
  intro _ _ _
  apply cfg_bind (I2F_apply_args_attrs _ _ h)
  intro vs ws hv
  apply cfg_bind (I2F_push_call_frame d hv)
  intro va vb hab
  apply cfg_bind (I2F_run_exc _ _ (I2F_denote_cfg d.df_instrs (.some va vb hab)))
  intro rv rw hr
  apply cfg_bind popFrame
  intro _ _ _
  exact I2F_check_call_return _ _ _ _ _ (I2F_targs_snd hv) hr

end Vellvm.Theory.I2F.I2F_denotation
