import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_interp.Environment

open Vellvm.Semantics.LLVMEvents Vellvm.Semantics.InterpretationStack
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_interp
open Vellvm.Utils.RelationsUtil (prod_rel)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_fused_global"
  I2F_fused_global : ∀ (e : (@GlobalE PInf).I) (f : (@GlobalE PFin).I), I2FE_Global e f →
    ∀ s t, I2F_FusedS s t →
      I2F_refine_MCFGbot (prod_rel (fun x y ↦ I2FA_Global e x f y) I2F_FusedS)
        (@fused_global PInf e s) (@fused_global PFin f t)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_fused_local"
  I2F_fused_local : ∀ (e : (@LocalE PInf).I) (f : (@LocalE PFin).I), I2FE_Local e f →
    ∀ s t, I2F_FusedS s t →
      I2F_refine_MCFGbot (prod_rel (fun x y ↦ I2FA_Local e x f y) I2F_FusedS)
        (@fused_local PInf e s) (@fused_local PFin f t)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_fused_stack"
  I2F_fused_stack : ∀ (e : (@StackE PInf).I) (f : (@StackE PFin).I), I2FE_Stack e f →
    ∀ s t, I2F_FusedS s t →
      I2F_refine_MCFGbot (prod_rel (fun x y ↦ I2FA_Stack e x f y) I2F_FusedS)
        (@fused_stack PInf e s) (@fused_stack PFin f t)
