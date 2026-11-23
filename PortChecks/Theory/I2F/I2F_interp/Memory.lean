import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_interp.Memory

namespace Vellvm.Theory.I2F.I2F_interp
open Refinement I2F_memory I2F_memS
open Semantics.InterpretationStack Semantics.Implementations.Memory Semantics.Handlers.Memory
open Semantics.LLVMEvents Utils.RelationsUtil

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_fresh_provenance_eq"
  I2F_fresh_provenance_eq : ∀ (s : @State PInf) (t : @State PFin), I2F_State s t →
    PInf.PROV.next_provenance (@state_provenance PInf s) =
      PFin.PROV.next_provenance (@state_provenance PFin t)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_memM_interp"
  I2F_memM_interp : ∀ (X Y : Type) (RR : X → Y → Prop)
    (l : @ConcreteMem PInf X) (r : @ConcreteMem PFin Y), I2F_memS I2F_State RR l r →
    ∀ (s : @State PInf) (t : @State PFin), I2F_State s t →
      I2F_refine_MCFGbot (prod_rel RR I2F_State)
        (memM_interp (Pa := PInf) l s) (memM_interp (Pa := PFin) r t)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_fused_memory"
  I2F_fused_memory : ∀ (e : (@MemoryE PInf).I) (f : (@MemoryE PFin).I), I2FE_Memory e f →
    ∀ (s : @FusedS PInf) (t : @FusedS PFin), I2F_FusedS s t →
      I2F_refine_MCFGbot (prod_rel (fun a b ↦ I2FA_Memory e a f b) I2F_FusedS)
        (@fused_memory PInf e s) (@fused_memory PFin f t)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_fused_intrinsic"
  I2F_fused_intrinsic : ∀ (e : (@IntrinsicE PInf).I) (f : (@IntrinsicE PFin).I),
    I2FE_Intrinsic e f → ∀ (s : @FusedS PInf) (t : @FusedS PFin), I2F_FusedS s t →
      I2F_refine_MCFGbot (prod_rel (fun a b ↦ I2FA_Intrinsic e a f b) I2F_FusedS)
        (@fused_intrinsic PInf e s) (@fused_intrinsic PFin f t)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_fused_draw"
  I2F_fused_draw : ∀ (e : (@DrawE PInf).I) (f : (@DrawE PFin).I), I2FE_Draw e f →
    ∀ (s : @FusedS PInf) (t : @FusedS PFin), I2F_FusedS s t →
      I2F_refine_MCFGbot (prod_rel (fun a b ↦ I2FA_Draw e a f b) I2F_FusedS)
        (@fused_draw PInf e s) (@fused_draw PFin f t)

end Vellvm.Theory.I2F.I2F_interp
