import PortChecks.SourceType
import Vellvm.Theory.I2F.Refinement.Basic

namespace PortChecks.RefinementBasic
open Vellvm Vellvm.Theory.I2F.Refinement Vellvm.Semantics.LLVMEvents
open Vellvm.Semantics.DynamicValues
open Vellvm.Utils.rutt_cutoff (prerel postrel pred1)
open ITree (Effect Subeffect)
universe u

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|sum_prerel"
  sum_prerel : ∀ {E₁ E₂ D₁ D₂ : Effect.{u}},
    prerel E₁ D₁ → prerel E₂ D₂ → prerel (E₁ ⊕ₑ E₂) (D₁ ⊕ₑ D₂)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|inl_prerel"
  inl_prerel : ∀ {E₁ E₂ D₁ D₂ : Effect.{u}},
    prerel (E₁ ⊕ₑ E₂) (D₁ ⊕ₑ D₂) → prerel E₁ D₁

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|inr_prerel"
  inr_prerel : ∀ {E₁ E₂ D₁ D₂ : Effect.{u}},
    prerel (E₁ ⊕ₑ E₂) (D₁ ⊕ₑ D₂) → prerel E₂ D₂

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|sum_postrel"
  sum_postrel : ∀ {E₁ E₂ D₁ D₂ : Effect.{u}},
    postrel E₁ D₁ → postrel E₂ D₂ → postrel (E₁ ⊕ₑ E₂) (D₁ ⊕ₑ D₂)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|inl_postrel"
  inl_postrel : ∀ {E₁ E₂ D₁ D₂ : Effect.{u}},
    postrel (E₁ ⊕ₑ E₂) (D₁ ⊕ₑ D₂) → postrel E₁ D₁

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|inr_postrel"
  inr_postrel : ∀ {E₁ E₂ D₁ D₂ : Effect.{u}},
    postrel (E₁ ⊕ₑ E₂) (D₁ ⊕ₑ D₂) → postrel E₂ D₂

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|PInf"
  PInf : Semantics.Interfaces.Params.Params

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|PFin"
  PFin : Semantics.Interfaces.Params.Params

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_Call"
  I2FE_Call : prerel (@CallE PInf) (@CallE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_Call"
  I2FA_Call : postrel (@CallE PInf) (@CallE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_ExternalCall"
  I2FE_ExternalCall : prerel (@ExternalCallE PInf) (@ExternalCallE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_ExternalCall"
  I2FA_ExternalCall : postrel (@ExternalCallE PInf) (@ExternalCallE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_Intrinsic"
  I2FE_Intrinsic : prerel (@IntrinsicE PInf) (@IntrinsicE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_Intrinsic"
  I2FA_Intrinsic : postrel (@IntrinsicE PInf) (@IntrinsicE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_Global"
  I2FE_Global : prerel (@GlobalE PInf) (@GlobalE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_Global"
  I2FA_Global : postrel (@GlobalE PInf) (@GlobalE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_Local"
  I2FE_Local : prerel (@LocalE PInf) (@LocalE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_Local"
  I2FA_Local : postrel (@LocalE PInf) (@LocalE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_Stack"
  I2FE_Stack : prerel (@StackE PInf) (@StackE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_Stack"
  I2FA_Stack : postrel (@StackE PInf) (@StackE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_Memory"
  I2FE_Memory : prerel (@MemoryE PInf) (@MemoryE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_Memory"
  I2FA_Memory : postrel (@MemoryE PInf) (@MemoryE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_Draw"
  I2FE_Draw : prerel (@DrawE PInf) (@DrawE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_Draw"
  I2FA_Draw : postrel (@DrawE PInf) (@DrawE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_Exc"
  I2FE_Exc : prerel (@LLVMExcE PInf) (@LLVMExcE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_Exc"
  I2FA_Exc : postrel (@LLVMExcE PInf) (@LLVMExcE PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_OOM"
  I2FE_OOM : prerel OOME OOME

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_OOM"
  I2FA_OOM : postrel OOME OOME

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_UB"
  I2FE_UB : prerel UBE UBE

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_UB"
  I2FA_UB : postrel UBE UBE

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_Debug"
  I2FE_Debug : prerel DebugE DebugE

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_Debug"
  I2FA_Debug : postrel DebugE DebugE

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_Failure"
  I2FE_Failure : prerel FailureE FailureE

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_Failure"
  I2FA_Failure : postrel FailureE FailureE

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_MCFG"
  I2FE_MCFG : prerel (@MCFGEtop PInf) (@MCFGEtop PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_MCFG"
  I2FA_MCFG : postrel (@MCFGEtop PInf) (@MCFGEtop PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_CFG"
  I2FE_CFG : prerel (@CFGEtop PInf) (@CFGEtop PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_CFG"
  I2FA_CFG : postrel (@CFGEtop PInf) (@CFGEtop PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FE_MCFGbot"
  I2FE_MCFGbot : prerel (@MCFGEbot PInf) (@MCFGEbot PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2FA_MCFGbot"
  I2FA_MCFGbot : postrel (@MCFGEbot PInf) (@MCFGEbot PFin)

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|cutUB"
  cutUB : ∀ {E : Effect.{u}} [UBE -< E], pred1 E

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|CutUB"
  CutUB : ∀ {E : Effect.{u}} [UBE -< E] (u : Unit),
    cutUB (E := E) (requestIn (D := UBE) (ThrowUB u))

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|cutOOM"
  cutOOM : ∀ {E : Effect.{u}} [OOME -< E], pred1 E

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|CutOOM"
  CutOOM : ∀ {E : Effect.{u}} [OOME -< E] (u : Unit),
    cutOOM (E := E) (requestIn (D := OOME) (ThrowOOM u))

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_refine_MCFG"
  I2F_refine_MCFG : ∀ {X Y : Type}, (X → Y → Prop) → @MCFGtop PInf X → @MCFGtop PFin Y → Prop

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_refine_CFG"
  I2F_refine_CFG : ∀ {X Y : Type}, (X → Y → Prop) → @CFGtop PInf X → @CFGtop PFin Y → Prop

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_refine_MCFGbot"
  I2F_refine_MCFGbot : ∀ {X Y : Type}, (X → Y → Prop) → @MCFGbot PInf X → @MCFGbot PFin Y → Prop

#source_check "src/rocq/Theory/I2F/Refinement.v|Vellvm.Theory.I2F.Refinement|I2F_refine"
  I2F_refine : @MCFGtop PInf (@dvalue PInf) → @MCFGtop PFin (@dvalue PFin) → Prop

end PortChecks.RefinementBasic
