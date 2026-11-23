import PortChecks.SourceType
import Vellvm.Semantics.Handlers.Intrinsics

namespace Vellvm.Semantics.Handlers.Intrinsics
open ITree (Effect Subeffect)
open CTree (CTree)
open Tree Interfaces.Params LLVMEvents

#source_check "src/rocq/Semantics/Handlers/Intrinsics.v|Vellvm.Semantics.Handlers.Intrinsics|interp_intrinsics_bind"
  interp_intrinsics_bind : ∀ [Pa : Params] {E F B : Effect} [MemoryE -< F] [FailureE -< F]
    [UBE -< F] [OOME -< F] (R S : Type) (t : CTree (Eff E F) B R) (k : R → CTree (Eff E F) B S),
    eqit Eq false false (interp_intrinsics (t >>= k))
      (interp_intrinsics t >>= fun r ↦ interp_intrinsics (k r))

#source_check "src/rocq/Semantics/Handlers/Intrinsics.v|Vellvm.Semantics.Handlers.Intrinsics|interp_intrinsics_ret"
  interp_intrinsics_ret : ∀ [Pa : Params] {E F B : Effect} [MemoryE -< F] [FailureE -< F]
    [UBE -< F] [OOME -< F] (R : Type) (x : R), eqit Eq false false
    (interp_intrinsics (CTree.ret x : CTree (Eff E F) B R)) (.ret x)

#source_check "src/rocq/Semantics/Handlers/Intrinsics.v|Vellvm.Semantics.Handlers.Intrinsics|interp_intrinsics_Tau"
  interp_intrinsics_Tau : ∀ [Pa : Params] {E F B : Effect} [MemoryE -< F] [FailureE -< F]
    [UBE -< F] [OOME -< F] {R : Type} (t : CTree (Eff E F) B R), eqit Eq false false
    (interp_intrinsics t.guard) (interp_intrinsics t).guard

#source_check "src/rocq/Semantics/Handlers/Intrinsics.v|Vellvm.Semantics.Handlers.Intrinsics|interp_intrinsics_vis_eqit"
  interp_intrinsics_vis_eqit : ∀ [Pa : Params] {E F B : Effect} [MemoryE -< F] [FailureE -< F]
    [UBE -< F] [OOME -< F] {R : Type} (e : (Eff E F).I) (k : (Eff E F).O e → CTree (Eff E F) B R),
    eqit Eq false false (interp_intrinsics (.vis e k))
      (interp_intrinsics_h e >>= fun x ↦ (interp_intrinsics (k x)).guard)

#source_check "src/rocq/Semantics/Handlers/Intrinsics.v|Vellvm.Semantics.Handlers.Intrinsics|interp_intrinsics_vis"
  interp_intrinsics_vis : ∀ [Pa : Params] {E F B : Effect} [MemoryE -< F] [FailureE -< F]
    [UBE -< F] [OOME -< F] (R : Type) (e : (Eff E F).I) (k : (Eff E F).O e → CTree (Eff E F) B R),
    eutt Eq (interp_intrinsics (.vis e k)) (interp_intrinsics_h e >>= fun x ↦ interp_intrinsics (k x))

#source_check "src/rocq/Semantics/Handlers/Intrinsics.v|Vellvm.Semantics.Handlers.Intrinsics|interp_intrinsics_trigger"
  interp_intrinsics_trigger : ∀ [Pa : Params] {E F B : Effect} [MemoryE -< F] [FailureE -< F]
    [UBE -< F] [OOME -< F] (e : (Eff E F).I), eutt Eq
    (interp_intrinsics (CTree.trigger e : CTree (Eff E F) B _)) (interp_intrinsics_h e)

#source_check "src/rocq/Semantics/Handlers/Intrinsics.v|Vellvm.Semantics.Handlers.Intrinsics|interp_intrinsics_bind_trigger_eqit"
  interp_intrinsics_bind_trigger_eqit : ∀ [Pa : Params] {E F B : Effect} [MemoryE -< F] [FailureE -< F]
    [UBE -< F] [OOME -< F] (R : Type) (e : (Eff E F).I) (k : (Eff E F).O e → CTree (Eff E F) B R),
    eqit Eq false false (interp_intrinsics (CTree.trigger e >>= k))
      (interp_intrinsics_h e >>= fun x ↦ (interp_intrinsics (k x)).guard)

#source_check "src/rocq/Semantics/Handlers/Intrinsics.v|Vellvm.Semantics.Handlers.Intrinsics|interp_intrinsics_bind_trigger"
  interp_intrinsics_bind_trigger : ∀ [Pa : Params] {E F B : Effect} [MemoryE -< F] [FailureE -< F]
    [UBE -< F] [OOME -< F] (R : Type) (e : (Eff E F).I) (k : (Eff E F).O e → CTree (Eff E F) B R),
    eutt Eq (interp_intrinsics (CTree.trigger e >>= k))
      (interp_intrinsics_h e >>= fun x ↦ interp_intrinsics (k x))

#source_check "src/rocq/Semantics/Handlers/Intrinsics.v|Vellvm.Semantics.Handlers.Intrinsics|eutt_interp_intrinsics"
  eutt_interp_intrinsics : ∀ [Pa : Params] {E F B : Effect} [MemoryE -< F] [FailureE -< F]
    [UBE -< F] [OOME -< F] {R : Type} {b : Bool} (t s : CTree (Eff E F) B R),
    eqit Eq b b t s → eqit Eq b b (interp_intrinsics t) (interp_intrinsics s)

end Vellvm.Semantics.Handlers.Intrinsics
