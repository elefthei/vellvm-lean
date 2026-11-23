module

public import Vellvm.Semantics.IntrinsicsDefinitions.Simulation
public import Vellvm.Semantics.InstrumentationFacts.Producer
public import Vellvm.Utils.rutt_cutoff

@[expose] public section
namespace Vellvm.Semantics.Handlers.Intrinsics
open ITree (Effect Subeffect)
open CTree (CTree)
open Tree Interfaces.Params LLVMEvents IntrinsicsDefinitions

abbrev Eff [Params] (E F : Effect) := E ⊕ₑ IntrinsicE ⊕ₑ F

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M] [Instrumentation.Diagnostics M]
variable [Pa : Params] {B : Effect}

def handle_intrinsics {E : Effect} [FailureE -< E] [UBE -< E] [OOME -< E] [MemoryE -< E]
    [IntrinsicE -< E] : (e : IntrinsicE.I) → M E B (IntrinsicE.O e)
  | .Intrinsic t name args va =>
    match IntrinsicsDefinitions.Worker.named_intrinsic_semantics t name with
    | some f => f (args.map Prod.snd) va
    | none => LLVMEvents.Worker.intrinsic t name args va

def E_trigger (E F : Effect) (e : E.I) : M (Eff E F) B (E.O e) :=
  Runtime.trigger (E := Eff E F) (.inl e)

def F_trigger (E F : Effect) (f : F.I) : M (Eff E F) B (F.O f) :=
  Runtime.trigger (E := Eff E F) (.inr (.inr f))

variable {E F : Effect} [MemoryE -< F] [FailureE -< F] [UBE -< F] [OOME -< F]

def interp_intrinsics_h : (e : (Eff E F).I) → M (Eff E F) B ((Eff E F).O e)
  | .inl e => E_trigger E F e
  | .inr (.inl intr) => handle_intrinsics intr
  | .inr (.inr f) => F_trigger E F f

def interp_intrinsics {R : Type} (t : M (Eff E F) B R) : M (Eff E F) B R :=
  Runtime.interp interp_intrinsics_h t

end Worker

variable [Pa : Params] {E F B : Effect}

def handle_intrinsics [FailureE -< E] [UBE -< E] [OOME -< E] [MemoryE -< E] [IntrinsicE -< E]
    (e : IntrinsicE.I) : CTree E B (IntrinsicE.O e) := Worker.handle_intrinsics e

def E_trigger (E F : Effect) (e : E.I) : CTree (Eff E F) B (E.O e) := Worker.E_trigger E F e

def F_trigger (E F : Effect) (f : F.I) : CTree (Eff E F) B (F.O f) := Worker.F_trigger E F f

variable [MemoryE -< F] [FailureE -< F] [UBE -< F] [OOME -< F]

def interp_intrinsics_h (e : (Eff E F).I) : CTree (Eff E F) B ((Eff E F).O e) :=
  Worker.interp_intrinsics_h e

def interp_intrinsics {R : Type} (t : CTree (Eff E F) B R) : CTree (Eff E F) B R :=
  Worker.interp_intrinsics t

theorem interp_intrinsics_bind (R S : Type) (t : CTree (Eff E F) B R) (k : R → CTree (Eff E F) B S) :
    eqit Eq false false (interp_intrinsics (t >>= k))
      (interp_intrinsics t >>= fun r ↦ interp_intrinsics (k r)) :=
  eqit_strict_iff_eq.mpr (CTree.interp_bind interp_intrinsics_h t k)

theorem interp_intrinsics_ret (R : Type) (x : R) : eqit Eq false false
    (interp_intrinsics (CTree.ret x : CTree (Eff E F) B R)) (.ret x) :=
  eqit_strict_iff_eq.mpr (CTree.interp_ret interp_intrinsics_h x)

theorem interp_intrinsics_Tau {R : Type} (t : CTree (Eff E F) B R) : eqit Eq false false
    (interp_intrinsics t.guard) (interp_intrinsics t).guard :=
  eqit_strict_iff_eq.mpr (CTree.interp_guard interp_intrinsics_h t)

theorem interp_intrinsics_vis_eqit {R : Type} (e : (Eff E F).I)
    (k : (Eff E F).O e → CTree (Eff E F) B R) : eqit Eq false false (interp_intrinsics (.vis e k))
      (interp_intrinsics_h e >>= fun x ↦ (interp_intrinsics (k x)).guard) :=
  eqit_strict_iff_eq.mpr (CTree.interp_vis interp_intrinsics_h e k)

private theorem bind_guard_eutt {I C : Effect} {X Y : Type} (t : CTree I C X)
    (k : X → CTree I C Y) : eutt Eq (t >>= fun x ↦ (k x).guard) (t >>= k) :=
  Utils.rutt_cutoff.ruttc_bind _ _ _ _ Eq Eq _ _ _ _ (eqit_refl true true t)
    (fun x _ h ↦ h ▸ Related.guard_left rfl (eqit_refl true true (k x)))

theorem interp_intrinsics_vis (R : Type) (e : (Eff E F).I)
    (k : (Eff E F).O e → CTree (Eff E F) B R) : eutt Eq (interp_intrinsics (.vis e k))
      (interp_intrinsics_h e >>= fun x ↦ interp_intrinsics (k x)) := by
  rw [eqit_strict_iff_eq.mp (interp_intrinsics_vis_eqit e k)]
  exact bind_guard_eutt _ _

theorem interp_intrinsics_trigger (e : (Eff E F).I) : eutt Eq
    (interp_intrinsics (CTree.trigger e : CTree (Eff E F) B _)) (interp_intrinsics_h e) := by
  change eutt Eq (CTree.interp interp_intrinsics_h (CTree.trigger e)) _
  rw [CTree.interp_trigger]
  simpa only [bind_pure] using bind_guard_eutt (interp_intrinsics_h (B := B) e) pure

theorem interp_intrinsics_bind_trigger_eqit (R : Type) (e : (Eff E F).I)
    (k : (Eff E F).O e → CTree (Eff E F) B R) : eqit Eq false false
      (interp_intrinsics (CTree.trigger e >>= k))
      (interp_intrinsics_h e >>= fun x ↦ (interp_intrinsics (k x)).guard) := by
  simpa only [CTree.trigger, CTree.vis_bind, CTree.pure_bind'] using interp_intrinsics_vis_eqit e k

theorem interp_intrinsics_bind_trigger (R : Type) (e : (Eff E F).I)
    (k : (Eff E F).O e → CTree (Eff E F) B R) : eutt Eq
      (interp_intrinsics (CTree.trigger e >>= k))
      (interp_intrinsics_h e >>= fun x ↦ interp_intrinsics (k x)) := by
  simpa only [CTree.trigger, CTree.vis_bind, CTree.pure_bind'] using interp_intrinsics_vis R e k

theorem eutt_interp_intrinsics {R : Type} {b : Bool} (t s : CTree (Eff E F) B R)
    (h : eqit Eq b b t s) : eqit Eq b b (interp_intrinsics t) (interp_intrinsics s) := by
  cases b with
  | false => cases eqit_strict_iff_eq.mp h; exact eqit_refl false false _
  | true =>
    apply Utils.rutt_cutoff.ruttc_interp_itree interp_intrinsics_h interp_intrinsics_h
      (fun _ h ↦ False.elim h) (fun _ h ↦ False.elim h) _ t s h
    rintro e _ rfl
    simpa only [heq_iff_eq] using eqit_refl true true (interp_intrinsics_h (B := B) e)

namespace Worker

variable {M : Effect → Effect → Type → Type v} {N : Effect → Effect → Type → Type w}
variable [Runtime M] [Runtime N] [Instrumentation.Diagnostics M] [Instrumentation.Diagnostics N]
variable [Instrumentation.Snapshots M] [Instrumentation.Snapshots N] (sim : Simulation M N)

theorem handle_intrinsics_sim {G : Effect} [FailureE -< G] [UBE -< G] [OOME -< G] [MemoryE -< G]
    [IntrinsicE -< G] (e : IntrinsicE.I) :
    sim.R (E := G) (B := B) (handle_intrinsics e) (handle_intrinsics e) := by
  rcases e with ⟨t, name, args, va⟩
  simp only [handle_intrinsics]
  have h := IntrinsicsDefinitions.Worker.named_intrinsic_semantics_sim (E := G) (B := B) sim t name
  generalize IntrinsicsDefinitions.Worker.named_intrinsic_semantics (M := M) (E := G) (B := B) t name = l at h ⊢
  generalize IntrinsicsDefinitions.Worker.named_intrinsic_semantics (M := N) (E := G) (B := B) t name = r at h ⊢
  cases h with
  | none => exact sim.intrinsic (E := G) t name args va
  | some hf => exact hf (args.map Prod.snd) va

theorem interp_intrinsics_h_sim (e : (Eff E F).I) :
    sim.R (B := B) (interp_intrinsics_h e) (interp_intrinsics_h e) := by
  rcases e with e | e | f
  · exact sim.trigger (E := Eff E F) (.inl e)
  · exact handle_intrinsics_sim sim e
  · exact sim.trigger (E := Eff E F) (.inr (.inr f))

theorem interp_intrinsics_sim {R : Type} {t : M (Eff E F) B R} {s : N (Eff E F) B R}
    (h : sim.R t s) : sim.R (interp_intrinsics t) (interp_intrinsics s) :=
  sim.interp (interp_intrinsics_h_sim sim) h

end Worker

theorem interp_intrinsics_meaning {R : Type} (p : Producer (Eff E F) B R) :
    (Worker.interp_intrinsics p).meaning = interp_intrinsics p.meaning :=
  Worker.interp_intrinsics_sim Instrumentation.producerSimulation (t := p) (s := p.meaning) rfl

end Vellvm.Semantics.Handlers.Intrinsics
