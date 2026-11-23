import Vellvm.Theory.I2F.I2F_interp.State
import Vellvm.Theory.I2F.I2F_memory
import Vellvm.Theory.I2F.I2F_exp.Freeze

namespace Vellvm.Theory.I2F.I2F_interp
open Refinement I2F_memory I2F_memS I2F_exp
open Semantics Semantics.InterpretationStack Semantics.Implementations.Memory
open Semantics.Handlers Semantics.Handlers.Memory Semantics.LLVMEvents Semantics.DynamicValues
open Utils.RelationsUtil (prod_rel)
open Utils.rutt_cutoff (ruttc_ret ruttc_bind)

theorem I2F_fresh_provenance_eq (s : @State PInf) (t : @State PFin) (h : I2F_State s t) :
    PInf.PROV.next_provenance (@state_provenance PInf s) =
      PFin.PROV.next_provenance (@state_provenance PFin t) :=
  congrArg PInf.PROV.next_provenance h.i2f_st_prov

theorem I2F_memM_interp (X Y : Type) (RR : X → Y → Prop)
    (l : @ConcreteMem PInf X) (r : @ConcreteMem PFin Y) (h : I2F_memS I2F_State RR l r) :
    ∀ s t, I2F_State s t → I2F_refine_MCFGbot (prod_rel RR I2F_State)
      (memM_interp (Pa := PInf) l s) (memM_interp (Pa := PFin) r t) := by
  induction h with
  | I2F_Mret a b hab => exact fun s t hst ↦ ruttc_ret (a, s) (b, t) ⟨hab, hst⟩
  | I2F_Merr msg msg' =>
    intro s t _
    exact I2F_refine_lift_bot _ (.raise_error msg) (.raise_error msg') (.I2F_EOU_error _ _)
  | I2F_Mub_l msg r =>
    intro s t _
    change I2F_refine_MCFGbot _ ((pure () : @MCFGbot PInf Unit) >>= fun _ ↦
      (CTree.CTree.trigger (requestIn (D := UBE) (E := @MCFGEbot PInf) (ThrowUB ())) >>=
        fun a ↦ pure a) >>=
        fun a : Empty ↦ nomatch a) _
    simp only [CTree.pure_bind', CTree.CTree.trigger, CTree.vis_bind]
    exact Tree.Related.cut_left _ _ _ (.CutUB ())
  | I2F_Moom_r l msg =>
    intro s t _
    change I2F_refine_MCFGbot _ _ ((pure () : @MCFGbot PFin Unit) >>= fun _ ↦
      (CTree.CTree.trigger (requestIn (D := OOME) (E := @MCFGEbot PFin) (ThrowOOM ())) >>=
        fun a ↦ pure a) >>=
        fun a : Empty ↦ nomatch a)
    simp only [CTree.pure_bind', CTree.CTree.trigger, CTree.vis_bind]
    exact Tree.Related.cut_right _ _ _ (.CutOOM ())
  | I2F_Mget k l _ ih => exact fun s t hst ↦ ih s t hst s t hst
  | I2F_Mput s t k l hst _ ih => exact fun _ _ _ ↦ ih s t hst
  | I2F_Mchoose c k l _ ih =>
    intro s t hst
    cases c <;> simp only [memM_interp, Memory.Worker.memM_interpWith] <;>
      apply ruttc_bind _ _ _ _ Eq _ _ _ _ _
    · exact ruttc_ret _ _ (I2F_next_key_with_alignment _ _ hst.i2f_st_ms.i2f_ms_memory _)
    · rintro a _ rfl; exact ih a s t hst
    · exact ruttc_ret _ _ (I2F_fresh_provenance_eq s t hst)
    · rintro a _ rfl; exact ih a _ _ ⟨hst.i2f_st_ms, rfl⟩
    · exact ruttc_ret _ _ rfl
    · rintro a _ rfl; exact ih a s t hst

private theorem liftMem {X Y : Type} (RR : X → Y → Prop)
    (l : @ConcreteMem PInf X) (r : @ConcreteMem PFin Y) (h : I2F_memS I2F_State RR l r)
    (s t) (hst : I2F_FusedS s t) : I2F_refine_MCFGbot (prod_rel RR I2F_FusedS)
      (@on_mem PInf X (memM_interp (Pa := PInf) l) s)
      (@on_mem PFin Y (memM_interp (Pa := PFin) r) t) := by
  obtain ⟨ms, rest⟩ := s
  obtain ⟨mt, rest'⟩ := t
  unfold on_mem InterpretationStack.Worker.on_mem
  apply ruttc_bind _ _ _ _ (prod_rel RR I2F_State) _ _ _ _ _
    (I2F_memM_interp X Y RR l r h ms mt hst.i2f_fs_mem)
  rintro ⟨a, ms'⟩ ⟨b, mt'⟩ ⟨hab, hm⟩
  exact ruttc_ret _ _ ⟨hab, ⟨hm, hst.i2f_fs_frame, hst.i2f_fs_stack, hst.i2f_fs_genv⟩⟩

theorem I2F_fused_memory (e : (@MemoryE PInf).I) (f : (@MemoryE PFin).I)
    (he : I2FE_Memory e f) (s t) (hs : I2F_FusedS s t) :
    I2F_refine_MCFGbot (prod_rel (fun a b ↦ I2FA_Memory e a f b) I2F_FusedS)
      (@fused_memory PInf e s) (@fused_memory PFin f t) :=
  liftMem _ _ _ (I2F_handle_memoryM e f he) s t hs

theorem I2F_fused_intrinsic (e : (@IntrinsicE PInf).I) (f : (@IntrinsicE PFin).I)
    (he : I2FE_Intrinsic e f) (s t) (hs : I2F_FusedS s t) :
    I2F_refine_MCFGbot (prod_rel (fun a b ↦ I2FA_Intrinsic e a f b) I2F_FusedS)
      (@fused_intrinsic PInf e s) (@fused_intrinsic PFin f t) :=
  liftMem _ _ _ (I2F_handle_intrinsicM e f he) s t hs

private theorem reference_draw (pa : Interfaces.Params.Params) (dt : Syntax.DynamicTypes.dtyp) :
    (Draw.Worker.handle_drawWith (Pa := pa) referenceChooser (.Draw dt) :
      @MCFGbot pa (@dvalue pa)) = EOU_to_itree (@default_dvalue_of_dtyp pa dt) := by
  simp only [Draw.Worker.handle_drawWith]
  split <;> rename_i h <;>
    simp only [h, referenceChooser, ChoiceRequest.reference, EOU_to_itree,
      LLVMEvents.Worker.EOU_to_itree]
  rfl

theorem I2F_fused_draw (e : (@DrawE PInf).I) (f : (@DrawE PFin).I) (he : I2FE_Draw e f)
    (s t) (hs : I2F_FusedS s t) :
    I2F_refine_MCFGbot (prod_rel (fun a b ↦ I2FA_Draw e a f b) I2F_FusedS)
      (@fused_draw PInf e s) (@fused_draw PFin f t) := by
  obtain ⟨dt⟩ := e
  obtain ⟨dt'⟩ := f
  change dt = dt' at he
  subst dt'
  unfold fused_draw InterpretationStack.Worker.fused_draw
  rw [reference_draw PInf, reference_draw PFin]
  apply ruttc_bind _ _ _ _ I2F_dvalue _ _ _ _ _
    (I2F_refine_lift_bot _ _ _ (I2F_default_dvalue_of_dtyp dt))
  exact fun a b hab ↦ ruttc_ret _ _ ⟨hab, hs⟩

end Vellvm.Theory.I2F.I2F_interp
