import Vellvm.Theory.I2F.I2F_interp.State
import Vellvm.Theory.I2F.Refinement.TreeLaws

namespace Vellvm.Theory.I2F.I2F_interp
open ITree (Effect)
open CTree (CTree)
open Refinement Semantics Semantics.LLVMEvents Semantics.InterpretationStack Semantics.Handlers
open Semantics.Interfaces.Params Semantics.Instrumentation Semantics.DynamicValues
open Syntax.RawIdMaps Syntax.LLVMAst
open Utils.RelationsUtil (prod_rel)
open Utils.rutt_cutoff (ruttc_ret)

private theorem record_quiet [Pa : Params] {E B : Effect} (v : @TraceRequest Pa) :
    (Snapshots.record v : CTree E B Unit) = pure () := rfl

private theorem bind_failure {E B : Effect} [FailureE -< E] {X Y : Type}
    (s : IRString) (k : X → CTree E B Y) :
    (LLVMEvents.Worker.«raise» s >>= k) = LLVMEvents.Worker.«raise» s := by
  unfold LLVMEvents.Worker.«raise»
  simp only [bind_assoc]
  congr 1; funext u
  congr 1; funext a; exact Empty.elim a

private theorem failure_related {X Y : Type} (R : X → Y → Prop) (a b : IRString) :
    I2F_refine_MCFGbot R (LLVMEvents.Worker.«raise» a) (LLVMEvents.Worker.«raise» b) :=
  I2F_refine_lift_bot R _ _ (.I2F_EOU_error a b)

theorem I2F_fused_global (e : (@GlobalE PInf).I) (f : (@GlobalE PFin).I) (h : I2FE_Global e f)
    (s t) (hs : I2F_FusedS s t) :
    I2F_refine_MCFGbot (prod_rel (fun x y ↦ I2FA_Global e x f y) I2F_FusedS)
      (@fused_global PInf e s) (@fused_global PFin f t) := by
  rcases s with ⟨m, ls, g⟩
  rcases t with ⟨n, ls', g'⟩
  cases e <;> cases f <;> try exact False.elim h
  all_goals simp only [fused_global, InterpretationStack.Worker.fused_global,
    InterpretationStack.Worker.on_genv, Global.Worker.handle_global_debug,
    Global.Worker.handle_global, Global.Worker.update_globals_ref, record_quiet, pure_bind]
  · obtain ⟨rfl, hv⟩ := h
    exact ruttc_ret _ _ ⟨trivial, hs.i2f_fs_mem, hs.i2f_fs_frame, hs.i2f_fs_stack,
      RM_Refine_add _ _ _ _ _ _ hs.i2f_fs_genv hv⟩
  · rename_i i j
    obtain rfl : i = j := h
    have hl := RM_Refine_lookup _ g g' hs.i2f_fs_genv i
    unfold rid_lookup at hl
    generalize RM.find i g = x, RM.find i g' = y at hl ⊢
    cases hl with
    | none => simp only [bind_failure]; exact failure_related _ _ _
    | some a b hv => simp only [pure_bind]; exact ruttc_ret _ _ ⟨hv, hs⟩

theorem I2F_fused_local (e : (@LocalE PInf).I) (f : (@LocalE PFin).I) (h : I2FE_Local e f)
    (s t) (hs : I2F_FusedS s t) :
    I2F_refine_MCFGbot (prod_rel (fun x y ↦ I2FA_Local e x f y) I2F_FusedS)
      (@fused_local PInf e s) (@fused_local PFin f t) := by
  rcases s with ⟨m, ⟨a, st⟩, g⟩
  rcases t with ⟨n, ⟨b, st'⟩, g'⟩
  have hf := hs.i2f_fs_frame
  cases e <;> cases f <;> try exact False.elim h
  all_goals simp only [fused_local, InterpretationStack.Worker.fused_local,
    InterpretationStack.Worker.on_ls, Stack.Worker.handle_local_stack, Local.Worker.handle_local_debug,
    Local.Worker.handle_local, Local.Worker.update_locals_ref, record_quiet, pure_bind]
  · obtain ⟨rfl, hv⟩ := h
    exact ruttc_ret _ _ ⟨trivial, hs.i2f_fs_mem,
      ⟨RM_Refine_add _ _ _ _ _ _ hf.i2f_sf_vars hv, hf.i2f_sf_exc, hf.i2f_sf_loc⟩,
      hs.i2f_fs_stack, hs.i2f_fs_genv⟩
  · rename_i i j
    obtain rfl : i = j := h
    have hl := RM_Refine_lookup _ (@Stack.stack_vars PInf a) (@Stack.stack_vars PFin b)
      hf.i2f_sf_vars i
    unfold rid_lookup at hl
    generalize RM.find i (@Stack.stack_vars PInf a) = x,
      RM.find i (@Stack.stack_vars PFin b) = y at hl ⊢
    cases hl with
    | none => simp only [bind_failure]; exact failure_related _ _ _
    | some v w hv => simp only [pure_bind]; exact ruttc_ret _ _ ⟨hv, hs⟩

private theorem push_vars (xs : List (raw_id × @dvalue PInf)) (ys : List (raw_id × @dvalue PFin))
    (h : List.Forall₂ (prod_rel Eq I2F_dvalue) xs ys) :
    I2F_local_env (xs.foldr (fun (k, v) m ↦ RM.add k v m) (RM.empty _))
      (ys.foldr (fun (k, v) m ↦ RM.add k v m) (RM.empty _)) := by
  induction h with
  | nil => exact RM_Refine_empty _
  | @cons a b xs ys ha _ ih =>
    rcases a with ⟨i, v⟩
    rcases b with ⟨j, w⟩
    obtain ⟨rfl, hv⟩ : i = j ∧ I2F_dvalue v w := ha
    exact RM_Refine_add _ _ _ _ _ _ ih hv

theorem I2F_fused_stack (e : (@StackE PInf).I) (f : (@StackE PFin).I) (h : I2FE_Stack e f)
    (s t) (hs : I2F_FusedS s t) :
    I2F_refine_MCFGbot (prod_rel (fun x y ↦ I2FA_Stack e x f y) I2F_FusedS)
      (@fused_stack PInf e s) (@fused_stack PFin f t) := by
  rcases s with ⟨m, ⟨a, st⟩, g⟩
  rcases t with ⟨n, ⟨b, st'⟩, g'⟩
  obtain ⟨hm, hf, hst, hg⟩ := hs
  cases e <;> cases f <;> try exact False.elim h
  all_goals simp only [fused_stack, InterpretationStack.Worker.fused_stack,
    InterpretationStack.Worker.on_ls, Stack.Worker.handle_stack, record_quiet, pure_bind]
  · exact ruttc_ret _ _ ⟨trivial, hm, ⟨push_vars _ _ h, .none, rfl⟩,
      List.Forall₂.cons hf hst, hg⟩
  · change List.Forall₂ I2F_stack_frame st st' at hst
    cases hst with
    | nil => simp only [bind_failure]; exact failure_related _ _ _
    | cons hhead htail => simp only [pure_bind]; exact ruttc_ret _ _ ⟨trivial, hm, hhead, htail, hg⟩
  · exact ruttc_ret _ _ ⟨trivial, hm, ⟨hf.i2f_sf_vars, .some _ _ h, hf.i2f_sf_loc⟩, hst, hg⟩
  · exact ruttc_ret _ _ ⟨hf.i2f_sf_exc, hm, ⟨hf.i2f_sf_vars, .none, hf.i2f_sf_loc⟩, hst, hg⟩

end Vellvm.Theory.I2F.I2F_interp
