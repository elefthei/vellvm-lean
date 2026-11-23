import Vellvm.Theory.I2F.I2F_denotation.Core
import Vellvm.Theory.I2F.I2F_exp.Values

namespace Vellvm.Theory.I2F.I2F_denotation
open Semantics.DynamicValues Semantics.Denotation Syntax.DynamicTypes Syntax.LLVMAst Syntax.CFG
open Refinement I2F_exp
open Semantics.LLVMEvents (MemoryE StackE MemPush StackPush Alloca Store)
open Utils.RelationsUtil (prod_rel TT)
open Utils.rutt_cutoff (ruttc_ret)

theorem I2F_combine_lists_varargs (d : definition dtyp (cfg dtyp)) {xs ys}
    (h : I2F_targs xs ys) : I2F_EOU
    (prod_rel (List.Forall₂ (prod_rel Eq (prod_rel Eq I2F_dvalue))) I2F_targs)
    (combine_lists_varargs d.df_args xs) (combine_lists_varargs d.df_args ys) := by
  generalize d.df_args = names
  induction names generalizing xs ys with
  | nil => exact I2F_EOU_ret _ _ ⟨.nil, h⟩
  | cons name names ih =>
    cases h with
    | nil => exact I2F_EOU_error _ _
    | cons hxy htail =>
      simp only [combine_lists_varargs]
      refine I2F_EOU_bind _ _ (ih htail) ?_
      rintro ⟨ls, vs⟩ ⟨rs, ws⟩ ⟨hl, hv⟩
      exact I2F_EOU_ret _ _ ⟨.cons ⟨rfl, hxy⟩ hl, hv⟩

theorem I2F_frame_bindings {ls : List (raw_id × (dtyp × @dvalue PInf))}
    {rs : List (raw_id × (dtyp × @dvalue PFin))}
    (h : List.Forall₂ (prod_rel Eq (prod_rel Eq I2F_dvalue)) ls rs) :
    List.Forall₂ (prod_rel Eq I2F_dvalue)
      (ls.map fun (x, _, v) ↦ (x, v)) (rs.map fun (y, _, w) ↦ (y, w)) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons ⟨h.1, h.2.2⟩ ih

theorem I2F_push_call_frame (d : definition dtyp (cfg dtyp)) {xs ys} (h : I2F_targs xs ys) :
    I2F_refine_CFG I2F_Addr (push_call_frame (Pa := PInf) d xs)
      (push_call_frame (Pa := PFin) d ys) := by
  unfold push_call_frame Worker.push_call_frame
  refine cfg_bind (I2F_refine_lift' _ _ _ (I2F_combine_lists_varargs d h)) ?_
  rintro ⟨bs, vs⟩ ⟨cs, ws⟩ ⟨hb, hv⟩
  dsimp only
  rw [I2F_targs_fst hv]
  refine cfg_bind (RR := TT) (cfg_emit (D₁ := @MemoryE PInf) (D₂ := @MemoryE PFin)
    (@MemPush PInf) (@MemPush PFin) trivial (fun _ _ _ ↦ trivial)) (fun _ _ _ ↦ ?_)
  refine cfg_bind (RR := TT) (cfg_emit (D₁ := @StackE PInf) (D₂ := @StackE PFin)
    (@StackPush PInf _) (@StackPush PFin _) (I2F_frame_bindings hb)
    (fun _ _ _ ↦ trivial)) (fun _ _ _ ↦ ?_)
  refine cfg_bind (RR := I2F_dvalue) (cfg_emit (D₁ := @MemoryE PInf) (D₂ := @MemoryE PFin)
    (@Alloca PInf _ _ _) (@Alloca PFin _ _ _) ⟨rfl, rfl, rfl⟩ (fun _ _ ha ↦ ha)) (fun _ _ ha ↦ ?_)
  refine cfg_bind (RR := TT) (cfg_emit (D₁ := @MemoryE PInf) (D₂ := @MemoryE PFin)
    (@Store PInf _ _ _) (@Store PFin _ _ _) ⟨rfl, ha, I2F_canonicalize_agg _ (I2F_targs_snd hv)⟩
    (fun _ _ _ ↦ trivial)) (fun _ _ _ ↦ ?_)
  cases ha with
  | I2F_dvalue_Base base => cases base <;> first | exact ruttc_ret _ _ ‹I2F_Addr _ _› | apply cfg_raise
  | _ => apply cfg_raise

end Vellvm.Theory.I2F.I2F_denotation
