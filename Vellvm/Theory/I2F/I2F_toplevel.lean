import Vellvm.Semantics.TopLevel.Interpreter
import Vellvm.Theory.I2F.I2F_denotation.Functions
import Vellvm.Theory.I2F.I2F_denotation.Mrec
import Vellvm.Theory.I2F.I2F_interp
import Vellvm.Theory.I2F.I2F_toplevel.InitialState
import Vellvm.Theory.I2F.I2F_toplevel.Initialization
import Vellvm.Theory.I2F.I2F_toplevel.Addressing
import Vellvm.Theory.I2F.I2F_toplevel.Libraries

namespace Vellvm.Theory.I2F.I2F_toplevel
open Semantics Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation Semantics.TopLevel
open Syntax.LLVMAst Syntax.DynamicTypes Syntax.CFG
open Utils.IntMaps Utils.RelationsUtil Utils.rutt_cutoff
open Refinement I2F_denotation I2F_interp

theorem I2F_address_one_function (df : definition dtyp (cfg dtyp)) :
    I2F_refine_MCFG (prod_rel Eq I2F_function_denotation)
      (@address_one_function PInf df) (@address_one_function PFin df) :=
  mcfg_bind (address_related df.df_prototype.dc_name _) fun _ _ he ↦
    ruttc_ret _ _ ⟨he, I2F_denote_function df⟩

private theorem raise_exception {x y} (h : I2F_dvalue x y) : I2F_refine_MCFG I2F_dvalue
    (@raiseLLVM PInf _ _ _ _ x) (@raiseLLVM PFin _ _ _ _ y) :=
  mcfg_bind (mcfg_emit (E := @LLVMExcE PInf) (F := @LLVMExcE PFin) (@LLVMExc PInf x) (@LLVMExc PFin y)
    (fun _ _ ↦ False) h (fun a _ _ ↦ Empty.elim a)) fun a _ _ ↦ Empty.elim a

theorem I2F_denote_vellvm (ret_typ : dtyp) (entry : function_id)
    {xs : List (dtyp × @dvalue PInf)} {ys : List (dtyp × @dvalue PFin)} (m : mcfg dtyp)
    (h : I2F_targs xs ys) : I2F_refine_MCFG I2F_dvalue
      (@denote_vellvm PInf ret_typ entry xs m) (@denote_vellvm PFin ret_typ entry ys m) := by
  rw [@denote_vellvm_source PInf, @denote_vellvm_source PFin]
  apply mcfg_bind (I2F_build_global_environment m)
  intro _ _ _
  apply mcfg_bind (ruttc_map_monad _ _ _ _ (prod_rel Eq I2F_function_denotation)
    _ _ m.m_definitions (fun df _ ↦ I2F_address_one_function df))
  intro defs₁ defs₂ hd
  refine mcfg_bind (ruttc_map_monad_gen _ _ _ _ (prod_rel Eq I2F_function_denotation)
    (@address_one_library_function PInf) (@address_one_library_function PFin) _ _ ?_) ?_
  · apply (I2F_library_functions m.m_declarations).imp
    rintro ⟨fid, f⟩ ⟨gid, g⟩ ⟨he, hg⟩
    change fid = gid at he
    subst gid
    exact I2F_address_one_library_function fid hg
  · intro libs₁ libs₂ hl
    apply mcfg_bind (mcfg_gread entry)
    intro a b hab
    apply mcfg_bind (I2F_denote_mcfg ret_typ hab h (I2F_ctx_of_list (List.rel_append hd hl)))
    intro v w hv
    cases hv with
    | inl hex => exact raise_exception hex
    | inr hret => exact ruttc_ret _ _ hret

theorem I2F_interpreter_gen (ret_typ : dtyp) (entry : function_id)
    {a : @MCFGtop PInf (List (dtyp × @dvalue PInf))} {b : @MCFGtop PFin (List (dtyp × @dvalue PFin))}
    (prog : ll_toplevel_entities) (h : I2F_refine_MCFG I2F_targs a b) :
    I2F_refine_MCFGbot (prod_rel I2F_dvalue I2F_FusedS)
      (@interpreter_gen PInf ret_typ entry a prog) (@interpreter_gen PFin ret_typ entry b prog) :=
  I2F_interp_mcfg_bind I2F_targs I2F_dvalue a b _ _ h
    (fun _ _ ha ↦ I2F_denote_vellvm ret_typ entry _ ha) _ _ I2F_initial_FusedS

theorem I2F_interpreter_param (args : List IRString) (prog : ll_toplevel_entities) :
    I2F_refine_MCFGbot (prod_rel I2F_dvalue I2F_FusedS)
      (@interpreter_param PInf args prog) (@interpreter_param PFin args prog) :=
  I2F_interpreter_gen _ _ prog (I2F_build_main_args args)

end Vellvm.Theory.I2F.I2F_toplevel
