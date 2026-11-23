import Vellvm.Semantics.TopLevel.Addressing
import Vellvm.Theory.I2F.I2F_attributes
import Vellvm.Theory.I2F.I2F_denotation.Context
import Vellvm.Theory.I2F.Refinement.TreeLaws
import Vellvm.Theory.I2F.I2F_toplevel.Allocation
import Vellvm.Utils.IntMaps.Refinement

namespace Vellvm.Theory.I2F.I2F_toplevel
open CTree (CTree)
open Refinement I2F_attributes I2F_denotation Semantics.DynamicValues Semantics.Denotation
open Semantics Semantics.LLVMEvents Semantics.TopLevel Syntax.LLVMAst
open Utils.IntMaps Utils.RelationsUtil Utils.rutt_cutoff

theorem address_related (fid : function_id) (msg : IRString) : I2F_refine_MCFG Eq
    (TopLevel.Worker.address (Pa := PInf) fid msg) (TopLevel.Worker.address (Pa := PFin) fid msg) := by
  unfold TopLevel.Worker.address
  apply mcfg_bind (mcfg_gread fid)
  intro x y h
  rw [I2F_dvalue_ptr_address h]
  cases dvalue_ptr_address (Pa := PFin) y with
  | some z => exact ruttc_ret z z rfl
  | none => exact I2F_refine_lift Eq _ _ (I2F_EOU_error msg msg)

theorem I2F_address_one_library_function (fid : function_id) {f : @function_denotation PInf}
    {g : @function_denotation PFin} (h : I2F_function_denotation f g) :
    I2F_refine_MCFG (prod_rel Eq I2F_function_denotation)
      (@address_one_library_function PInf (fid, f)) (@address_one_library_function PFin (fid, g)) :=
  mcfg_bind (address_related fid _) fun _ _ he ↦ ruttc_ret _ _ ⟨he, h⟩

theorem I2F_ctx_of_list {l : List (Int × @function_denotation PInf)}
    {r : List (Int × @function_denotation PFin)} (h : List.Forall₂ (prod_rel Eq I2F_function_denotation) l r) :
    I2F_ctx (IP.of_list l) (IP.of_list r) :=
  IM_Refine_lookup _ _ _ (IM_Refine_Forall2 l r _ h)

end Vellvm.Theory.I2F.I2F_toplevel
