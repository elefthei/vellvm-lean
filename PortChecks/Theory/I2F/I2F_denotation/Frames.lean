import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_denotation.Frames

namespace PortChecks.I2FDenotationFrames
open Vellvm.Semantics.Denotation Vellvm.Syntax.LLVMAst Vellvm.Syntax.DynamicTypes Vellvm.Syntax.CFG
open Vellvm.Semantics.DynamicValues Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_denotation
open Vellvm.Utils.RelationsUtil (prod_rel)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_combine_lists_varargs"
  I2F_combine_lists_varargs : ∀ (d : definition dtyp (cfg dtyp)) {l r}, I2F_targs l r →
    I2F_EOU (prod_rel (List.Forall₂ (prod_rel Eq (prod_rel Eq I2F_dvalue))) I2F_targs)
      (combine_lists_varargs d.df_args l) (combine_lists_varargs d.df_args r)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_frame_bindings"
  I2F_frame_bindings : ∀ {l : List (raw_id × (dtyp × @dvalue PInf))}
    {r : List (raw_id × (dtyp × @dvalue PFin))},
    List.Forall₂ (prod_rel Eq (prod_rel Eq I2F_dvalue)) l r →
    List.Forall₂ (prod_rel Eq I2F_dvalue) (l.map fun (x, _, v) ↦ (x, v))
      (r.map fun (x, _, w) ↦ (x, w))

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_push_call_frame"
  I2F_push_call_frame : ∀ (d : definition dtyp (cfg dtyp)) {l r}, I2F_targs l r → I2F_refine_CFG
    I2F_Addr (push_call_frame (Pa := PInf) d l) (push_call_frame (Pa := PFin) d r)

end PortChecks.I2FDenotationFrames
