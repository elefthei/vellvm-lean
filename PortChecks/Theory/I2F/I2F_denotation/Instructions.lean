import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_denotation.Instructions

open Vellvm Vellvm.Syntax.LLVMAst Vellvm.Syntax.DynamicTypes
open Vellvm.Semantics.Denotation Vellvm.Numeric.Rocqlib
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_denotation

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_denote_operand_bundles"
  I2F_denote_operand_bundles : ∀ (loc : IRString) (f : exp dtyp) (obs : List (@operand_bundle dtyp)),
    I2F_refine_CFG (fun _ _ ↦ True)
      (@denote_operand_bundles PInf loc f obs) (@denote_operand_bundles PFin loc f obs)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_denote_call_args"
  I2F_denote_call_args : ∀ (args : List (texp dtyp × List param_attr)) (msg : IRString),
    I2F_refine_CFG I2F_targs (@denote_call_args PInf args msg) (@denote_call_args PFin args msg)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_denote_instr"
  I2F_denote_instr : ∀ (i : (instr_id × instr dtyp) × List (metadata dtyp))
    (va1 : Option PInf.PTR.ptr) (va2 : Option PFin.PTR.ptr), option_rel I2F_Addr va1 va2 →
    I2F_refine_CFG (fun _ _ ↦ True) (@denote_instr PInf i va1) (@denote_instr PFin i va2)
