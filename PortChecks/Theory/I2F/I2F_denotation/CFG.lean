import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_denotation.CFG

namespace PortChecks.I2FDenotationCFG
open Vellvm.Syntax.LLVMAst Vellvm.Syntax.DynamicTypes Vellvm.Syntax.CFG Vellvm.Semantics.Denotation
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_denotation
open Vellvm.Numeric.Rocqlib (option_rel)
open Vellvm.Utils.RelationsUtil (TT)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_denote_code"
  I2F_denote_code : ∀ (c : code dtyp) {va vb}, option_rel I2F_Addr va vb →
    I2F_refine_CFG TT (denote_code (Pa := PInf) c va) (denote_code (Pa := PFin) c vb)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_denote_block"
  I2F_denote_block : ∀ (pred : block_id) (b : block dtyp) {va vb}, option_rel I2F_Addr va vb →
    I2F_refine_CFG (Sum.LiftRel Eq I2F_dvalue) (denote_block (Pa := PInf) b pred va)
      (denote_block (Pa := PFin) b pred vb)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_denote_ocfg"
  I2F_denote_ocfg : ∀ (graph : ocfg dtyp) (entry : block_id × block_id) {va vb},
    option_rel I2F_Addr va vb → I2F_refine_CFG (Sum.LiftRel Eq I2F_dvalue)
      (@denote_ocfg PInf graph va entry) (@denote_ocfg PFin graph vb entry)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_denote_cfg"
  I2F_denote_cfg : ∀ (graph : cfg dtyp) {va vb}, option_rel I2F_Addr va vb →
    I2F_refine_CFG I2F_dvalue (denote_cfg (Pa := PInf) graph va) (denote_cfg (Pa := PFin) graph vb)

end PortChecks.I2FDenotationCFG
