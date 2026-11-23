import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_denotation.Terminators

open Vellvm.Semantics.Denotation Vellvm.Semantics.DynamicValues
open Vellvm.Syntax.LLVMAst Vellvm.Syntax.DynamicTypes
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_denotation
open Vellvm.Utils.RelationsUtil (prod_rel)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_select_switch"
  I2F_select_switch : ∀ {v₁ : @dvalue PInf} {v₂ : @dvalue PFin}, I2F_dvalue v₁ v₂ →
    ∀ {sw₁ : List (@dvalue PInf × block_id)} {sw₂ : List (@dvalue PFin × block_id)},
    List.Forall₂ (prod_rel I2F_dvalue Eq) sw₁ sw₂ → ∀ db : block_id,
    @select_switch PInf v₁ db sw₁ = @select_switch PFin v₂ db sw₂

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_denote_terminator"
  I2F_denote_terminator : ∀ t : (instr_id × terminator dtyp) × List (metadata dtyp),
    I2F_refine_CFG (Sum.LiftRel Eq I2F_dvalue) (@denote_terminator PInf t) (@denote_terminator PFin t)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_denote_phi"
  I2F_denote_phi : ∀ (pred : block_id) (p : (local_id × phi dtyp) × List (metadata dtyp)),
    I2F_refine_CFG (prod_rel Eq I2F_dvalue) (@denote_phi PInf pred p) (@denote_phi PFin pred p)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_denote_phis"
  I2F_denote_phis : ∀ (pred : block_id) (ps : List ((local_id × phi dtyp) × List (metadata dtyp))),
    I2F_refine_CFG (fun _ _ ↦ True) (@denote_phis PInf pred ps) (@denote_phis PFin pred ps)
