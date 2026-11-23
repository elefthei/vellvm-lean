import Vellvm.Semantics.Denotation
import Vellvm.Theory.I2F.I2F_denotation.Terminators

namespace Vellvm.Theory.I2F.I2F_denotation
open Semantics.Denotation Syntax.DynamicTypes Syntax.LLVMAst Syntax.CFG Syntax.RawIdMaps Refinement
open Numeric.Rocqlib (option_rel)
open Utils.RelationsUtil (TT)
open Utils.rutt_cutoff (ruttc_ret ruttc_iter)

theorem I2F_denote_code (c : code dtyp) {va vb} (h : option_rel I2F_Addr va vb) :
    I2F_refine_CFG TT (@denote_code PInf c va) (@denote_code PFin c vb) := by
  induction c with
  | nil => exact ruttc_ret _ _ trivial
  | cons i is ih => exact cfg_bind (I2F_denote_instr i va vb h) fun _ _ _ ↦ ih

theorem I2F_denote_block (pred : block_id) (b : block dtyp) {va vb} (h : option_rel I2F_Addr va vb) :
    I2F_refine_CFG (Sum.LiftRel Eq I2F_dvalue) (@denote_block PInf b pred va)
      (@denote_block PFin b pred vb) :=
  cfg_bind (I2F_denote_phis pred b.blk_phis) fun _ _ _ ↦
    cfg_bind (I2F_denote_code b.blk_code h) fun _ _ _ ↦ I2F_denote_terminator b.blk_term

theorem I2F_denote_ocfg (graph : ocfg dtyp) (entry : block_id × block_id) {va vb}
    (h : option_rel I2F_Addr va vb) : I2F_refine_CFG (Sum.LiftRel Eq I2F_dvalue)
      (@denote_ocfg PInf graph va entry) (@denote_ocfg PFin graph vb entry) := by
  unfold denote_ocfg Worker.denote_ocfg Worker.denote_ocfg_map
  refine ruttc_iter cutUB cutOOM I2FE_CFG I2FA_CFG _ Eq _ _ ?_ entry entry rfl
  rintro ⟨pred, src⟩ _ rfl
  dsimp only
  cases RM.find src (ocfg_map graph) with
  | none => exact ruttc_ret _ _ (.inr (.inl rfl))
  | some b =>
    apply cfg_bind (I2F_denote_block pred b h)
    intro x y hxy
    cases hxy with
    | inl eq => cases eq; exact ruttc_ret _ _ (.inl rfl)
    | inr hv => exact ruttc_ret _ _ (.inr (.inr hv))

theorem I2F_denote_cfg (graph : cfg dtyp) {va vb} (h : option_rel I2F_Addr va vb) :
    I2F_refine_CFG I2F_dvalue (@denote_cfg PInf graph va) (@denote_cfg PFin graph vb) := by
  unfold denote_cfg Worker.denote_cfg Worker.denote_cfg_map
  apply cfg_bind (I2F_denote_ocfg graph.blks (graph.init, graph.init) h)
  intro x y hxy
  cases hxy with
  | inl eq => cases eq; apply cfg_raise
  | inr hv => exact ruttc_ret _ _ hv

end Vellvm.Theory.I2F.I2F_denotation
