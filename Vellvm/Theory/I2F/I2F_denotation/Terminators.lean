import Vellvm.Theory.I2F.I2F_denotation.Instructions
import Vellvm.Theory.I2F.I2F_denotation.Attributes
import Vellvm.Theory.I2F.I2F_exp.Operations
import Vellvm.Theory.I2F.I2F_attributes
import Vellvm.Semantics.Denotation.Terminators

namespace Vellvm.Theory.I2F.I2F_denotation
open Semantics Semantics.DynamicValues Semantics.Denotation Semantics.LLVMEvents
open Syntax.DynamicTypes Syntax.LLVMAst Syntax.AstLib Refinement I2F_exp I2F_attributes
open Utils.RelationsUtil (prod_rel)
open Utils.rutt_cutoff (ruttc_ret ruttc_map_monad)
open Utils.ListUtil (Forall2_eq)

theorem I2F_select_switch {v₁ v₂} (hv : I2F_dvalue v₁ v₂) {sw₁ sw₂}
    (hs : List.Forall₂ (prod_rel I2F_dvalue Eq) sw₁ sw₂) (db : block_id) :
    @select_switch PInf v₁ db sw₁ = @select_switch PFin v₂ db sw₂ := by
  induction hs with
  | nil => rfl
  | @cons p q xs ys hp _ ih =>
    rcases p with ⟨x, i⟩
    rcases q with ⟨y, j⟩
    obtain ⟨hxy, rfl⟩ : I2F_dvalue x y ∧ i = j := hp
    cases hv <;> try rfl
    case I2F_dvalue_Base hb =>
      cases hb <;> try rfl
      case I2F_dvalue_Int =>
        cases hxy <;> try rfl
        case I2F_dvalue_Base hb' => cases hb' <;> first | rfl | simp only [select_switch, ih]

private theorem ub {X Y : Type} (R : X → Y → Prop) (s t : IRString) :
    I2F_refine_CFG R (raiseUB s) (raiseUB t) :=
  I2F_refine_lift' R (.raise_ub s) (.raise_ub t) (.I2F_EOU_ub _ _)

private theorem writeLocal (id : local_id) {x y} (h : I2F_dvalue x y) :
    I2F_refine_CFG (fun _ _ ↦ True) (lwrite (Pa := PInf) id x) (lwrite (Pa := PFin) id y) :=
  cfg_emit (D₁ := @LocalE PInf) (D₂ := @LocalE PFin) (@LocalWrite PInf id x) (@LocalWrite PFin id y)
    ⟨rfl, h⟩ (fun _ _ _ ↦ trivial)

theorem I2F_denote_terminator (t : (instr_id × terminator dtyp) × List (metadata dtyp)) :
    I2F_refine_CFG (Sum.LiftRel Eq I2F_dvalue) (@denote_terminator PInf t)
      (@denote_terminator PFin t) := by
  rcases t with ⟨⟨iid, term⟩, md⟩
  unfold denote_terminator Denotation.Worker.denote_terminator
  refine cfg_bind (RR := fun _ _ ↦ True) (ruttc_ret () () trivial) fun _ _ _ ↦ ?_
  cases term with
  | TERM_Ret arg =>
    obtain ⟨dt, op⟩ := arg
    exact cfg_bind (I2F_denote_exp' op (some dt)) fun _ _ hv ↦ ruttc_ret _ _ (.inr hv)
  | TERM_Ret_void => exact ruttc_ret _ _ (.inr (.I2F_dvalue_Base .I2F_dvalue_None))
  | TERM_Br_1 _ => exact ruttc_ret _ _ (.inl rfl)
  | TERM_Br arg br₁ br₂ =>
    obtain ⟨dt, op⟩ := arg
    refine cfg_bind (I2F_denote_exp' op (some dt)) fun _ _ hv ↦ ?_
    cases hv <;> try exact cfg_raise _ _ _
    case I2F_dvalue_Base hb =>
      cases hb <;> try first | exact cfg_raise _ _ _ | exact ub _ _ _
      dsimp only
      split
      · exact ruttc_ret _ _ (.inl rfl)
      · exact cfg_raise _ _ _
  | TERM_Switch arg db dests =>
    obtain ⟨dt, op⟩ := arg
    refine cfg_bind (I2F_denote_exp' op (some dt)) fun v w hv ↦ ?_
    dsimp only
    rw [I2F_dvalue_is_poison hv]
    split
    · exact ub _ _ _
    · refine cfg_bind (RR := Eq) (I2F_refine_lift' _ _ _ ?_) ?_
      · apply I2F_EOU_bind (R := List.Forall₂ (prod_rel I2F_dvalue Eq))
        · apply I2F_EOU_map_monad
          rintro ⟨⟨sz, x⟩, dest⟩ _
          exact .I2F_EOU_ret _ _ ⟨.I2F_dvalue_Base (.I2F_dvalue_Int _), rfl⟩
        · intro xs ys hxy
          rw [I2F_select_switch hv hxy]
          exact I2F_EOU_refl _
      · rintro b _ rfl
        exact ruttc_ret _ _ (.inl rfl)
  | TERM_Unreachable => exact ub _ _ _
  | TERM_Invoke fnptr args normal unwind anns obs =>
    obtain ⟨dt, f⟩ := fnptr
    refine cfg_bind (I2F_denote_call_args args _) fun xs ys hargs ↦ ?_
    refine cfg_bind (I2F_denote_operand_bundles _ f obs) fun _ _ _ ↦ ?_
    refine cfg_bind (I2F_denote_exp' f none) fun x y hfv ↦ ?_
    refine cfg_bind (RR := I2F_exc_dvalue) (cfg_emit (D₁ := @CallE PInf) (D₂ := @CallE PFin)
      (@Call PInf dt _ x xs) (@Call PFin dt _ y ys) ⟨rfl, rfl, hfv, hargs⟩ (fun _ _ h ↦ h)) ?_
    intro ex ey hrv
    refine cfg_bind (I2F_check_call_return _ _ _ _ _ (I2F_targs_snd hargs) hrv) fun _ _ hr ↦ ?_
    cases hr with
    | inl hex =>
      refine cfg_bind (RR := fun _ _ ↦ True) (cfg_emit (D₁ := @StackE PInf) (D₂ := @StackE PFin)
        (@StackRaise PInf _) (@StackRaise PFin _) hex (fun _ _ _ ↦ trivial)) ?_
      exact fun _ _ _ ↦ ruttc_ret _ _ (.inl rfl)
    | inr hval =>
      cases iid with
      | IId name => exact cfg_bind (writeLocal name hval) fun _ _ _ ↦ ruttc_ret _ _ (.inl rfl)
      | IVoid _ => exact ruttc_ret _ _ (.inl rfl)
  | TERM_Resume arg =>
    obtain ⟨dt, op⟩ := arg
    refine cfg_bind (I2F_denote_exp' op (some dt)) fun x y hv ↦ ?_
    refine cfg_bind (RR := fun (_ _ : Empty) ↦ False) (cfg_emit
      (D₁ := @LLVMExcE PInf) (D₂ := @LLVMExcE PFin)
      (@LLVMExc PInf x) (@LLVMExc PFin y) hv (fun _ _ h ↦ h)) ?_
    exact fun a ↦ nomatch a
  | TERM_IndirectBr arg brs fn =>
    obtain ⟨dt, op⟩ := arg
    refine cfg_bind (I2F_denote_exp' op (some dt)) fun x y hv ↦ ?_
    dsimp only
    rw [I2F_dvalue_is_poison hv]
    split
    · exact ub _ _ _
    · cases fn with
      | none => exact cfg_raise _ _ _
      | some f =>
        refine cfg_bind (RR := List.Forall₂ Eq) (ruttc_map_monad _ _ _ _ Eq _ _ brs ?_) ?_
        · intro b _
          refine cfg_bind (RR := I2F_dvalue) (cfg_emit (D₁ := @GlobalE PInf) (D₂ := @GlobalE PFin)
            (@GlobalRead PInf (blockaddress_id f b)) (@GlobalRead PFin (blockaddress_id f b)) rfl
            (fun _ _ h ↦ h)) ?_
          exact fun _ _ h ↦ ruttc_ret _ _ (I2F_dvalue_ptr_address h)
        · intro as bs h
          cases Forall2_eq as bs h
          rw [I2F_dvalue_ptr_address hv]
          cases @dvalue_ptr_address PFin y with
          | none => exact cfg_raise _ _ _
          | some z =>
            cases ht : indirectbr_target z (brs.zip as) with
            | some b => simp only [ht]; exact ruttc_ret _ _ (.inl rfl)
            | none => simp only [ht]; exact ub _ _ _

theorem I2F_denote_phi (pred : block_id) (p : (local_id × phi dtyp) × List (metadata dtyp)) :
    I2F_refine_CFG (prod_rel Eq I2F_dvalue) (@denote_phi PInf pred p) (@denote_phi PFin pred p) := by
  rcases p with ⟨⟨id, ⟨_, dt, args⟩⟩, md⟩
  unfold denote_phi Denotation.Worker.denote_phi
  refine cfg_bind (RR := fun _ _ ↦ True) (ruttc_ret () () trivial) fun _ _ _ ↦ ?_
  cases Utils.Assoc.assoc pred args with
  | none => exact cfg_raise _ _ _
  | some op => exact cfg_bind (I2F_denote_exp' op (some dt)) fun _ _ hv ↦ ruttc_ret _ _ ⟨rfl, hv⟩

theorem I2F_denote_phis (pred : block_id) (ps : List ((local_id × phi dtyp) × List (metadata dtyp))) :
    I2F_refine_CFG (fun _ _ ↦ True) (@denote_phis PInf pred ps) (@denote_phis PFin pred ps) := by
  unfold denote_phis Denotation.Worker.denote_phis
  refine cfg_bind (ruttc_map_monad _ _ _ _ (prod_rel Eq I2F_dvalue) _ _ ps
    (fun p _ ↦ I2F_denote_phi pred p)) fun xs ys h ↦ ?_
  induction h with
  | nil => exact ruttc_ret _ _ trivial
  | @cons p q _ _ hp _ ih =>
    rcases p with ⟨i, x⟩
    rcases q with ⟨j, y⟩
    obtain ⟨rfl, hv⟩ : i = j ∧ I2F_dvalue x y := hp
    exact cfg_bind (writeLocal _ hv) fun _ _ _ ↦ ih

end Vellvm.Theory.I2F.I2F_denotation
