import Vellvm.Semantics.Denotation.Instructions
import Vellvm.Theory.I2F.I2F_denotation.Attributes
import Vellvm.Theory.I2F.I2F_exp.Operations
import Vellvm.Theory.I2F.I2F_exp.Arithmetic

namespace Vellvm.Theory.I2F.I2F_denotation
open Syntax.LLVMAst Syntax.DynamicTypes Syntax.AstLib
open Semantics Semantics.DynamicValues Semantics.Denotation
open Semantics.LLVMEvents Refinement I2F_exp I2F_attributes
open Numeric.Rocqlib (option_rel)
open Utils.RelationsUtil (TT)
open Utils.rutt_cutoff (ruttc_ret ruttc_map_monad)
open Utils.ListUtil (map_monad loop_monad)
open Vellvm.Tree (NoChoice)

private theorem instrLoad (dt : dtyp) {p q} (h : I2F_dvalue p q) :
    I2F_refine_CFG I2F_dvalue (load (Pa := PInf) dt p) (load (Pa := PFin) dt q) :=
  cfg_emit (D₁ := @MemoryE PInf) (D₂ := @MemoryE PFin) (@Load PInf dt p) (@Load PFin dt q)
    ⟨rfl, h⟩ (fun _ _ ab ↦ ab)

private theorem instrStore (dt : dtyp) {p q v w} (hp : I2F_dvalue p q) (hv : I2F_dvalue v w) :
    I2F_refine_CFG TT (store (Pa := PInf) dt p v) (store (Pa := PFin) dt q w) :=
  cfg_emit (D₁ := @MemoryE PInf) (D₂ := @MemoryE PFin) (@Store PInf dt p v) (@Store PFin dt q w)
    ⟨rfl, hp, hv⟩ (fun _ _ _ ↦ trivial)

private theorem instrWrite (id : raw_id) {v w} (h : I2F_dvalue v w) :
    I2F_refine_CFG TT (lwrite (Pa := PInf) id v) (lwrite (Pa := PFin) id w) :=
  cfg_emit (D₁ := @LocalE PInf) (D₂ := @LocalE PFin) (@LocalWrite PInf id v) (@LocalWrite PFin id w)
    ⟨rfl, h⟩ (fun _ _ _ ↦ trivial)

private theorem instrUB {X Y : Type} (R : X → Y → Prop) (msg : IRString) :
    I2F_refine_CFG R (raiseUB msg) (raiseUB msg) :=
  I2F_refine_lift' R _ _ (.I2F_EOU_ub msg (.raise_ub msg))

private theorem instrThrow {X Y : Type} (R : X → Y → Prop) {v w} (h : I2F_dvalue v w) :
    I2F_refine_CFG R (@raiseLLVM PInf _ _ _ _ v) (@raiseLLVM PFin _ _ _ _ w) := by
  apply cfg_bind (RR := fun _ _ ↦ False)
    (cfg_emit (D₁ := @LLVMExcE PInf) (D₂ := @LLVMExcE PFin) (@LLVMExc PInf v) (@LLVMExc PFin w)
      h (fun _ _ ab ↦ ab))
  exact fun _ _ ab ↦ ab.elim

theorem I2F_denote_operand_bundles (loc : IRString) (f : exp dtyp) (obs : List (@operand_bundle dtyp)) :
    I2F_refine_CFG (fun _ _ ↦ True)
      (@denote_operand_bundles PInf loc f obs) (@denote_operand_bundles PFin loc f obs) := by
  unfold denote_operand_bundles Denotation.Worker.denote_operand_bundles
  induction obs with
  | nil => exact ruttc_ret _ _ trivial
  | cons ob obs ih =>
    simp only [loop_monad]
    refine cfg_bind (RR := TT) ?_ fun _ _ _ ↦ ih
    refine cfg_bind (RR := List.Forall₂ I2F_dvalue) ?_ ?_
    · apply ruttc_map_monad
      rintro (⟨t, e⟩ | _) _
      · exact I2F_denote_exp' e (some t)
      · exact ruttc_ret _ _ (.I2F_dvalue_Base .I2F_dvalue_None)
    · intro xs ys hs
      have hc := I2F_bundle_check f ob.ob_tag
      unfold Attributes.bundle_check at hc
      generalize Attributes.Worker.bundle_check (M := CTree.CTree) (Pa := PInf)
        (E := @CFGEtop PInf) (B := NoChoice) f ob.ob_tag = l at hc ⊢
      generalize Attributes.Worker.bundle_check (M := CTree.CTree) (Pa := PFin)
        (E := @CFGEtop PFin) (B := NoChoice) f ob.ob_tag = r at hc ⊢
      cases l <;> cases r <;>
        first | exact ruttc_ret _ _ trivial | exact False.elim hc | exact hc loc xs ys hs

theorem I2F_denote_call_args (args : List (texp dtyp × List param_attr)) (msg : IRString) :
    I2F_refine_CFG I2F_targs (@denote_call_args PInf args msg) (@denote_call_args PFin args msg) := by
  unfold denote_call_args Denotation.Worker.denote_call_args I2F_targs
  apply ruttc_map_monad
  rintro ⟨⟨t, e⟩, attrs⟩ _
  refine cfg_bind (I2F_denote_exp' e (some t)) fun _ _ h ↦ ?_
  refine cfg_bind (I2F_apply_attrs attrs msg t h) fun _ _ ha ↦ ?_
  exact ruttc_ret _ _ ⟨rfl, ha⟩

private theorem instrRmwOp (op : atomic_rmw_operation) (dt : dtyp) {p q v w}
    (hp : I2F_dvalue p q) (hv : I2F_dvalue v w) : I2F_refine_CFG I2F_dvalue
      (@denote_atomic_rmw_operation PInf op dt p v) (@denote_atomic_rmw_operation PFin op dt q w) := by
  cases op <;> simp only [denote_atomic_rmw_operation, Denotation.Worker.denote_atomic_rmw_operation]
  all_goals try first
    | exact ruttc_ret _ _ hv
    | exact cfg_raise _ _ _
    | exact I2F_refine_lift' _ _ _ (I2F_eval_iop _ dt hp hv)
    | exact I2F_refine_lift' _ _ _ (I2F_eval_fop _ dt hp hv)
  cases hv <;> try exact cfg_raise _ _ _
  cases ‹I2F_dvalue_base _ _› <;> try exact cfg_raise _ _ _
  apply I2F_refine_lift'
  refine I2F_EOU_bind _ _ (I2F_eval_iop .And dt hp (.I2F_dvalue_Base (.I2F_dvalue_Int _))) ?_
  exact fun _ _ h ↦ I2F_eval_iop _ dt (.I2F_dvalue_Base (.I2F_dvalue_Int _)) h

private theorem instrRmw (id : raw_id) (a : atomicrmw dtyp) : I2F_refine_CFG TT
    (@denote_atomicrmw PInf id a) (@denote_atomicrmw PFin id a) := by
  rcases a with ⟨_, op, ⟨t, e⟩, ⟨dt, val⟩, _, _, _⟩
  simp only [denote_atomicrmw, Denotation.Worker.denote_atomicrmw]
  refine cfg_bind (I2F_denote_exp' _ _) fun _ _ ptr ↦ ?_
  refine cfg_bind (I2F_denote_exp' _ _) fun _ _ v ↦ ?_
  refine cfg_bind (I2F_refine_lift' _ _ _ (I2F_assert_aligned_to _ _ ptr)) fun _ _ _ ↦ ?_
  refine cfg_bind (instrLoad dt ptr) fun _ _ loaded ↦ ?_
  refine cfg_bind (instrRmwOp op dt loaded v) fun _ _ stored ↦ ?_
  exact cfg_bind (instrStore dt ptr stored) fun _ _ _ ↦ instrWrite id loaded

private theorem instrCmpXchg (id : raw_id) (c : cmpxchg dtyp) : I2F_refine_CFG TT
    (@denote_cmpxchg PInf id c) (@denote_cmpxchg PFin id c) := by
  rcases c with ⟨_, _, ⟨_, _⟩, ⟨dt, _⟩, ⟨dt', _⟩, _, _, _, _⟩
  simp only [denote_cmpxchg, Denotation.Worker.denote_cmpxchg]
  split
  · exact cfg_raise _ _ _
  · refine cfg_bind (I2F_denote_exp' _ _) fun _ _ ptr ↦ ?_
    refine cfg_bind (I2F_denote_exp' _ _) fun _ _ cmp ↦ ?_
    refine cfg_bind (I2F_denote_exp' _ _) fun _ _ newVal ↦ ?_
    refine cfg_bind (I2F_refine_lift' _ _ _ (I2F_assert_aligned_to _ _ ptr)) fun _ _ _ ↦ ?_
    refine cfg_bind (instrLoad dt ptr) fun _ _ loaded ↦ ?_
    refine cfg_bind (I2F_refine_lift' _ _ _ (I2F_eval_icmp false .Eq dt loaded cmp)) fun _ _ flag ↦ ?_
    cases flag <;> try exact cfg_raise _ _ _
    cases ‹I2F_dvalue_base _ _› <;> try first | exact cfg_raise _ _ _ | exact instrUB _ _
    rename_i sz bit
    obtain ⟨n, hn⟩ := sz
    cases n with
    | zero => contradiction
    | succ n =>
      cases n with
      | succ n => exact cfg_raise _ _ _
      | zero =>
        by_cases hbit : Numeric.Integers.eq bit Numeric.Integers.one = true
        · simp only [hbit, ite_true]
          refine cfg_bind (instrStore dt ptr newVal) fun _ _ _ ↦ ?_
          exact instrWrite id (.I2F_dvalue_Struct false
            (.cons loaded (.cons (.I2F_dvalue_Base (.I2F_dvalue_Int _)) .nil)))
        · simp only [hbit, ite_false]
          exact instrWrite id (.I2F_dvalue_Struct false
            (.cons loaded (.cons (.I2F_dvalue_Base (.I2F_dvalue_Int _)) .nil)))

private theorem instrInvoke (fn : texp dtyp) (args : List (texp dtyp × List param_attr))
    (anns : List (annotation dtyp)) (obs : List (@operand_bundle dtyp)) (md : List (metadata dtyp))
    (iid : instr_id) {va vb} (hav : option_rel I2F_Addr va vb) : I2F_refine_CFG TT
      (@denote_instr PInf ((iid, .INSTR_Call fn args anns obs), md) va)
      (@denote_instr PFin ((iid, .INSTR_Call fn args anns obs), md) vb) := by
  obtain ⟨dt, f⟩ := fn
  cases iid <;> unfold denote_instr Denotation.Worker.denote_instr
  all_goals
    refine cfg_bind (RR := TT) (ruttc_ret _ _ trivial) fun _ _ _ ↦ ?_
    refine cfg_bind (I2F_denote_call_args args _) fun xs ys hs ↦ ?_
    refine cfg_bind (I2F_denote_operand_bundles _ f obs) fun _ _ _ ↦ ?_
    dsimp only
    cases hint : IntrinsicsDefinitions.intrinsic_exp f <;> first
      | rename_i s
        refine cfg_bind (RR := I2F_exc_dvalue) (cfg_emit (D₁ := @IntrinsicE PInf)
          (D₂ := @IntrinsicE PFin) (@Intrinsic PInf dt s xs va) (@Intrinsic PFin dt s ys vb)
          ⟨rfl, rfl, hs, hav⟩ (fun _ _ h ↦ h)) ?_
      | refine cfg_bind (I2F_denote_exp' f none) fun x y hf ↦ ?_
        refine cfg_bind (RR := I2F_exc_dvalue) (cfg_emit (D₁ := @CallE PInf) (D₂ := @CallE PFin)
          (@Call PInf dt _ x xs) (@Call PFin dt _ y ys) ⟨rfl, rfl, hf, hs⟩ (fun _ _ h ↦ h)) ?_
    all_goals
      intro _ _ hr
      refine cfg_bind (I2F_check_call_return _ _ _ _ dt (I2F_targs_snd hs) hr) fun _ _ hr' ↦ ?_
      cases hr' <;> first | exact instrThrow _ ‹_› | exact ruttc_ret _ _ trivial | exact instrWrite _ ‹_›

theorem I2F_denote_instr (i : (instr_id × instr dtyp) × List (metadata dtyp))
    (va1 : Option PInf.PTR.ptr) (va2 : Option PFin.PTR.ptr) (h : option_rel I2F_Addr va1 va2) :
    I2F_refine_CFG TT (@denote_instr PInf i va1) (@denote_instr PFin i va2) := by
  rcases i with ⟨⟨iid, ins⟩, md⟩
  cases ins <;> try exact instrInvoke _ _ _ _ _ _ h
  all_goals cases iid <;> unfold denote_instr Denotation.Worker.denote_instr
  all_goals
    refine cfg_bind (RR := TT) (ruttc_ret () () trivial) fun u v huv ↦ ?_
    clear u v huv
  all_goals try first
    | exact cfg_raise _ _ _
    | exact ruttc_ret _ _ trivial
    | exact instrCmpXchg _ _
    | exact instrRmw _ _
    | exact cfg_bind (I2F_denote_exp' _ _) fun _ _ v ↦ instrWrite _ v
  case INSTR_Alloca.IId dt anns id =>
    have alloc (n : Nat) : I2F_refine_CFG I2F_dvalue
        (alloca (Pa := PInf) dt n (Attributes.explicit_alignment anns))
        (alloca (Pa := PFin) dt n (Attributes.explicit_alignment anns)) :=
      cfg_emit (D₁ := @MemoryE PInf) (D₂ := @MemoryE PFin)
        (@Alloca PInf dt n _) (@Alloca PFin dt n _) ⟨rfl, rfl, rfl⟩ (fun _ _ ab ↦ ab)
    cases he : anns.findSome? ann_num_elements with
    | none =>
      simp only [he, CTree.pure_bind']
      exact cfg_bind (alloc 1) fun _ _ hv ↦ instrWrite id hv
    | some te =>
      obtain ⟨t, e⟩ := te
      simp only [he]
      refine cfg_bind (I2F_denote_exp' e (some t)) fun v w hv ↦ ?_
      rw [I2F_dvalue_is_poison hv]
      split
      · exact cfg_bind (instrUB (fun (_ _ : Nat) ↦ False) _) fun _ _ hf ↦ hf.elim
      · refine cfg_bind (I2F_refine_lift' _ _ _ (I2F_dvalue_to_dvalue_base hv)) fun b c hb ↦ ?_
        simp only [CTree.pure_bind', I2F_dvalue_base_int_unsigned hb]
        exact cfg_bind (alloc _) fun _ _ ha ↦ instrWrite id ha
  case INSTR_Load.IId dt p anns id =>
    obtain ⟨du, p⟩ := p
    refine cfg_bind (I2F_denote_exp' p (some du)) fun _ _ a ↦ ?_
    refine cfg_bind (I2F_refine_lift' _ _ _ (I2F_assert_alignment anns _ a)) fun _ _ _ ↦ ?_
    refine cfg_bind (instrLoad dt a) fun _ _ v ↦ ?_
    refine cfg_bind (I2F_refine_lift' _ _ _ (I2F_apply_value_attrs _ _ dt
      (I2F_value_metadata_range _ dt v))) fun _ _ v' ↦ ?_
    exact cfg_bind (I2F_assert_load_dereferenceable md _ v') fun _ _ _ ↦ instrWrite id v'
  case INSTR_Store.IVoid v p anns id =>
    obtain ⟨dt, v⟩ := v
    obtain ⟨du, p⟩ := p
    refine cfg_bind (I2F_denote_exp' v (some dt)) fun _ _ hv ↦ ?_
    refine cfg_bind (I2F_denote_exp' p (some du)) fun x y ha ↦ ?_
    refine cfg_bind (I2F_refine_lift' _ _ _ (I2F_assert_alignment anns _ ha)) fun _ _ _ ↦ ?_
    have keep := ha
    cases ha <;> try exact instrStore dt keep hv
    cases ‹I2F_dvalue_base _ _› <;> first | exact instrStore dt keep hv | exact instrUB _ _
  case INSTR_LandingPad.IId _ _ _ id =>
    refine cfg_bind (cfg_emit (D₁ := @StackE PInf) (D₂ := @StackE PFin)
      (@StackGetExc PInf) (@StackGetExc PFin) (RR := option_rel I2F_dvalue) trivial (fun _ _ ab ↦ ab))
      fun _ _ hr ↦ ?_
    cases hr <;> first | exact cfg_raise _ _ _ | exact instrWrite id ‹_›
  all_goals
    refine cfg_bind (I2F_denote_exp' _ _) fun _ _ hp ↦ ?_
    refine cfg_bind (instrLoad _ hp) fun _ _ ha ↦ ?_
    refine cfg_bind (instrLoad _ ha) fun _ _ hv ↦ ?_
    refine cfg_bind (I2F_refine_lift' _ _ _ (I2F_from_Z 1)) fun _ _ ix ↦ ?_
    refine cfg_bind (I2F_refine_lift' _ _ _ (I2F_eval_gep _ _ ha
      (.cons (.I2F_dvalue_Base (.I2F_dvalue_Ptr ix)) .nil))) fun _ _ hn ↦ ?_
    refine cfg_bind (instrStore _ hp hn) fun _ _ _ ↦ ?_
    first | exact instrWrite _ hv | exact ruttc_ret _ _ trivial

end Vellvm.Theory.I2F.I2F_denotation
