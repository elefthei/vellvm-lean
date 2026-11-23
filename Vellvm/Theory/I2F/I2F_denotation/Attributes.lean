import Vellvm.Theory.I2F.I2F_denotation.Core
import Vellvm.Theory.I2F.I2F_attributes
import Vellvm.Semantics.Attributes.Bundles

namespace Vellvm.Theory.I2F.I2F_denotation
open Semantics Semantics.Attributes Semantics.DynamicValues Semantics.LLVMEvents Semantics.EOU
open Syntax.DynamicTypes Syntax.LLVMAst Refinement I2F_attributes
open Vellvm.Tree (NoChoice)
open Utils.rutt_cutoff (ruttc_ret)

private theorem units : I2F_refine_CFG (fun _ _ ↦ True) (pure ()) (pure ()) :=
  ruttc_ret _ _ trivial

private theorem ubUnit (msg : IRString) : I2F_refine_CFG (fun _ _ : Unit ↦ True)
    (raiseUB msg) (raiseUB msg) :=
  I2F_refine_lift' _ (raise_ub msg) (raise_ub msg) (I2F_EOU_ub _ _)

private theorem loadRelated (dt : dtyp) {a b} (h : I2F_dvalue a b) :
    I2F_refine_CFG I2F_dvalue (load (Pa := PInf) dt a) (load (Pa := PFin) dt b) :=
  cfg_emit (D₁ := @MemoryE PInf) (D₂ := @MemoryE PFin) (@Load PInf dt a) (@Load PFin dt b)
    ⟨rfl, h⟩ (fun _ _ hab ↦ hab)

theorem I2F_assert_dereferenceable (or_null : Bool) (n : Nat) {v1 v2} (msg : IRString)
    (h : I2F_dvalue v1 v2) : I2F_refine_CFG (fun _ _ ↦ True)
      (assert_dereferenceable (Pa := PInf) or_null n v1 msg)
      (assert_dereferenceable (Pa := PFin) or_null n v2 msg) := by
  have hv := h
  cases h with
  | I2F_dvalue_Base hb =>
    cases hb <;> try first | exact cfg_raise _ _ _ | exact ubUnit _
    rename_i p q hp
    have ha : PInf.P2I.ptr_to_int p = PFin.P2I.ptr_to_int q := hp.1
    have hn : PInf.P2I.ptr_to_int PInf.PTR.null = PFin.P2I.ptr_to_int PFin.PTR.null := rfl
    simp only [assert_dereferenceable, Attributes.Worker.assert_dereferenceable, ha, hn]
    split
    · exact units
    · exact cfg_bind (loadRelated _ hv) fun _ _ _ ↦ units
  | _ => exact cfg_raise _ _ _

theorem I2F_assert_attrs_dereferenceable (attrs : List param_attr) {v1 v2} (msg : IRString)
    (h : I2F_dvalue v1 v2) : I2F_refine_CFG (fun _ _ ↦ True)
      (assert_attrs_dereferenceable (Pa := PInf) attrs v1 msg)
      (assert_attrs_dereferenceable (Pa := PFin) attrs v2 msg) := by
  unfold assert_attrs_dereferenceable Attributes.Worker.assert_attrs_dereferenceable
  cases attrs.findSome? attr_dereferenceable with
  | none => exact units
  | some a =>
    obtain ⟨or_null, n⟩ := a
    have hv := h
    cases h with
    | I2F_dvalue_Base hb =>
      cases hb <;> first | exact units | exact I2F_assert_dereferenceable _ _ msg hv
    | _ => exact units

theorem I2F_assert_load_dereferenceable (md : List (metadata dtyp)) {v1 v2} (msg : IRString)
    (h : I2F_dvalue v1 v2) : I2F_refine_CFG (fun _ _ ↦ True)
      (assert_load_dereferenceable (Pa := PInf) md v1 msg)
      (assert_load_dereferenceable (Pa := PFin) md v2 msg) := by
  unfold assert_load_dereferenceable Attributes.Worker.assert_load_dereferenceable
  cases load_metadata_dereferenceable md with
  | none => exact units
  | some a => exact I2F_assert_dereferenceable a.1 _ msg h

theorem I2F_apply_attrs (attrs : List param_attr) (msg : IRString) (dt : dtyp) {v1 v2}
    (h : I2F_dvalue v1 v2) : I2F_refine_CFG I2F_dvalue
      (apply_attrs (Pa := PInf) attrs msg dt v1) (apply_attrs (Pa := PFin) attrs msg dt v2) := by
  unfold apply_attrs Attributes.Worker.apply_attrs
  apply cfg_bind (I2F_refine_lift' _ _ _ (I2F_apply_value_attrs attrs msg dt h))
  intro a b hab
  exact cfg_bind (I2F_assert_attrs_dereferenceable attrs msg hab) fun _ _ _ ↦ ruttc_ret a b hab

theorem I2F_apply_args_attrs (attrss : List (List param_attr)) (msg : IRString) {xs ys}
    (h : I2F_targs xs ys) : I2F_refine_CFG I2F_targs
      (apply_args_attrs (Pa := PInf) attrss msg xs) (apply_args_attrs (Pa := PFin) attrss msg ys) := by
  induction h generalizing attrss with
  | nil => exact ruttc_ret _ _ List.Forall₂.nil
  | @cons x y xs ys hxy _ ih =>
    obtain ⟨t, v⟩ := x
    obtain ⟨u, w⟩ := y
    obtain ⟨htu, hvw⟩ := hxy
    change t = u at htu
    subst u
    unfold apply_args_attrs
    simp only [Attributes.Worker.apply_args_attrs]
    apply cfg_bind (I2F_apply_attrs (attrss.headD []) msg t hvw)
    intro a b hab
    exact cfg_bind (ih attrss.tail) fun l r hlr ↦ ruttc_ret _ _ (List.Forall₂.cons ⟨rfl, hab⟩ hlr)

theorem I2F_check_call_return (fattrs : List fn_attr) (ret_attrs : List param_attr)
    (ranges : Option (List (int_syntax × int_syntax))) (loc : IRString) (ret_t : dtyp)
    {xs ys r1 r2} (ha : List.Forall₂ I2F_dvalue xs ys) (hr : I2F_exc_dvalue r1 r2) :
    I2F_refine_CFG I2F_exc_dvalue (check_call_return (Pa := PInf) fattrs ret_attrs ranges loc ret_t xs r1)
      (check_call_return (Pa := PFin) fattrs ret_attrs ranges loc ret_t ys r2) := by
  unfold check_call_return Attributes.Worker.check_call_return
  apply cfg_bind (I2F_refine_lift' _ _ _ (I2F_check_call_result fattrs loc ha hr))
  intro _ _ _
  cases hr with
  | inl h => exact ruttc_ret _ _ (Sum.LiftRel.inl h)
  | inr h =>
    exact cfg_bind (I2F_apply_attrs ret_attrs _ ret_t (I2F_value_metadata_range ranges ret_t h))
      fun _ _ hab ↦ ruttc_ret _ _ (Sum.LiftRel.inr hab)

private abbrev InfCheck := assume_bundle_check (Pa := PInf) (E := @CFGEtop PInf) (B := NoChoice)
private abbrev FinCheck := assume_bundle_check (Pa := PFin) (E := @CFGEtop PFin) (B := NoChoice)

def I2F_assume_bundle_check (l : InfCheck) (r : FinCheck) : Prop :=
  ∀ loc xs ys, List.Forall₂ I2F_dvalue xs ys → I2F_refine_CFG (fun _ _ ↦ True) (l loc xs) (r loc ys)

private theorem malformed (loc tag : IRString) : I2F_refine_CFG (fun _ _ : Unit ↦ True)
    (assume_malformed loc tag) (assume_malformed loc tag) := cfg_raise _ _ _

private theorem violated (loc tag : IRString) : I2F_refine_CFG (fun _ _ : Unit ↦ True)
    (assume_violated loc tag) (assume_violated loc tag) := ubUnit _

local macro "check_branches" : tactic => `(tactic|
  repeat' first | exact units | exact violated _ _ | split)

theorem I2F_assume_nonnull : I2F_assume_bundle_check (assume_nonnull (Pa := PInf))
    (assume_nonnull (Pa := PFin)) := by
  intro loc xs ys hs
  cases hs with
  | nil => exact malformed _ _
  | cons hp ht =>
    cases ht with
    | cons => exact malformed _ _
    | nil =>
      simp only [assume_nonnull, Attributes.Worker.assume_nonnull, I2F_dvalue_ptr_address hp]
      check_branches

theorem I2F_assume_noundef : I2F_assume_bundle_check (assume_noundef (Pa := PInf))
    (assume_noundef (Pa := PFin)) := by
  intro loc xs ys hs
  cases hs with
  | nil => exact malformed _ _
  | cons hv ht =>
    cases ht with
    | cons => exact malformed _ _
    | nil =>
      simp only [assume_noundef, Attributes.Worker.assume_noundef, I2F_exp.I2F_dvalue_well_defined hv]
      check_branches

theorem I2F_assume_align : I2F_assume_bundle_check (assume_align (Pa := PInf))
    (assume_align (Pa := PFin)) := by
  intro loc xs ys hs
  cases hs with
  | nil => exact malformed _ _
  | cons hp ht =>
    cases ht with
    | nil => exact malformed _ _
    | cons hal hos =>
      simp only [assume_align, Attributes.Worker.assume_align, I2F_dvalue_ptr_address hp,
        I2F_bundle_uint hal]
      cases hos with
      | nil => dsimp only; check_branches
      | cons ho ht =>
        cases ht <;> dsimp only <;> (try rw [I2F_bundle_sint ho]) <;> check_branches

theorem I2F_assume_dereferenceable (or_null : Bool) : I2F_assume_bundle_check
    (assume_dereferenceable (Pa := PInf) or_null) (assume_dereferenceable (Pa := PFin) or_null) := by
  intro loc xs ys hs
  cases hs with
  | nil => exact malformed _ _
  | cons hp ht =>
    cases ht with
    | nil => exact malformed _ _
    | cons hn ht =>
      cases ht with
      | cons => exact malformed _ _
      | nil =>
        simp only [assume_dereferenceable, Attributes.Worker.assume_dereferenceable,
          I2F_dvalue_ptr_address hp, I2F_bundle_uint hn]
        repeat' first | exact I2F_assert_dereferenceable or_null _ _ hp | exact violated _ _
                      | exact units | split

theorem I2F_assume_bundle_checks : List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ I2F_assume_bundle_check a.2 b.2)
    (assume_bundle_checks (Pa := PInf)) (assume_bundle_checks (Pa := PFin)) :=
  .cons ⟨rfl, I2F_assume_nonnull⟩ <| .cons ⟨rfl, I2F_assume_noundef⟩ <|
  .cons ⟨rfl, I2F_assume_align⟩ <| .cons ⟨rfl, I2F_assume_dereferenceable false⟩ <|
  .cons ⟨rfl, I2F_assume_dereferenceable true⟩ .nil

theorem I2F_find_bundle_check (tag : IRString) {l : List (IRString × InfCheck)}
    {r : List (IRString × FinCheck)} (h : List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ I2F_assume_bundle_check a.2 b.2) l r) :
    match (l.find? (fun p ↦ p.1 == tag)).map Prod.snd, (r.find? (fun p ↦ p.1 == tag)).map Prod.snd with
    | some a, some b => I2F_assume_bundle_check a b
    | none, none => True
    | _, _ => False := by
  induction h with
  | nil => trivial
  | @cons _ b _ _ h _ ih =>
    simp only [List.find?_cons, h.1]
    cases b.1 == tag <;> first | exact h.2 | exact ih

theorem I2F_bundle_check (f : exp dtyp) (tag : IRString) :
    match bundle_check (Pa := PInf) (E := @CFGEtop PInf) (B := NoChoice) f tag,
          bundle_check (Pa := PFin) (E := @CFGEtop PFin) (B := NoChoice) f tag with
    | some a, some b => I2F_assume_bundle_check a b
    | none, none => True
    | _, _ => False := by
  unfold bundle_check Attributes.Worker.bundle_check
  cases is_llvm_assume f <;> first | trivial | exact I2F_find_bundle_check tag I2F_assume_bundle_checks

end Vellvm.Theory.I2F.I2F_denotation
