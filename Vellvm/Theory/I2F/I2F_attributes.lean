import Vellvm.Semantics.Attributes.Values
import Vellvm.Theory.I2F.I2F_exp.Values

namespace Vellvm.Theory.I2F.I2F_attributes
open Semantics.Attributes Semantics.DynamicValues Semantics.EOU
open Syntax.LLVMAst Syntax.DynamicTypes Refinement I2F_exp

private theorem unitRefl (m : EOU Unit) : I2F_EOU (fun _ _ ↦ True) m m := by
  cases m with
  | raise_ret v => exact I2F_EOU_ret v v trivial
  | raise_ub s => exact I2F_EOU_ub s _
  | raise_oom s => exact I2F_EOU_oom _ s
  | raise_error s => exact I2F_EOU_error s s

private theorem nullTest {p q} (h : I2F_Addr p q) :
    (PInf.P2I.ptr_to_int p == PInf.P2I.ptr_to_int PInf.PTR.null) =
    (PFin.P2I.ptr_to_int q == PFin.P2I.ptr_to_int PFin.PTR.null) := by
  rw [show PInf.P2I.ptr_to_int p = PFin.P2I.ptr_to_int q from h.1]
  rfl

theorem I2F_assert_aligned_to {a1 a2} (align : Option int_syntax) (msg : IRString)
    (h : I2F_dvalue a1 a2) : I2F_EOU (fun _ _ ↦ True)
      (@assert_aligned_to PInf a1 align msg) (@assert_aligned_to PFin a2 align msg) := by
  cases h with
  | I2F_dvalue_Base hb =>
    cases hb <;> try exact unitRefl _
    rename_i p q hp
    cases align with
    | none => exact unitRefl _
    | some al =>
      simp only [assert_aligned_to, I2F_Addr_ptr_aligned_to p q _ hp]
      exact unitRefl _
  | _ => exact unitRefl _

theorem I2F_assert_alignment {a1 a2} (anns : List (annotation dtyp)) (msg : IRString)
    (h : I2F_dvalue a1 a2) : I2F_EOU (fun _ _ ↦ True)
      (@assert_alignment PInf a1 anns msg) (@assert_alignment PFin a2 anns msg) :=
  I2F_assert_aligned_to _ msg h

theorem I2F_value_attr_nonnull (attrs : List param_attr) {x y} (h : I2F_dvalue x y) :
    I2F_dvalue (@value_attr_nonnull PInf attrs x) (@value_attr_nonnull PFin attrs y) := by
  have keep := h
  cases h with
  | I2F_dvalue_Base hb =>
    cases hb <;> try exact keep
    rename_i p q hp
    simp only [value_attr_nonnull, nullTest hp]
    split <;> first | exact keep | exact I2F_dvalue_Base I2F_dvalue_Poison
  | _ => exact keep

theorem I2F_value_attr_align (attrs : List param_attr) {x y} (h : I2F_dvalue x y) :
    I2F_dvalue (@value_attr_align PInf attrs x) (@value_attr_align PFin attrs y) := by
  have keep := h
  cases h with
  | I2F_dvalue_Base hb =>
    cases hb <;> try exact keep
    rename_i p q hp
    cases ha : attrs.findSome? attr_align with
    | none => simpa only [value_attr_align, ha] using keep
    | some al =>
      simp only [value_attr_align, ha, I2F_Addr_ptr_aligned_to p q _ hp]
      split <;> first | exact keep | exact I2F_dvalue_Base I2F_dvalue_Poison
  | _ => exact keep

theorem I2F_value_attr_range (attrs : List param_attr) {x y} (h : I2F_dvalue x y) :
    I2F_dvalue (@value_attr_range PInf attrs x) (@value_attr_range PFin attrs y) := by
  have keep := h
  cases h with
  | I2F_dvalue_Base hb =>
    cases hb <;> try exact keep
    cases hr : attrs.findSome? attr_range with
    | none => simpa only [value_attr_range, hr] using keep
    | some r =>
      obtain ⟨lo, hi⟩ := r
      simp only [value_attr_range, hr]
      split <;> first | exact keep | exact I2F_dvalue_Base I2F_dvalue_Poison
  | _ => exact keep

theorem I2F_fp_class {b c} (h : I2F_dvalue_base b c) : @fp_class PInf b = @fp_class PFin c := by
  cases h <;> rfl

theorem I2F_value_nofpclass (mask : Int) (dt : dtyp) {x y} (h : I2F_dvalue x y) :
    I2F_dvalue (@value_nofpclass PInf mask dt x) (@value_nofpclass PFin mask dt y) := by
  revert dt
  apply I2F_dvalue_ind (P := fun a b ↦ ∀ t,
    I2F_dvalue (@value_nofpclass PInf mask t a) (@value_nofpclass PFin mask t b)) _ _ _ h
  · intro b c hb t
    simp only [value_nofpclass, I2F_fp_class hb]
    cases @fp_class PFin c with
    | none => exact I2F_dvalue_Base hb
    | some cls =>
      dsimp only
      split <;> first | exact I2F_dvalue_Base hb | exact I2F_dvalue_Base I2F_dvalue_Poison
  · intro packed xs ys hs ih t
    cases t with
    | DTYPE_Struct p ts =>
      apply I2F_canonicalize_agg
      induction hs generalizing ts with
      | nil => cases ts <;> exact .nil
      | cons hr hrs ind =>
        cases ih with
        | cons hx hxs =>
          cases ts with
          | nil => exact .cons hr hrs
          | cons u us => exact .cons (hx u) (ind hxs us)
    | _ => exact I2F_dvalue_Struct packed hs
  · intro vector xs ys hs ih t
    cases t with
    | DTYPE_Array v n u =>
      apply I2F_canonicalize_agg
      clear hs
      induction ih with
      | nil => exact .nil
      | cons hx _ ind => exact .cons (hx u) ind
    | _ => exact I2F_dvalue_Array vector hs

theorem I2F_value_attr_nofpclass (attrs : List param_attr) (dt : dtyp) {x y} (h : I2F_dvalue x y) :
    I2F_dvalue (@value_attr_nofpclass PInf attrs dt x) (@value_attr_nofpclass PFin attrs dt y) := by
  unfold value_attr_nofpclass
  cases attrs.findSome? attr_nofpclass with
  | none => exact h
  | some m => exact I2F_value_nofpclass m dt h

theorem I2F_value_attrs_poison (attrs : List param_attr) (dt : dtyp) {x y} (h : I2F_dvalue x y) :
    I2F_dvalue (@value_attrs_poison PInf attrs dt x) (@value_attrs_poison PFin attrs dt y) :=
  I2F_value_attr_nofpclass attrs dt
    (I2F_value_attr_range attrs (I2F_value_attr_align attrs (I2F_value_attr_nonnull attrs h)))

theorem I2F_apply_value_attrs (attrs : List param_attr) (msg : IRString) (dt : dtyp) {x y}
    (h : I2F_dvalue x y) : I2F_EOU I2F_dvalue
      (@apply_value_attrs PInf attrs msg dt x) (@apply_value_attrs PFin attrs msg dt y) := by
  have hp := I2F_value_attrs_poison attrs dt h
  simp only [apply_value_attrs, I2F_dvalue_well_defined hp]
  split
  · exact I2F_EOU_ub _ _
  · exact I2F_EOU_ret _ _ hp

theorem I2F_value_metadata_range_base (rs : List (int_syntax × int_syntax)) {x y}
    (h : I2F_dvalue x y) :
    I2F_dvalue (@value_metadata_range_base PInf rs x) (@value_metadata_range_base PFin rs y) := by
  have keep := h
  cases h with
  | I2F_dvalue_Base hb =>
    cases hb <;> try exact keep
    simp only [value_metadata_range_base]
    split <;> first | exact keep | exact I2F_dvalue_Base I2F_dvalue_Poison
  | _ => exact keep

theorem I2F_value_metadata_range (r : Option (List (int_syntax × int_syntax))) (dt : dtyp)
    {x y} (h : I2F_dvalue x y) :
    I2F_dvalue (@value_metadata_range PInf r dt x) (@value_metadata_range PFin r dt y) := by
  cases r with
  | none => exact h
  | some rs =>
    have hb := I2F_value_metadata_range_base rs h
    cases h with
    | I2F_dvalue_Array v hs =>
      cases v with
      | false => exact hb
      | true =>
        apply I2F_canonicalize_agg
        clear hb
        induction hs with
        | nil => exact .nil
        | cons hr _ ih => exact .cons (I2F_value_metadata_range_base rs hr) ih
    | _ => exact hb

theorem I2F_forallb_well_defined {xs ys} (h : List.Forall₂ I2F_dvalue xs ys) :
    xs.all (@dvalue_well_defined PInf) = ys.all (@dvalue_well_defined PFin) := by
  induction h with
  | nil => rfl
  | cons hv _ ih => exact congrArg₂ Bool.and (I2F_dvalue_well_defined hv) ih

theorem I2F_check_call_result (fattrs : List fn_attr) (msg : IRString) {xs ys r1 r2}
    (ha : List.Forall₂ I2F_dvalue xs ys) (hr : Sum.LiftRel I2F_dvalue I2F_dvalue r1 r2) :
    I2F_EOU (fun _ _ ↦ True) (@check_call_result PInf fattrs msg xs r1)
      (@check_call_result PFin fattrs msg ys r2) := by
  cases hr with
  | inl => exact unitRefl _
  | inr hv =>
    simp only [check_call_result, I2F_forallb_well_defined ha, I2F_dvalue_well_defined hv]
    exact unitRefl _

theorem I2F_check_callee {x y} (h : I2F_dvalue x y) :
    I2F_EOU (fun _ _ ↦ True) (@check_callee PInf x) (@check_callee PFin y) := by
  cases h with
  | I2F_dvalue_Base hb =>
    cases hb <;> try exact unitRefl _
    rename_i p q hp
    simp only [check_callee, nullTest hp]
    exact unitRefl _
  | _ => exact unitRefl _

theorem I2F_dvalue_ptr_address {x y} (h : I2F_dvalue x y) :
    @dvalue_ptr_address PInf x = @dvalue_ptr_address PFin y := by
  cases h with
  | I2F_dvalue_Base hb =>
    cases hb <;> try rfl
    rename_i hp
    exact congrArg some (show PInf.P2I.ptr_to_int _ = PFin.P2I.ptr_to_int _ from hp.1)
  | _ => rfl

theorem I2F_bundle_uint {x y} (h : I2F_dvalue x y) : @bundle_uint PInf x = @bundle_uint PFin y := by
  cases h with
  | I2F_dvalue_Base hb => cases hb <;> rfl
  | _ => rfl

theorem I2F_bundle_sint {x y} (h : I2F_dvalue x y) : @bundle_sint PInf x = @bundle_sint PFin y := by
  cases h with
  | I2F_dvalue_Base hb => cases hb <;> rfl
  | _ => rfl

end Vellvm.Theory.I2F.I2F_attributes
