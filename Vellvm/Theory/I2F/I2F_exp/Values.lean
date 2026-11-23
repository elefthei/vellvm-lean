module

public import Vellvm.Semantics.DynamicValues.Canonical
public import Vellvm.Theory.I2F.Refinement.EOU
public import Vellvm.Theory.I2F.Refinement.Values

@[expose] public section
namespace Vellvm.Theory.I2F.I2F_exp
open Refinement Semantics.DynamicValues Syntax.DynamicTypes
open Utils.ListUtil (Forall2_repeat)

theorem I2F_dvalue_to_dvalue_base {v w} (h : I2F_dvalue v w) :
    I2F_EOU I2F_dvalue_base (@dvalue_to_dvalue_base PInf v) (@dvalue_to_dvalue_base PFin w) := by
  cases h with
  | I2F_dvalue_Base hb => exact .I2F_EOU_ret _ _ hb
  | I2F_dvalue_Struct _ _ | I2F_dvalue_Array _ _ => exact .I2F_EOU_error _ _

theorem Forall2_map_Base {xs ys} (h : List.Forall₂ I2F_dvalue_base xs ys) :
    List.Forall₂ I2F_dvalue (xs.map (@DVALUE_Base PInf)) (ys.map (@DVALUE_Base PFin)) := by
  induction h with
  | nil => exact .nil
  | cons hb _ ih => exact .cons (.I2F_dvalue_Base hb) ih

theorem I2F_dvalue_is_poison {v w} (h : I2F_dvalue v w) :
    @dvalue_is_poison PInf v = @dvalue_is_poison PFin w := by
  cases h with
  | I2F_dvalue_Base hb => cases hb <;> rfl
  | I2F_dvalue_Struct _ _ | I2F_dvalue_Array _ _ => rfl

private theorem all_eq_of_related {p : α → Bool} {q : β → Bool} {xs ys}
    (h : List.Forall₂ (fun x y ↦ p x = q y) xs ys) : xs.all p = ys.all q := by
  induction h with
  | nil => rfl
  | cons heq _ ih => exact congrArg₂ Bool.and heq ih

theorem I2F_forallb_is_poison {xs ys} (h : List.Forall₂ I2F_dvalue xs ys) :
    xs.all (@dvalue_is_poison PInf) = ys.all (@dvalue_is_poison PFin) :=
  all_eq_of_related (h.imp fun _ _ hxy ↦ I2F_dvalue_is_poison hxy)

theorem I2F_fields_all_poison (ts : List dtyp) {xs ys} (h : List.Forall₂ I2F_dvalue xs ys) :
    @fields_all_poison PInf ts xs = @fields_all_poison PFin ts ys := by
  induction h generalizing ts with
  | nil => cases ts <;> rfl
  | cons hxy _ ih => cases ts <;> simp [fields_all_poison, I2F_dvalue_is_poison hxy, ih]

theorem I2F_agg_is_poison (t : dtyp) {xs ys} (h : List.Forall₂ I2F_dvalue xs ys) :
    @agg_is_poison PInf t xs = @agg_is_poison PFin t ys := by
  cases t <;> simp only [agg_is_poison, I2F_fields_all_poison _ h, I2F_forallb_is_poison h]

theorem I2F_canonicalize_agg (t : dtyp) {xs ys} (h : List.Forall₂ I2F_dvalue xs ys) :
    I2F_dvalue (@canonicalize_agg PInf t xs) (@canonicalize_agg PFin t ys) := by
  simp only [canonicalize_agg, I2F_agg_is_poison t h]
  split
  · exact .I2F_dvalue_Base .I2F_dvalue_Poison
  · cases t with
    | DTYPE_Base _ => exact .I2F_dvalue_Base .I2F_dvalue_Poison
    | DTYPE_Struct p _ => exact .I2F_dvalue_Struct p h
    | DTYPE_Array v _ _ => exact .I2F_dvalue_Array v h

theorem I2F_empty_dvalue_of_dtyp (t : dtyp) :
    I2F_dvalue (@empty_dvalue_of_dtyp PInf t) (@empty_dvalue_of_dtyp PFin t) := by
  induction t using dtyp_ind with
  | base _ =>
    simp only [empty_dvalue_of_dtyp]
    exact .I2F_dvalue_Base .I2F_dvalue_Poison
  | struct p ts ih =>
    simp only [empty_dvalue_of_dtyp]
    apply I2F_dvalue_Struct p
    simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same] using ih
  | array v n t ih =>
    simp only [empty_dvalue_of_dtyp]
    exact .I2F_dvalue_Array v (Forall2_repeat _ _ _ n ih)

theorem I2F_poison_of_dtyp (t : dtyp) :
    I2F_dvalue (@poison_of_dtyp PInf t) (@poison_of_dtyp PFin t) := by
  unfold poison_of_dtyp
  split
  · exact I2F_empty_dvalue_of_dtyp t
  · exact .I2F_dvalue_Base .I2F_dvalue_Poison

theorem I2F_vector_elts (n : Nat) {v w} (h : I2F_dvalue v w) :
    match @vector_elts PInf n v, @vector_elts PFin n w with
    | some xs, some ys => List.Forall₂ I2F_dvalue xs ys
    | none, none => True
    | _, _ => False := by
  cases h with
  | I2F_dvalue_Base hb =>
    cases hb <;> first | exact True.intro | exact Forall2_repeat _ _ _ n (.I2F_dvalue_Base .I2F_dvalue_Poison)
  | I2F_dvalue_Struct _ _ => trivial
  | I2F_dvalue_Array v hs => cases v <;> first | exact hs | trivial

private theorem any_poison_bit_eq {xs ys} (h : List.Forall₂ I2F_memory_bit xs ys) :
    xs.any (@is_poison_bit PInf) = ys.any (@is_poison_bit PFin) := by
  induction h with
  | nil => rfl
  | cons hb _ ih =>
    apply congrArg₂ Bool.or _ ih
    cases hb <;> rfl

theorem I2F_dvalue_well_defined {v w} (h : I2F_dvalue v w) :
    @dvalue_well_defined PInf v = @dvalue_well_defined PFin w := by
  apply I2F_dvalue_ind (P := fun x y ↦ @dvalue_well_defined PInf x = @dvalue_well_defined PFin y)
      _ _ _ h
  · intro b b' hb
    simp only [dvalue_well_defined]
    cases hb <;> try rfl
    case I2F_dvalue_B hbv =>
      cases hbv <;> try rfl
      case I2F_BYTE_Mixed bits => exact congrArg Bool.not (any_poison_bit_eq bits)
  · intro _ xs ys _ ih
    simpa only [dvalue_well_defined] using all_eq_of_related ih
  · intro _ xs ys _ ih
    simpa only [dvalue_well_defined] using all_eq_of_related ih

end Vellvm.Theory.I2F.I2F_exp
