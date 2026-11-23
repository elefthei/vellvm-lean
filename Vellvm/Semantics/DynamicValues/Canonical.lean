module

public import Vellvm.Semantics.DynamicValues.Core

@[expose] public section
namespace Vellvm.Semantics.DynamicValues
open Interfaces.Params Syntax.DynamicTypes Numeric.Integers

variable [Pa : Params]

/-- Empty types have no scalar leaves, including arrays of length zero. -/
def dtyp_is_empty : dtyp → Bool
  | .DTYPE_Base _ => false
  | .DTYPE_Struct _ fields => fields.all dtyp_is_empty
  | .DTYPE_Array _ sz t => (sz == 0) || dtyp_is_empty t

def empty_dvalue_of_dtyp : dtyp → dvalue
  | .DTYPE_Base _ => DVALUE_Base DVALUE_Poison
  | .DTYPE_Struct p fields => DVALUE_Struct p (fields.map empty_dvalue_of_dtyp)
  | .DTYPE_Array v sz t => DVALUE_Array v (List.replicate sz (empty_dvalue_of_dtyp t))

def poison_of_dtyp (dt : dtyp) : dvalue :=
  if dtyp_is_empty dt then empty_dvalue_of_dtyp dt else DVALUE_Base DVALUE_Poison

def fields_all_poison : List dtyp → List dvalue → Bool
  | [], [] => true
  | t :: ts, v :: vs => (dtyp_is_empty t || dvalue_is_poison v) && fields_all_poison ts vs
  | _, _ => false

def agg_is_poison (dt : dtyp) (vs : List dvalue) : Bool :=
  !dtyp_is_empty dt && match dt with
    | .DTYPE_Struct _ dts => fields_all_poison dts vs
    | .DTYPE_Array _ _ _ => vs.all dvalue_is_poison
    | .DTYPE_Base _ => true

def canonicalize_agg (dt : dtyp) (vs : List dvalue) : dvalue :=
  if agg_is_poison dt vs then DVALUE_Base DVALUE_Poison
  else match dt with
    | .DTYPE_Struct p _ => DVALUE_Struct p vs
    | .DTYPE_Array v _ _ => DVALUE_Array v vs
    | .DTYPE_Base _ => DVALUE_Base DVALUE_Poison

mutual
  def dvalue_is_canonical (dt : dtyp) (dv : dvalue) : Bool :=
    match dv, dt with
    | .DVALUE_Base .DVALUE_Poison, _ => !dtyp_is_empty dt
    | .DVALUE_Base b, .DTYPE_Base tb => dvalue_base_has_dtyp_base b tb && dvalue_base_canonical b
    | .DVALUE_Struct p fields, .DTYPE_Struct q dts =>
        ((p == q) && !agg_is_poison dt fields) && fields_canonical dts fields
    | .DVALUE_Array v elts, .DTYPE_Array w sz t =>
        ((((v == w) && @decide (NO_VOID t) (NO_VOID_dec t)) && (elts.length == sz)) &&
          !agg_is_poison dt elts) && elts.all (dvalue_is_canonical t)
    | _, _ => false

  def fields_canonical (ts : List dtyp) (vs : List dvalue) : Bool :=
    match ts, vs with
    | [], [] => true
    | t :: ts, v :: vs => dvalue_is_canonical t v && fields_canonical ts vs
    | _, _ => false
end

def vector_elts (sz : Nat) : dvalue → Option (List dvalue)
  | .DVALUE_Array true elts => some elts
  | .DVALUE_Base .DVALUE_Poison => some (List.replicate sz (DVALUE_Base DVALUE_Poison))
  | _ => none

inductive dvalue_bv_has_sz {sz : Positive} : Positive → dvalue_bv sz → Prop where
  | BYTE_Pointer_sz (x : Pa.PTR.ptr) (idx : Nat) : dvalue_bv_has_sz sz (BYTE_Pointer x idx)
  | BYTE_Int_sz {sz' : Positive} (x : bit_int sz) : sz = sz' → dvalue_bv_has_sz sz' (BYTE_I x)
  | BYTE_Mixed_sz (bits : List memory_bit) {sz' : Positive} :
      bits.length = sz'.val → sz = sz' → dvalue_bv_has_sz sz' (BYTE_Mixed bits)
export dvalue_bv_has_sz (BYTE_Pointer_sz BYTE_Int_sz BYTE_Mixed_sz)

/-- The typing rules include the canonical representation invariant. -/
inductive dvalue_has_dtyp : dvalue → dtyp → Prop where
  | DVALUE_Base_typ (dv : dvalue_base) (t : dtyp_base) :
      dvalue_base_has_dtyp_base dv t = true → dvalue_base_canonical dv = true →
      dvalue_has_dtyp (DVALUE_Base dv) (DTYPE_Base t)
  | DVALUE_Poison_typ_agg (t : dtyp) : dtyp_is_empty t = false →
      dvalue_has_dtyp (DVALUE_Base DVALUE_Poison) t
  | DVALUE_Struct_typ (p : Bool) {fields : List dvalue} {dts : List dtyp} :
      agg_is_poison (DTYPE_Struct p dts) fields = false → List.Forall₂ dvalue_has_dtyp fields dts →
      dvalue_has_dtyp (DVALUE_Struct p fields) (DTYPE_Struct p dts)
  | DVALUE_Array_typ (v : Bool) {xs : List dvalue} (sz : Nat) {dt : dtyp} :
      NO_VOID dt → agg_is_poison (DTYPE_Array v sz dt) xs = false →
      (∀ x ∈ xs, dvalue_has_dtyp x dt) → xs.length = sz →
      dvalue_has_dtyp (DVALUE_Array v xs) (DTYPE_Array v sz dt)
export dvalue_has_dtyp (DVALUE_Base_typ DVALUE_Poison_typ_agg DVALUE_Struct_typ DVALUE_Array_typ)

theorem dvalue_is_canonical_struct (p : Bool) (fields : List dvalue) (q : Bool) (dts : List dtyp) :
    dvalue_is_canonical (DTYPE_Struct q dts) (DVALUE_Struct p fields) =
    (((p == q) && !agg_is_poison (DTYPE_Struct q dts) fields) && fields_canonical dts fields) := by
  rw [dvalue_is_canonical]

private theorem fields_canonical_iff (fields : List dvalue) (dts : List dtyp)
    (ih : ∀ x ∈ fields, ∀ t, dvalue_is_canonical t x = true ↔ dvalue_has_dtyp x t) :
    fields_canonical dts fields = true ↔ List.Forall₂ dvalue_has_dtyp fields dts := by
  induction fields generalizing dts with
  | nil => cases dts <;> simp [fields_canonical]
  | cons x xs tail =>
    cases dts with
    | nil => simp [fields_canonical]
    | cons t ts =>
      rw [fields_canonical, Bool.and_eq_true, List.forall₂_cons, ih x (by simp) t,
        tail ts (fun y hy ↦ ih y (by simp [hy]))]

theorem dvalue_is_canonical_iff (dv : dvalue) (dt : dtyp) :
    dvalue_is_canonical dt dv = true ↔ dvalue_has_dtyp dv dt := by
  refine dvalue_ind (fun x ↦ ∀ t, dvalue_is_canonical t x = true ↔ dvalue_has_dtyp x t)
    ?_ ?_ ?_ dv dt
  · intro b t
    constructor
    · intro h
      cases b with
      | DVALUE_Poison => exact DVALUE_Poison_typ_agg t (by simpa [dvalue_is_canonical] using h)
      | _ =>
        cases t with
        | DTYPE_Base tb =>
          simp [dvalue_is_canonical] at h
          exact DVALUE_Base_typ _ _ h.1 h.2
        | _ => simp [dvalue_is_canonical] at h
    · intro h
      cases h with
      | DVALUE_Base_typ b _ hb hc => cases b <;> simp [dvalue_is_canonical, dtyp_is_empty, hb, hc]
      | DVALUE_Poison_typ_agg _ hne => simp [dvalue_is_canonical, hne]
  · intro p fields ih dt
    constructor
    · intro h
      cases dt with
      | DTYPE_Struct q ts =>
        rw [dvalue_is_canonical_struct] at h
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
        obtain ⟨⟨rfl, hnp⟩, hc⟩ := h
        exact DVALUE_Struct_typ p hnp ((fields_canonical_iff fields ts ih).mp hc)
      | _ => simp [dvalue_is_canonical] at h
    · intro h
      cases h with
      | DVALUE_Struct_typ _ hnp hall =>
        simp [dvalue_is_canonical_struct, hnp, (fields_canonical_iff _ _ ih).mpr hall]
  · intro v elts ih dt
    constructor
    · intro h
      cases dt with
      | DTYPE_Array w sz t =>
        simp only [dvalue_is_canonical, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
          Bool.not_eq_true', List.all_eq_true] at h
        obtain ⟨⟨⟨⟨rfl, hnv⟩, hlen⟩, hnp⟩, hall⟩ := h
        exact DVALUE_Array_typ v sz hnv hnp (fun x hx ↦ (ih x hx t).mp (hall x hx)) hlen
      | _ => simp [dvalue_is_canonical] at h
    · intro h
      cases h with
      | DVALUE_Array_typ _ _ hnv hnp hall hlen =>
        simpa [dvalue_is_canonical, hnv, hnp, hlen] using
          fun x hx ↦ (ih x hx _).mpr (hall x hx)

theorem dvalue_is_canonical_sound (dv : dvalue) (dt : dtyp) :
    dvalue_is_canonical dt dv = true → dvalue_has_dtyp dv dt :=
  (dvalue_is_canonical_iff dv dt).mp

theorem dvalue_is_canonical_complete {dv : dvalue} {dt : dtyp} :
    dvalue_has_dtyp dv dt → dvalue_is_canonical dt dv = true :=
  (dvalue_is_canonical_iff dv dt).mpr

end Vellvm.Semantics.DynamicValues
