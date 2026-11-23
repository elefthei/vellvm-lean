module

public import Vellvm.Semantics.DynamicValues.Canonical
public import Vellvm.Syntax.ShowAST

@[expose] public section

namespace Vellvm.Semantics.DynamicValues
open Interfaces.Params Syntax.DynamicTypes Utils.ListUtil EOU

variable [Pa : Params]

def default_dvalue_of_dtyp_i (sz : Positive) : dvalue_base :=
  DVALUE_I sz (Numeric.Integers.repr 0)

def default_dvalue_base_of_dtyp_base : dtyp_base → EOU dvalue_base
  | .DTYPE_I sz => .raise_ret (default_dvalue_of_dtyp_i sz)
  | .DTYPE_Iptr => .raise_ret (DVALUE_Iptr Pa.IPTR.zero_iptr)
  | .DTYPE_Pointer => .raise_ret (DVALUE_Pointer Pa.PTR.null)
  | .DTYPE_Void => .raise_error "DTYPE_Void is not a true LLVM value".toUTF8
  | .DTYPE_FP .FP_float => .raise_ret (DVALUE_Float (.B754_zero false))
  | .DTYPE_FP .FP_double => .raise_ret (DVALUE_Double (.B754_zero false))
  | .DTYPE_FP fp => .raise_error ("Unimplemented default type: floating point ".toUTF8 ++
      Syntax.ShowAST.show_floating_point_variant fp)
  | .DTYPE_Label => .raise_error "Unimplemented default type: label".toUTF8
  | .DTYPE_Token => .raise_error "Unimplemented default type: token".toUTF8
  | .DTYPE_Metadata => .raise_error "Unimplemented default type: metadata".toUTF8
  | .DTYPE_X86_mmx => .raise_error "Unimplemented default type: x86_mmx".toUTF8
  | .DTYPE_Opaque => .raise_error "Unimplemented default type: opaque".toUTF8
  | .DTYPE_B sz => .raise_ret (DVALUE_B sz (BYTE_I Numeric.Integers.zero))

def default_dvalue_of_dtyp : dtyp → EOU dvalue
  | .DTYPE_Base t => do return DVALUE_Base (← default_dvalue_base_of_dtyp_base t)
  | .DTYPE_Struct p ts => do return DVALUE_Struct p (← fields ts)
  | .DTYPE_Array v n t => do
    let x ← default_dvalue_of_dtyp t
    return DVALUE_Array v (repeat_acc x (N_to_nat_safe n))
where
  fields : List dtyp → EOU (List dvalue)
    | [] => .raise_ret []
    | t :: ts => do return (← default_dvalue_of_dtyp t) :: (← fields ts)

theorem default_fields_eq_map (ts : List dtyp) :
    default_dvalue_of_dtyp.fields ts = map_monad default_dvalue_of_dtyp ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [default_dvalue_of_dtyp.fields, map_monad, ih]

theorem dvalue_default_base_NO_VOID (t : dtyp_base) {v : dvalue_base} :
    default_dvalue_base_of_dtyp_base t = raise_ret v → NO_VOID_base t := by
  cases t <;> intro h <;> trivial

theorem dvalue_default_NO_VOID (t : dtyp) {v : dvalue} :
    default_dvalue_of_dtyp t = raise_ret v → NO_VOID t := by
  induction t using dtyp_ind generalizing v with
  | base t =>
    intro h
    rw [default_dvalue_of_dtyp] at h
    obtain ⟨b, hb, _⟩ := EOU_bind_ret_inv _ _ _ h
    simpa only [NO_VOID] using dvalue_default_base_NO_VOID t hb
  | struct p ts ih =>
    intro h
    rw [default_dvalue_of_dtyp, default_fields_eq_map] at h
    obtain ⟨xs, hxs, _⟩ := EOU_bind_ret_inv _ _ _ h
    rw [NO_VOID]
    change FORALL NO_VOID ts
    apply (FORALL_forall _ _).mpr
    apply List.forall_iff_forall_mem.mpr
    intro t ht
    obtain ⟨x, hx⟩ := map_monad_EOU_success _ _ _ _ _ hxs t ht
    exact ih t ht hx
  | array v n t ih =>
    intro h
    rw [default_dvalue_of_dtyp] at h
    obtain ⟨x, hx, _⟩ := EOU_bind_ret_inv _ _ _ h
    simpa only [NO_VOID] using ih hx

private theorem defined_not_poison (x : dvalue) (hx : dvalue_well_defined x = true) :
    dvalue_is_poison x = false := by
  cases hp : dvalue_is_poison x with
  | false => rfl
  | true =>
    obtain rfl := dvalue_is_poison_true x hp
    simp [dvalue_well_defined, dvalue_base_well_defined] at hx

private theorem default_base_canonical_defined (t : dtyp_base) (b : dvalue_base)
    (h : default_dvalue_base_of_dtyp_base t = raise_ret b) :
    dvalue_is_canonical (DTYPE_Base t) (DVALUE_Base b) = true ∧
    dvalue_well_defined (DVALUE_Base b) = true := by
  cases t
  case' DTYPE_FP fp => cases fp
  all_goals simp [default_dvalue_base_of_dtyp_base] at h
  all_goals subst b
  all_goals
    simp [default_dvalue_of_dtyp_i, dvalue_is_canonical, dvalue_base_has_dtyp_base,
      dvalue_base_canonical, dvalue_bv_canonical, dvalue_well_defined, dvalue_base_well_defined]

private theorem default_fields_canonical_defined {ts : List dtyp} {xs : List dvalue}
    (rel : List.Forall₂ (fun t x ↦ default_dvalue_of_dtyp t = raise_ret x) ts xs)
    (onField : ∀ t ∈ ts, ∀ x, default_dvalue_of_dtyp t = raise_ret x →
      dvalue_is_canonical t x = true ∧ dvalue_well_defined x = true) :
    fields_canonical ts xs = true ∧ xs.all dvalue_well_defined = true ∧
    fields_all_poison ts xs = ts.all dtyp_is_empty := by
  induction rel with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | @cons t x ts xs h _ ih =>
    obtain ⟨hc, hw⟩ := onField t (by simp) x h
    obtain ⟨hcs, hws, hp⟩ := ih (fun u hu ↦ onField u (List.mem_cons_of_mem _ hu))
    simp [fields_canonical, fields_all_poison, hc, hw, hcs, hws, hp, defined_not_poison x hw]

theorem default_success_canonical_defined (t : dtyp) (v : dvalue) :
    default_dvalue_of_dtyp t = raise_ret v →
    dvalue_is_canonical t v = true ∧ dvalue_well_defined v = true := by
  induction t using dtyp_ind generalizing v with
  | base t =>
    intro h
    rw [default_dvalue_of_dtyp] at h
    obtain ⟨b, hb, he⟩ := EOU_bind_ret_inv _ _ _ h
    change raise_ret (DVALUE_Base b) = raise_ret v at he
    cases he
    exact default_base_canonical_defined t b hb
  | struct p ts ih =>
    intro h
    rw [default_dvalue_of_dtyp, default_fields_eq_map] at h
    obtain ⟨xs, hxs, he⟩ := EOU_bind_ret_inv _ _ _ h
    change raise_ret (DVALUE_Struct p xs) = raise_ret v at he
    cases he
    obtain ⟨hc, hw, hp⟩ := default_fields_canonical_defined
      ((map_monad_EOU_Forall2 _ _ _).mp hxs) ih
    rw [dvalue_is_canonical_struct, dvalue_well_defined]
    simp [agg_is_poison, dtyp_is_empty, hp, hc, hw]
  | array vec n t ih =>
    intro h
    rw [default_dvalue_of_dtyp] at h
    obtain ⟨x, hx, he⟩ := EOU_bind_ret_inv _ _ _ h
    change raise_ret (DVALUE_Array vec (repeat_acc x (N_to_nat_safe n))) = raise_ret v at he
    cases he
    obtain ⟨hc, hw⟩ := ih x hx
    have hnv := dvalue_default_NO_VOID t hx
    rw [N_to_nat_safe_eq, repeat_acc_eq, dvalue_is_canonical, dvalue_well_defined]
    cases n <;> simp [agg_is_poison, dtyp_is_empty, List.all_replicate, hnv, hc, hw,
      defined_not_poison x hw]

end Vellvm.Semantics.DynamicValues
