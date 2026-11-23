module

public import Vellvm.Semantics.DynamicValues.Default

@[expose] public section
namespace Vellvm.Semantics.DynamicValues
open Interfaces.Params Syntax.DynamicTypes Utils.ListUtil EOU

variable [Pa : Params]

/-- Includes pointer fragments: a single pointer bit still carries that pointer's provenance. -/
def allPointers (P : Pa.PTR.ptr → Prop) (v : dvalue) : Prop :=
  match v with
  | .DVALUE_Base (.DVALUE_Pointer p) | .DVALUE_Base (.DVALUE_B _ (.BYTE_Pointer p _)) => P p
  | .DVALUE_Base (.DVALUE_B _ (.BYTE_Mixed bits)) => ∀ b ∈ bits, match b with
      | .Bit_ptr p _ => P p
      | _ => True
  | .DVALUE_Base _ => True
  | .DVALUE_Struct _ vs | .DVALUE_Array _ vs => ∀ x ∈ vs, allPointers P x
termination_by sizeOf v
decreasing_by all_goals decreasing_tactic

private theorem forall_right_of_related {A B : Type} {R : A → B → Prop} {P : B → Prop}
    {as : List A} {bs : List B} (h : List.Forall₂ R as bs)
    (each : ∀ a ∈ as, ∀ b, R a b → P b) : ∀ b ∈ bs, P b := by
  induction h with
  | nil => simp
  | cons h _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact each _ (by simp) _ h
    · exact ih (fun a ha ↦ each a (List.mem_cons_of_mem _ ha)) _ hb

/-- No abstract law about the provenance of null is needed: the caller supplies its property. -/
theorem default_valid_pointers (P : Pa.PTR.ptr → Prop) (hn : P Pa.PTR.null) (t : dtyp) (v : dvalue)
    (h : default_dvalue_of_dtyp t = raise_ret v) : allPointers P v := by
  induction t using dtyp_ind generalizing v with
  | base t =>
    rw [default_dvalue_of_dtyp] at h
    obtain ⟨b, hb, hv⟩ := EOU_bind_ret_inv _ _ _ h
    change raise_ret (DVALUE_Base b) = raise_ret v at hv
    cases hv
    cases t
    case' DTYPE_FP fp => cases fp
    all_goals simp [default_dvalue_base_of_dtyp_base] at hb
    all_goals subst b; simp [allPointers, default_dvalue_of_dtyp_i, hn]
  | struct p ts ih =>
    rw [default_dvalue_of_dtyp, default_fields_eq_map] at h
    obtain ⟨xs, hxs, hv⟩ := EOU_bind_ret_inv _ _ _ h
    change raise_ret (DVALUE_Struct p xs) = raise_ret v at hv
    cases hv
    rw [allPointers]
    exact forall_right_of_related ((map_monad_EOU_Forall2 _ _ _).mp hxs) ih
  | array vec n t ih =>
    rw [default_dvalue_of_dtyp] at h
    obtain ⟨x, hx, hv⟩ := EOU_bind_ret_inv _ _ _ h
    change raise_ret (DVALUE_Array vec (repeat_acc x (N_to_nat_safe n))) = raise_ret v at hv
    cases hv
    rw [allPointers, repeat_acc_eq]
    intro y hy
    obtain rfl := List.eq_of_mem_replicate hy
    exact ih _ hx

end Vellvm.Semantics.DynamicValues
