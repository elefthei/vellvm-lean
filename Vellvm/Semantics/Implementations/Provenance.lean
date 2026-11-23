module

public import Vellvm.Semantics.Interfaces.Provenance
public import Vellvm.Syntax.ShowAST

@[expose] public section
namespace Vellvm.Semantics.Implementations.Provenance
open Numeric.Rocqlib Utils.StringUtil Interfaces.Provenance

def eq_dec_option {A : Type u} (dec : EqDecision A) : EqDecision (Option A) := option_eq dec

instance ProvenanceV : Provenance where
  provenance := Nat
  allocationId := Option Nat
  prov := Option (List Nat)
  wildcard_prov := none
  nil_prov := some []
  access_allowed
    | some ps, some a => ps.any (a == ·)
    | _, _ => true
  aid_access_allowed
    | some a, some b => a == b
    | _, _ => true
  allocation_id_to_prov := Option.map (fun a ↦ [a])
  provenance_to_allocation_id := some
  provenance_to_prov p := some [p]
  initial_provenance := 0
  next_provenance := Nat.succ
  eq_dec_provenance a b := decideSum (a = b)
  eq_dec_aid := eq_dec_option (fun a b ↦ decideSum (a = b))
  provenance_lt := Nat.lt
  -- Extraction selects DShowList here, not the bracketed StringUtil.showList.
  show_prov := (@showOpt (List Nat) (@Syntax.ShowAST.DShowShow _
    (@Syntax.ShowAST.DShowList Nat Syntax.ShowAST.DShow_N))).«show»
  show_provenance := show_N
  show_allocation_id := «show»

instance ProvenanceVTheory : @ProvenanceTheory ProvenanceV where
  aid_access_allowed_refl aid := by cases aid <;> simp [aid_access_allowed]
  access_allowed_refl aid := by cases aid <;> simp [access_allowed, allocation_id_to_prov]
  allocation_id_to_prov_inv a b := by
    cases a <;> cases b <;> simp [allocation_id_to_prov] <;> rintro ⟨⟩ <;> rfl
  provenance_to_allocation_id_inv _ _ := Option.some.inj
  allocation_id_to_prov_provenance_to_allocation_id _ := rfl
  provenance_eq_dec_refl _ := (proj_sumbool_is_true _ rfl).symm
  aid_eq_dec_refl _ := (proj_sumbool_is_true _ rfl).symm
  access_allowed_Proper := by
    rintro p _ rfl a b h
    cases proj_sumbool_true _ h.symm
    rfl
  provenance_lt_trans := Nat.lt_trans
  provenance_lt_next_provenance := Nat.lt_succ_self
  provenance_lt_nrefl := Nat.lt_irrefl
  provenance_lt_antisym h₁ h₂ := (Nat.lt_asymm h₁ h₂).elim
  next_provenance_neq := Nat.ne_of_lt (Nat.lt_succ_self _)

end Vellvm.Semantics.Implementations.Provenance
