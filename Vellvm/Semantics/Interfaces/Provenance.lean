module

public import Vellvm.Numeric.Rocqlib

@[expose] public section
namespace Vellvm.Semantics.Interfaces.Provenance
open Numeric.Rocqlib

/-- Provenance names, allocation IDs on bytes, and the access rights attached to pointers. -/
class Provenance where
  Build_Provenance ::
  provenance : Type
  allocationId : Type
  prov : Type
  wildcard_prov : prov
  nil_prov : prov
  access_allowed : prov → allocationId → Bool
  aid_access_allowed : allocationId → allocationId → Bool
  allocation_id_to_prov : allocationId → prov
  provenance_to_allocation_id : provenance → allocationId
  provenance_to_prov : provenance → prov
  initial_provenance : provenance
  next_provenance : provenance → provenance
  eq_dec_provenance : EqDecision provenance
  eq_dec_aid : EqDecision allocationId
  provenance_lt : provenance → provenance → Prop
  show_prov : prov → IRString
  show_provenance : provenance → IRString
  show_allocation_id : allocationId → IRString

export Provenance (Build_Provenance provenance allocationId prov wildcard_prov nil_prov
  access_allowed aid_access_allowed allocation_id_to_prov provenance_to_allocation_id
  provenance_to_prov initial_provenance next_provenance eq_dec_provenance eq_dec_aid
  provenance_lt show_prov show_provenance show_allocation_id)

class ProvenanceTheory [P : Provenance] : Prop where
  Build_ProvenanceTheory ::
  aid_access_allowed_refl (aid : P.allocationId) : P.aid_access_allowed aid aid = true
  access_allowed_refl (aid : P.allocationId) : P.access_allowed (P.allocation_id_to_prov aid) aid = true
  allocation_id_to_prov_inv (aid aid' : P.allocationId) :
    P.allocation_id_to_prov aid = P.allocation_id_to_prov aid' → aid = aid'
  provenance_to_allocation_id_inv (pr pr' : P.provenance) :
    P.provenance_to_allocation_id pr = P.provenance_to_allocation_id pr' → pr = pr'
  allocation_id_to_prov_provenance_to_allocation_id (pr : P.provenance) :
    P.allocation_id_to_prov (P.provenance_to_allocation_id pr) = P.provenance_to_prov pr
  provenance_eq_dec_refl (pr : P.provenance) : true = proj_sumbool (P.eq_dec_provenance pr pr)
  aid_eq_dec_refl (aid : P.allocationId) : true = proj_sumbool (P.eq_dec_aid aid aid)
  access_allowed_Proper (p q : P.prov) : p = q → ∀ a b : P.allocationId,
    true = proj_sumbool (P.eq_dec_aid a b) → P.access_allowed p a = P.access_allowed q b
  provenance_lt_trans {x y z : P.provenance} : P.provenance_lt x y → P.provenance_lt y z →
    P.provenance_lt x z
  provenance_lt_next_provenance (pr : P.provenance) : P.provenance_lt pr (P.next_provenance pr)
  provenance_lt_nrefl (pr : P.provenance) : ¬ P.provenance_lt pr pr
  provenance_lt_antisym {x y : P.provenance} : P.provenance_lt x y → P.provenance_lt y x → x = y
  next_provenance_neq {pr : P.provenance} : pr ≠ P.next_provenance pr

export ProvenanceTheory (Build_ProvenanceTheory aid_access_allowed_refl access_allowed_refl
  allocation_id_to_prov_inv provenance_to_allocation_id_inv
  allocation_id_to_prov_provenance_to_allocation_id provenance_eq_dec_refl aid_eq_dec_refl
  access_allowed_Proper provenance_lt_trans provenance_lt_next_provenance provenance_lt_nrefl
  provenance_lt_antisym next_provenance_neq)

end Vellvm.Semantics.Interfaces.Provenance
