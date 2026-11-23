import PortChecks.SourceType
import Vellvm.Semantics.Interfaces.Provenance

open Vellvm Vellvm.Numeric.Rocqlib Vellvm.Semantics.Interfaces.Provenance

#source_check "src/rocq/Semantics/Interfaces/Provenance.v|Vellvm.Semantics.Interfaces.Provenance|aid_access_allowed_refl"
  aid_access_allowed_refl : ∀ [P : Provenance] [@ProvenanceTheory P] (aid : P.allocationId),
    P.aid_access_allowed aid aid = true
#source_check "src/rocq/Semantics/Interfaces/Provenance.v|Vellvm.Semantics.Interfaces.Provenance|access_allowed_refl"
  access_allowed_refl : ∀ [P : Provenance] [@ProvenanceTheory P] (aid : P.allocationId),
    P.access_allowed (P.allocation_id_to_prov aid) aid = true
#source_check "src/rocq/Semantics/Interfaces/Provenance.v|Vellvm.Semantics.Interfaces.Provenance|allocation_id_to_prov_inv"
  allocation_id_to_prov_inv : ∀ [P : Provenance] [@ProvenanceTheory P] (a b : P.allocationId),
    P.allocation_id_to_prov a = P.allocation_id_to_prov b → a = b
#source_check "src/rocq/Semantics/Interfaces/Provenance.v|Vellvm.Semantics.Interfaces.Provenance|provenance_to_allocation_id_inv"
  provenance_to_allocation_id_inv : ∀ [P : Provenance] [@ProvenanceTheory P] (a b : P.provenance),
    P.provenance_to_allocation_id a = P.provenance_to_allocation_id b → a = b
#source_check "src/rocq/Semantics/Interfaces/Provenance.v|Vellvm.Semantics.Interfaces.Provenance|allocation_id_to_prov_provenance_to_allocation_id"
  allocation_id_to_prov_provenance_to_allocation_id : ∀ [P : Provenance] [@ProvenanceTheory P] (pr : P.provenance),
    P.allocation_id_to_prov (P.provenance_to_allocation_id pr) = P.provenance_to_prov pr
#source_check "src/rocq/Semantics/Interfaces/Provenance.v|Vellvm.Semantics.Interfaces.Provenance|provenance_eq_dec_refl"
  provenance_eq_dec_refl : ∀ [P : Provenance] [@ProvenanceTheory P] (pr : P.provenance),
    true = proj_sumbool (P.eq_dec_provenance pr pr)
#source_check "src/rocq/Semantics/Interfaces/Provenance.v|Vellvm.Semantics.Interfaces.Provenance|aid_eq_dec_refl"
  aid_eq_dec_refl : ∀ [P : Provenance] [@ProvenanceTheory P] (aid : P.allocationId),
    true = proj_sumbool (P.eq_dec_aid aid aid)
#source_check "src/rocq/Semantics/Interfaces/Provenance.v|Vellvm.Semantics.Interfaces.Provenance|access_allowed_Proper"
  access_allowed_Proper : ∀ [P : Provenance] [@ProvenanceTheory P] (x y : P.prov), x = y →
    ∀ a b : P.allocationId, true = proj_sumbool (P.eq_dec_aid a b) →
      P.access_allowed x a = P.access_allowed y b
#source_check "src/rocq/Semantics/Interfaces/Provenance.v|Vellvm.Semantics.Interfaces.Provenance|provenance_lt_trans"
  provenance_lt_trans : ∀ [P : Provenance] [@ProvenanceTheory P] {x y z : P.provenance},
    P.provenance_lt x y → P.provenance_lt y z → P.provenance_lt x z
#source_check "src/rocq/Semantics/Interfaces/Provenance.v|Vellvm.Semantics.Interfaces.Provenance|provenance_lt_next_provenance"
  provenance_lt_next_provenance : ∀ [P : Provenance] [@ProvenanceTheory P] (pr : P.provenance),
    P.provenance_lt pr (P.next_provenance pr)
#source_check "src/rocq/Semantics/Interfaces/Provenance.v|Vellvm.Semantics.Interfaces.Provenance|provenance_lt_nrefl"
  provenance_lt_nrefl : ∀ [P : Provenance] [@ProvenanceTheory P] (pr : P.provenance),
    ¬ P.provenance_lt pr pr
#source_check "src/rocq/Semantics/Interfaces/Provenance.v|Vellvm.Semantics.Interfaces.Provenance|provenance_lt_antisym"
  provenance_lt_antisym : ∀ [P : Provenance] [@ProvenanceTheory P] {x y : P.provenance},
    P.provenance_lt x y → P.provenance_lt y x → x = y
#source_check "src/rocq/Semantics/Interfaces/Provenance.v|Vellvm.Semantics.Interfaces.Provenance|next_provenance_neq"
  next_provenance_neq : ∀ [P : Provenance] [@ProvenanceTheory P] {pr : P.provenance},
    pr ≠ P.next_provenance pr
