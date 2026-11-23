import PortChecks.SourceType
import Vellvm.Syntax.RawIdMaps

open Vellvm Vellvm.Syntax.LLVMAst Vellvm.Syntax.RawIdMaps Vellvm.Numeric.Rocqlib
universe u v

#source_check "src/rocq/Syntax/RawIdMaps.v|Vellvm.Syntax.RawIdMaps|rmap"
  rmap : Type u → Type u

#source_check "src/rocq/Syntax/RawIdMaps.v|Vellvm.Syntax.RawIdMaps|Map_rmap"
  Map_rmap : ∀ {V : Type u}, Map raw_id V (rmap V)

#source_check "src/rocq/Syntax/RawIdMaps.v|Vellvm.Syntax.RawIdMaps|Maps_lookup_rid_lookup"
  Maps_lookup_rid_lookup : ∀ {V : Type u} (k : raw_id) (m : rmap V), Map.lookup k m = rid_lookup k m

#source_check "src/rocq/Syntax/RawIdMaps.v|Vellvm.Syntax.RawIdMaps|RM_Refine_empty"
  RM_Refine_empty : ∀ {α : Type u} {β : Type v} (R : α → β → Prop), RM_Refine R (RM.empty α) (RM.empty β)

#source_check "src/rocq/Syntax/RawIdMaps.v|Vellvm.Syntax.RawIdMaps|RM_Refine_add"
  RM_Refine_add : ∀ {α : Type u} {β : Type v} (R : α → β → Prop) (m₁ : rmap α) (m₂ : rmap β) k x y,
    RM_Refine R m₁ m₂ → R x y → RM_Refine R (RM.add k x m₁) (RM.add k y m₂)

#source_check "src/rocq/Syntax/RawIdMaps.v|Vellvm.Syntax.RawIdMaps|RM_Refine_lookup"
  RM_Refine_lookup : ∀ {α : Type u} {β : Type v} (R : α → β → Prop) (m : rmap α) (n : rmap β),
    RM_Refine R m n → ∀ k, option_rel R (rid_lookup k m) (rid_lookup k n)

#source_check "src/rocq/Syntax/RawIdMaps.v|Vellvm.Syntax.RawIdMaps|MapOk_rmap"
  MapOk_rmap : ∀ {V : Type u}, MapOk (· = ·) (@Map_rmap V)

-- Conflicting bindings select the left environment, including when the right one is nonempty.
example (k : raw_id) (x y : Nat) :
    rid_lookup k (Map.union (RM.add k x (RM.empty Nat)) (RM.add k y (RM.empty Nat))) = some x := by
  rw [show rid_lookup k (Map.union (RM.add k x (RM.empty Nat)) (RM.add k y (RM.empty Nat))) =
      (RM.find k (RM.add k x (RM.empty Nat))).or (RM.find k (RM.add k y (RM.empty Nat))) from
    OrderedAVL.Raw.find_union k (RM.add k x (RM.empty Nat)).is_bst (RM.add k y (RM.empty Nat)).is_bst]
  simp
