/- Port of Vellvm, Syntax/RawIdMaps.v. -/
module

public import Vellvm.Syntax.AstLib
public import Vellvm.Utils.OrderedAVLRemove
public import Vellvm.Numeric.Rocqlib
public import Vellvm.Map

@[expose] public section
namespace Vellvm.Syntax.RawIdMaps
open LLVMAst
open Vellvm.OrderedAVL

namespace RM
abbrev key := raw_id
abbrev t (A : Type u) := bst raw_id A
abbrev empty (A : Type u) : t A := bst.empty
abbrev add {A : Type u} := @bst.add raw_id A _
abbrev remove {A : Type u} := @bst.remove raw_id A _
abbrev find {A : Type u} := @bst.find raw_id A _
abbrev mem {A : Type u} := @bst.mem raw_id A _
abbrev elements {A : Type u} := @bst.elements raw_id A _
abbrev MapsTo (k : raw_id) (v : A) (m : t A) := Raw.MapsTo k v m.this
abbrev In (k : raw_id) (m : t A) := ∃ v, MapsTo k v m
theorem find_mapsto_iff (k : raw_id) (v : A) (m : t A) : find k m = some v ↔ MapsTo k v m :=
  Raw.find_eq_some_iff k v m.is_bst

@[simp] theorem find_empty {A} (k : raw_id) : find k (empty A) = none := rfl
@[simp] theorem find_add (k k' : raw_id) (x : A) (m : t A) :
    find k' (add k x m) = if k' = k then some x else find k' m := Raw.find_add k k' x m.is_bst
@[simp] theorem find_remove (k k' : raw_id) (m : t A) :
    find k' (remove k m) = if k' = k then none else find k' m := Raw.find_remove k k' m.is_bst
end RM

-- The lookup fragment of WProperties_fun used by ScopeTheory.
namespace RMF.F
theorem empty_o {A : Type u} (x : raw_id) : RM.find x (RM.empty A) = none := RM.find_empty x
theorem add_eq_o (m : RM.t A) (x y : raw_id) (e : A) (h : x = y) :
    RM.find y (RM.add x e m) = some e := by simp [h]
theorem add_neq_o (m : RM.t A) (x y : raw_id) (e : A) (h : x ≠ y) :
    RM.find y (RM.add x e m) = RM.find y m := by simp [Ne.symm h]
end RMF.F

abbrev rmap (A : Type u) := RM.t A

instance Map_rmap {V : Type u} : Map raw_id V (rmap V) :=
  ⟨RM.empty V, RM.add, RM.remove, RM.find, bst.union⟩

def rmap_to_list {V : Type u} (m : rmap V) := RM.elements m
def rid_member {V : Type u} (k : raw_id) (m : rmap V) := RM.mem k m
def rid_lookup {V : Type u} (k : raw_id) (m : rmap V) := RM.find k m

theorem Maps_lookup_rid_lookup {V : Type u} (k : raw_id) (m : rmap V) :
    Map.lookup k m = rid_lookup k m := rfl

def RM_Refine (R : A → B → Prop) (m : rmap A) (n : rmap B) : Prop :=
  (∀ k, rid_member k m ↔ rid_member k n) ∧
  (∀ k x y, rid_lookup k m = some x → rid_lookup k n = some y → R x y)

private theorem member_eq_lookup (k : raw_id) (m : rmap A) : rid_member k m = (rid_lookup k m).isSome :=
  Raw.mem_eq_isSome_find k m.this

theorem RM_Refine_empty {A : Type u} {B : Type v} (R : A → B → Prop) :
    RM_Refine R (RM.empty A) (RM.empty B) :=
  ⟨fun _ ↦ Iff.rfl, fun _ _ _ h ↦ nomatch h⟩

theorem RM_Refine_add {A : Type u} {B : Type v} (R : A → B → Prop) (m : rmap A) (n : rmap B)
    (k : raw_id) (x : A) (y : B) (h : RM_Refine R m n) (hxy : R x y) :
    RM_Refine R (RM.add k x m) (RM.add k y n) := by
  obtain ⟨dom, vals⟩ := h
  constructor
  · intro i
    specialize dom i
    simp only [member_eq_lookup, rid_lookup, RM.find_add] at dom ⊢
    split <;> simp_all
  · intro i a b
    by_cases hi : i = k
    · simp [rid_lookup, hi]; rintro rfl rfl; exact hxy
    · simpa [rid_lookup, hi] using vals i a b

theorem RM_Refine_lookup {A : Type u} {B : Type v} (R : A → B → Prop) (m : rmap A) (n : rmap B)
    (h : RM_Refine R m n) (k : raw_id) : Numeric.Rocqlib.option_rel R (rid_lookup k m) (rid_lookup k n) := by
  have hd := h.1 k
  rw [member_eq_lookup, member_eq_lookup] at hd
  cases hm : rid_lookup k m <;> cases hn : rid_lookup k n <;> simp [hm, hn] at hd
  · exact .none
  · exact .some _ _ (h.2 k _ _ hm hn)

instance MapOk_rmap {V : Type u} : MapOk (· = ·) (@Map_rmap V) where
  mapsto := RM.MapsTo
  mapsto_empty := fun _ _ h ↦ nomatch h
  mapsto_lookup := RM.find_mapsto_iff
  mapsto_add_eq m k v := (RM.find_mapsto_iff k v (RM.add k v m)).mp (by simp)
  mapsto_add_neq m k v k' hn v' := by
    change RM.MapsTo k' v' m ↔ RM.MapsTo k' v' (RM.add k v m)
    rw [← RM.find_mapsto_iff, ← RM.find_mapsto_iff]
    simp [Ne.symm hn]
  mapsto_remove_eq m k v := by
    change ¬RM.MapsTo k v (RM.remove k m)
    rw [← RM.find_mapsto_iff]
    simp
  mapsto_remove_neq m k k' hn v' := by
    change RM.MapsTo k' v' m ↔ RM.MapsTo k' v' (RM.remove k m)
    rw [← RM.find_mapsto_iff, ← RM.find_mapsto_iff]
    simp [Ne.symm hn]

end Vellvm.Syntax.RawIdMaps
