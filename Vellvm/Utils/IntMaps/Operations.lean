module

public import Vellvm.Utils.IntMaps.Basic
public import Vellvm.Utils.OrderedAVLRemove
public import Vellvm.Numeric.Rocqlib
public import Vellvm.Map

@[expose] public section
namespace Vellvm.Utils.IntMaps

abbrev delete (k : Int) (m : IntMap A) := OrderedAVL.bst.remove k m
abbrev union (m n : IntMap A) := OrderedAVL.bst.union m n

namespace IM
abbrev empty (A : Type u) := @IntMaps.empty A
abbrev add {A : Type u} := @IntMaps.add A
abbrev find {A : Type u} := @IntMaps.lookup A
abbrev mem {A : Type u} := @IntMaps.member A
abbrev remove {A : Type u} := @IntMaps.delete A
abbrev elements (m : t A) := OrderedAVL.Raw.elements m.this
abbrev Equal {A : Type u} := @IntMaps.Equal A
abbrev Raw.t := Raw.tree
abbrev Raw.fold (f : Int → A → B → B) (m : Raw.t A) (z : B) := OrderedAVL.Raw.fold f m z
abbrev fold (f : Int → A → B → B) (m : t A) (z : B) := Raw.fold f m.this z
end IM

namespace IP
abbrev uncurry (f : A → B → C) (p : A × B) := f p.1 p.2
abbrev of_list (l : List (Int × A)) := add_all l empty
end IP

namespace IS
abbrev t := IntMap Unit
abbrev empty : t := IntMaps.empty
abbrev add (k : Int) (s : t) := IntMaps.add k () s
abbrev mem (k : Int) (s : t) := member k s
abbrev elements (s : t) := OrderedAVL.Raw.keys s.this
abbrev fold (f : Int → B → B) (s : t) (z : B) := IM.fold (fun k _ ↦ f k) s z
end IS

namespace ISP
abbrev of_list (l : List Int) := l.foldr IS.add IS.empty
abbrev to_list := IS.elements
end ISP

def IM_find_many (xs : List Int) (im : IntMap A) : Option (List A) := xs.mapM (lookup · im)

def IM_merge (m₁ m₂ : IM.Raw.tree A) : IM.Raw.tree A :=
  IM.Raw.fold OrderedAVL.Raw.add m₂ m₁

@[simp] theorem lookup_empty {A : Type u} (q : Int) : lookup q (empty : IntMap A) = none := rfl

@[simp] theorem lookup_insert (q k : Int) (v : A) (m : IntMap A) :
    lookup q (add k v m) = if q = k then some v else lookup q m :=
  OrderedAVL.Raw.find_add k q v m.is_bst

@[simp] theorem lookup_delete (q k : Int) (m : IntMap A) :
    lookup q (delete k m) = if q = k then none else lookup q m :=
  OrderedAVL.Raw.find_remove k q m.is_bst

@[simp] theorem member_isSome (k : Int) (m : IntMap A) : member k m = (lookup k m).isSome :=
  OrderedAVL.Raw.mem_eq_isSome_find k m.this

theorem lookup_mapsTo (k : Int) (v : A) (m : IntMap A) : lookup k m = some v ↔ IM.MapsTo k v m :=
  OrderedAVL.Raw.find_eq_some_iff k v m.is_bst

instance Map_IntMap {A : Type u} : Map Int A (IntMap A) := ⟨empty, add, delete, lookup, union⟩

instance MapOk_IntMap {A : Type u} : MapOk Eq (@Map_IntMap A) where
  mapsto := IM.MapsTo
  mapsto_empty := fun _ _ h ↦ nomatch h
  mapsto_lookup := lookup_mapsTo
  mapsto_add_eq m k v := (lookup_mapsTo k v _).mp (by change lookup k (add k v m) = _; simp)
  mapsto_add_neq m k v k' hn v' := by
    change IM.MapsTo k' v' m ↔ IM.MapsTo k' v' (add k v m)
    simp [← lookup_mapsTo, Ne.symm hn]
  mapsto_remove_eq m k v := by
    change ¬IM.MapsTo k v (delete k m)
    simp [← lookup_mapsTo]
  mapsto_remove_neq m k k' hn v' := by
    change IM.MapsTo k' v' m ↔ IM.MapsTo k' v' (delete k m)
    simp [← lookup_mapsTo, Ne.symm hn]

end Vellvm.Utils.IntMaps
