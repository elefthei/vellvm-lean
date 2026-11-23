module

public import Vellvm.Utils.IntMaps.Operations

@[expose] public section
namespace Vellvm.Utils.IntMaps

open OrderedAVL
universe u v w

/-- FMapAVL maps values in place in the tree shape, retaining even noncanonical heights. -/
def IM.Raw.map (f : A → B) : IM.Raw.tree A → IM.Raw.tree B
  | .Leaf => .Leaf
  | .Node l k a r h => .Node (IM.Raw.map f l) k (f a) (IM.Raw.map f r) h

private theorem map_keys (f : A → B) (t : IM.Raw.tree A) :
    Raw.keys (IM.Raw.map f t) = Raw.keys t := by
  induction t <;> simp [IM.Raw.map, Raw.keys, *]

def IM.map (f : A → B) (m : IM.t A) : IM.t B :=
  ⟨IM.Raw.map f m.this, (Raw.bst_iff_sorted _).mpr (by
    rw [map_keys]; exact (Raw.bst_iff_sorted _).mp m.is_bst)⟩

private theorem find_raw_map (f : A → B) (k : Int) (t : IM.Raw.tree A) :
    Raw.find k (IM.Raw.map f t) = (Raw.find k t).map f := by
  induction t with
  | Leaf => rfl
  | Node l x a r h il ir => simp only [IM.Raw.map, Raw.find]; split <;> simp [*]

private theorem lookup_map (f : A → B) (k : Int) (m : IM.t A) :
    lookup k (IM.map f m) = (lookup k m).map f := find_raw_map f k m.this

/-- Fold left subtree, root, then right subtree: insertion order determines the result's raw tree. -/
def IP.filter (f : IM.key → A → Bool) (m : IM.t A) : IM.t A :=
  Raw.fold step m.this empty
where
  step (k : Int) (a : A) (acc : IntMap A) := if f k a then add k a acc else acc

def IP.filter_dom (f : IM.key → Bool) : IM.t A → IM.t A := IP.filter (fun k _ ↦ f k)

private theorem lookup_step (f : Int → A → Bool) (q k : Int) (a : A) (m : IntMap A) :
    lookup q (IP.filter.step f k a m) = if q = k ∧ f k a = true then some a else lookup q m := by
  cases hf : f k a <;> simp [IP.filter.step, hf, lookup_insert]

private theorem find_outside {q : Int} {t : IM.Raw.tree A} (ht : Raw.bst t) (h : ¬ Raw.In q t) :
    Raw.find q t = none := by
  cases he : Raw.find q t with
  | none => rfl
  | some a => exact (h (Raw.mapsTo_iff_in.mp ⟨a, (Raw.find_eq_some_iff q a ht).mp he⟩)).elim

private theorem lookup_fold_filter (f : Int → A → Bool) (q : Int) {t : IM.Raw.tree A}
    (ht : Raw.bst t) (acc : IntMap A) : lookup q (Raw.fold (IP.filter.step f) t acc) =
      ((Raw.find q t).filter (f q)).or (lookup q acc) := by
  induction ht generalizing acc with
  | BSLeaf => rfl
  | @BSNode l r k a h bl br hl hr il ir =>
    have left (hle : k ≤ q) := find_outside bl (fun h ↦ (not_lt_of_ge hle) (hl q h))
    have right (hle : q ≤ k) := find_outside br (fun h ↦ (not_lt_of_ge hle) (hr q h))
    simp only [Raw.fold, ir, lookup_step, il, Raw.find]
    rcases lt_trichotomy q k with hq | rfl | hq
    · simp [compare_lt_iff_lt.mpr hq, right hq.le, ne_of_lt hq]
    · cases hf : f q a <;> simp [left le_rfl, right le_rfl, hf, Option.filter]
    · simp [compare_gt_iff_gt.mpr hq, left hq.le, ne_of_gt hq]

private theorem lookup_filter (f : Int → A → Bool) (k : Int) (m : IntMap A) :
    lookup k (IP.filter f m) = (lookup k m).filter (f k) := by
  unfold IP.filter
  rw [lookup_fold_filter f k m.is_bst, lookup_empty, Option.or_none]
  rfl

private theorem lookup_filter_dom (f : Int → Bool) (k : Int) (m : IntMap A) :
    lookup k (IP.filter_dom f m) = if f k then lookup k m else none := by
  unfold IP.filter_dom
  rw [lookup_filter]
  cases f k <;> cases lookup k m <;> rfl

theorem filter_dom_map_eq {A : Type u} {B : Type v} (f : IM.key → Bool) (g : A → B)
    (m : IntMap A) (k : IM.key) (e : B) : IM.MapsTo k e (IM.map g (IP.filter_dom f m)) ↔
      IM.MapsTo k e (IP.filter_dom f (IM.map g m)) := by
  simp only [← lookup_mapsTo, lookup_map, lookup_filter_dom]
  cases f k <;> simp

theorem MapsTo_filter_true {A : Type u} (f : IM.key → A → Bool) (m : IM.t A) (k : IM.key) (e : A) :
    (f k e = true ∧ IM.MapsTo k e m) ↔ IM.MapsTo k e (IP.filter f m) := by
  simp only [← lookup_mapsTo, lookup_filter, Option.filter_eq_some_iff, and_comm]

theorem MapsTo_filter_subset {A : Type u} (f : IM.key → A → Bool) (m : IM.t A) (k : IM.key)
    (e : A) (h : IM.MapsTo k e (IP.filter f m)) : IM.MapsTo k e m :=
  ((MapsTo_filter_true f m k e).mpr h).2

theorem not_MapsTo_filter {A : Type u} (f : IM.key → A → Bool) (m : IM.t A) (k : IM.key) (e : A)
    (h : ¬ IM.MapsTo k e m) : ¬ IM.MapsTo k e (IP.filter f m) := h ∘ MapsTo_filter_subset f m k e

theorem MapsTo_filter_dom_true {A : Type u} (f : IM.key → Bool) (m : IntMap A) (k : IM.key) (e : A) :
    (f k = true ∧ IM.MapsTo k e m) ↔ IM.MapsTo k e (IP.filter_dom f m) :=
  MapsTo_filter_true (fun i _ ↦ f i) m k e

theorem MapsTo_filter_dom_subset {A : Type u} (f : IM.key → Bool) (m : IntMap A) (k : IM.key)
    (e : A) : IM.MapsTo k e (IP.filter_dom f m) → IM.MapsTo k e m :=
  MapsTo_filter_subset (fun i _ ↦ f i) m k e

theorem not_MapsTo_filter_dom {A : Type u} (f : IM.key → Bool) (m : IntMap A) (k : IM.key) (e : A) :
    ¬ IM.MapsTo k e m → ¬ IM.MapsTo k e (IP.filter_dom f m) := not_MapsTo_filter (fun i _ ↦ f i) m k e

theorem find_filter_true {A : Type u} (f : IM.key → A → Bool) (m : IntMap A) (k : IM.key) (a : A) :
    IM.find k (IP.filter f m) = some a ↔ IM.find k m = some a ∧ f k a = true := by
  rw [IM.find, lookup_filter, Option.filter_eq_some_iff]

theorem find_filter_dom_true {A : Type u} (f : IM.key → Bool) (m : IntMap A) (k : IM.key) (a : A) :
    IM.find k (IP.filter_dom f m) = some a ↔ IM.find k m = some a ∧ f k = true :=
  find_filter_true (fun i _ ↦ f i) m k a

theorem IntMaps_find_None {A : Type u} (k : IM.key) (m : IntMap A) :
    IM.find k m = none ↔ ∀ e, ¬ IM.MapsTo k e m := by
  simp only [IM.find, ← lookup_mapsTo]
  cases lookup k m <;> simp

theorem find_filter_None {A : Type u} (f : IM.key → A → Bool) (m : IntMap A) (k : IM.key)
    (h : IM.find k m = none) : IM.find k (IP.filter f m) = none := by
  simp [IM.find, lookup_filter, show lookup k m = none from h]

theorem find_filter_dom_None {A : Type u} (f : IM.key → Bool) (m : IntMap A) (k : IM.key) :
    IM.find k m = none → IM.find k (IP.filter_dom f m) = none := find_filter_None (fun i _ ↦ f i) m k

theorem find_filter_dom_false {elt : Type u} {m : IM.t elt} {k : IM.key} {f : IM.key → Bool}
    (h : f k = false) : IM.find k (IP.filter_dom f m) = none := by simp [IM.find, lookup_filter_dom, h]

theorem filter_dom_Proper {elt : Type u} {f : IM.key → Bool} (m n : IM.t elt) (h : IM.Equal m n) :
    IM.Equal (IP.filter_dom f m) (IP.filter_dom f n) := by
  intro q; simp only [lookup_filter_dom, h q]

theorem IntMaps_map_empty_Equal {A : Type u} {B : Type v} (f : A → B) :
    IM.Equal (IM.map f (IM.empty A)) (IM.empty B) := fun _ ↦ rfl

theorem IntMaps_map_id_Equal {A : Type u} (m : IntMap A) : IM.Equal (IM.map id m) m := by
  intro q; simp [lookup_map]

theorem IntMaps_map_compose_Equal {A : Type u} {B : Type v} {C : Type w} (f : A → B) (g : B → C)
    (m : IntMap A) : IM.Equal (IM.map (fun a ↦ g (f a)) m) (IM.map g (IM.map f m)) := by
  intro q; simp only [lookup_map, Option.map_map, Function.comp_def]

theorem IntMaps_map_add_Equal {A : Type u} {B : Type v} (f : A → B) (m : IntMap A) (k : IM.key)
    (a : A) : IM.Equal (IM.map f (IM.add k a m)) (IM.add k (f a) (IM.map f m)) := by
  intro q; by_cases h : q = k <;> simp [IM.add, lookup_map, lookup_insert, h]

theorem IntMaps_map_list_map_Equal {A : Type u} {B : Type v} (f : A → B) (l : List (IM.key × A)) :
    IM.Equal (IM.map f (IP.of_list l)) (IP.of_list (List.map (fun (i, x) ↦ (i, f x)) l)) := by
  intro q
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, a⟩ := p
    change lookup q (IM.map f (add k a (IP.of_list l))) =
      lookup q (add k (f a) (IP.of_list (l.map fun (i, x) ↦ (i, f x))))
    rw [IntMaps_map_add_Equal f _ k a q, lookup_insert, lookup_insert, ih]

theorem IntMaps_filter_dom_add_true_Equal {A : Type u} (f : IM.key → Bool) (k : IM.key) (a : A)
    (m : IM.t A) (h : f k = true) : IM.Equal (IP.filter_dom f (IM.add k a m))
      (IM.add k a (IP.filter_dom f m)) := by
  intro q; by_cases hq : q = k <;> simp [lookup_filter_dom, IM.add, lookup_insert, hq, h]

theorem IntMaps_filter_dom_add_false_Equal {A : Type u} (f : IM.key → Bool) (k : IM.key) (a : A)
    (m : IM.t A) (h : f k = false) : IM.Equal (IP.filter_dom f (IM.add k a m)) (IP.filter_dom f m) := by
  intro q; by_cases hq : q = k <;> simp [lookup_filter_dom, IM.add, lookup_insert, hq, h]

theorem IntMaps_filter_dom_list_filter_Equal {A : Type u} (f : IM.key → Bool) (l : List (IM.key × A)) :
    IM.Equal (IP.filter_dom f (IP.of_list l)) (IP.of_list (List.filter (fun (k, _) ↦ f k) l)) := by
  intro q
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, a⟩ := p
    cases hf : f k with
    | false =>
      rw [List.filter_cons_of_neg (by simpa using hf)]
      exact (IntMaps_filter_dom_add_false_Equal f k a _ hf q).trans ih
    | true =>
      rw [List.filter_cons_of_pos (by exact hf)]
      change lookup q (IP.filter_dom f (add k a (IP.of_list l))) =
        lookup q (add k a (IP.of_list (l.filter fun (i, _) ↦ f i)))
      rw [IntMaps_filter_dom_add_true_Equal f k a _ hf q, lookup_insert, lookup_insert, ih]

end Vellvm.Utils.IntMaps
