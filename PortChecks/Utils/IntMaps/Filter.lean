import PortChecks.SourceType
import Vellvm.Utils.IntMaps.Filter

open Vellvm.Utils.IntMaps
universe u v w

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|filter_dom_map_eq"
  filter_dom_map_eq : ∀ {A : Type u} {B : Type v} (f : IM.key → Bool) (g : A → B)
    (m : IntMap A) (k : IM.key) (e : B), IM.MapsTo k e (IM.map g (IP.filter_dom f m)) ↔
      IM.MapsTo k e (IP.filter_dom f (IM.map g m))

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|MapsTo_filter_true"
  MapsTo_filter_true : ∀ {A : Type u} (f : IM.key → A → Bool) (m : IM.t A) (k : IM.key) (e : A),
    (f k e = true ∧ IM.MapsTo k e m) ↔ IM.MapsTo k e (IP.filter f m)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|MapsTo_filter_subset"
  MapsTo_filter_subset : ∀ {A : Type u} (f : IM.key → A → Bool) (m : IM.t A) (k : IM.key) (e : A),
    IM.MapsTo k e (IP.filter f m) → IM.MapsTo k e m

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|not_MapsTo_filter"
  not_MapsTo_filter : ∀ {A : Type u} (f : IM.key → A → Bool) (m : IM.t A) (k : IM.key) (e : A),
    ¬ IM.MapsTo k e m → ¬ IM.MapsTo k e (IP.filter f m)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|MapsTo_filter_dom_true"
  MapsTo_filter_dom_true : ∀ {A : Type u} (f : IM.key → Bool) (m : IntMap A) (k : IM.key) (e : A),
    (f k = true ∧ IM.MapsTo k e m) ↔ IM.MapsTo k e (IP.filter_dom f m)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|MapsTo_filter_dom_subset"
  MapsTo_filter_dom_subset : ∀ {A : Type u} (f : IM.key → Bool) (m : IntMap A) (k : IM.key) (e : A),
    IM.MapsTo k e (IP.filter_dom f m) → IM.MapsTo k e m

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|not_MapsTo_filter_dom"
  not_MapsTo_filter_dom : ∀ {A : Type u} (f : IM.key → Bool) (m : IntMap A) (k : IM.key) (e : A),
    ¬ IM.MapsTo k e m → ¬ IM.MapsTo k e (IP.filter_dom f m)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|find_filter_true"
  find_filter_true : ∀ {A : Type u} (f : IM.key → A → Bool) (m : IntMap A) (k : IM.key) (a : A),
    IM.find k (IP.filter f m) = some a ↔ IM.find k m = some a ∧ f k a = true

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|find_filter_dom_true"
  find_filter_dom_true : ∀ {A : Type u} (f : IM.key → Bool) (m : IntMap A) (k : IM.key) (a : A),
    IM.find k (IP.filter_dom f m) = some a ↔ IM.find k m = some a ∧ f k = true

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IntMaps_find_None"
  IntMaps_find_None : ∀ {A : Type u} (k : IM.key) (m : IntMap A),
    IM.find k m = none ↔ ∀ e : A, ¬ IM.MapsTo k e m

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|find_filter_None"
  find_filter_None : ∀ {A : Type u} (f : IM.key → A → Bool) (m : IntMap A) (k : IM.key),
    IM.find k m = none → IM.find k (IP.filter f m) = none

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|find_filter_dom_None"
  find_filter_dom_None : ∀ {A : Type u} (f : IM.key → Bool) (m : IntMap A) (k : IM.key),
    IM.find k m = none → IM.find k (IP.filter_dom f m) = none

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|find_filter_dom_false"
  find_filter_dom_false : ∀ {elt : Type u} {m : IM.t elt} {k : IM.key} {f : IM.key → Bool},
    f k = false → IM.find k (IP.filter_dom f m) = none

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|filter_dom_Proper"
  filter_dom_Proper : ∀ {elt : Type u} {f : IM.key → Bool} (m n : IM.t elt),
    IM.Equal m n → IM.Equal (IP.filter_dom f m) (IP.filter_dom f n)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IntMaps_map_empty_Equal"
  IntMaps_map_empty_Equal : ∀ {A : Type u} {B : Type v} (f : A → B),
    IM.Equal (IM.map f (IM.empty A)) (IM.empty B)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IntMaps_map_id_Equal"
  IntMaps_map_id_Equal : ∀ {A : Type u} (m : IntMap A), IM.Equal (IM.map id m) m

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IntMaps_map_compose_Equal"
  IntMaps_map_compose_Equal : ∀ {A : Type u} {B : Type v} {C : Type w} (f : A → B) (g : B → C)
    (m : IntMap A), IM.Equal (IM.map (fun a ↦ g (f a)) m) (IM.map g (IM.map f m))

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IntMaps_map_add_Equal"
  IntMaps_map_add_Equal : ∀ {A : Type u} {B : Type v} (f : A → B) (m : IntMap A) (k : IM.key)
    (a : A), IM.Equal (IM.map f (IM.add k a m)) (IM.add k (f a) (IM.map f m))

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IntMaps_map_list_map_Equal"
  IntMaps_map_list_map_Equal : ∀ {A : Type u} {B : Type v} (f : A → B) (l : List (IM.key × A)),
    IM.Equal (IM.map f (IP.of_list l)) (IP.of_list (List.map (fun (i, x) ↦ (i, f x)) l))

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IntMaps_filter_dom_add_true_Equal"
  IntMaps_filter_dom_add_true_Equal : ∀ {A : Type u} (f : IM.key → Bool) (k : IM.key) (a : A)
    (m : IM.t A), f k = true → IM.Equal (IP.filter_dom f (IM.add k a m))
      (IM.add k a (IP.filter_dom f m))

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IntMaps_filter_dom_add_false_Equal"
  IntMaps_filter_dom_add_false_Equal : ∀ {A : Type u} (f : IM.key → Bool) (k : IM.key) (a : A)
    (m : IM.t A), f k = false → IM.Equal (IP.filter_dom f (IM.add k a m)) (IP.filter_dom f m)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IntMaps_filter_dom_list_filter_Equal"
  IntMaps_filter_dom_list_filter_Equal : ∀ {A : Type u} (f : IM.key → Bool) (l : List (IM.key × A)),
    IM.Equal (IP.filter_dom f (IP.of_list l)) (IP.of_list (List.filter (fun (k, _) ↦ f k) l))
