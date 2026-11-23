import PortChecks.SourceType
import Vellvm.Utils.IntMaps.Refinement

open Vellvm.Utils.IntMaps
open Vellvm.Utils.RelationsUtil (prod_rel)
open Vellvm.Numeric.Rocqlib (option_rel)
universe u v

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_Refine_empty"
  IM_Refine_empty : ∀ {A : Type u} {B : Type v} (R : A → B → Prop),
    IM_Refine R (IM.empty A) (IM.empty B)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_Refine_add"
  IM_Refine_add : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (m : IntMap A) (n : IntMap B)
    (k : IM.key) (x : A) (y : B), IM_Refine R m n → R x y → IM_Refine R (add k x m) (add k y n)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_Refine_Forall2"
  IM_Refine_Forall2 : ∀ {A : Type u} {B : Type v} (xs : List (Int × A)) (ys : List (Int × B))
    (R : A → B → Prop), List.Forall₂ (prod_rel Eq R) xs ys → IM_Refine R (IP.of_list xs) (IP.of_list ys)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_Refine_of_list_app"
  IM_Refine_of_list_app : ∀ {A : Type u} {B : Type v} (R : A → B → Prop)
    (xs xs' : List (IM.key × A)) (ys ys' : List (IM.key × B)),
    List.Forall₂ (prod_rel Eq R) xs' ys' → List.Forall₂ (prod_rel Eq R) xs ys →
    IM_Refine R (IP.of_list (xs' ++ xs)) (IP.of_list (ys' ++ ys))

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_Refine_lookup"
  IM_Refine_lookup : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (m : IntMap A) (n : IntMap B),
    IM_Refine R m n → ∀ k : IM.key, option_rel R (lookup k m) (lookup k n)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_Refine_remove"
  IM_Refine_remove : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (m : IntMap A) (n : IntMap B)
    (k : IM.key), IM_Refine R m n → IM_Refine R (delete k m) (delete k n)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_Refine_add_all_index"
  IM_Refine_add_all_index : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (xs : List A)
    (ys : List B) (z : Int) (m : IntMap A) (n : IntMap B), List.Forall₂ R xs ys → IM_Refine R m n →
    IM_Refine R (add_all_index xs z m) (add_all_index ys z n)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_Refine_add_all_index_acc"
  IM_Refine_add_all_index_acc : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (xs : List A)
    (ys : List B) (z : Int) (m : IntMap A) (n : IntMap B), List.Forall₂ R xs ys → IM_Refine R m n →
    IM_Refine R (add_all_index_acc xs z m) (add_all_index_acc ys z n)

#source_check "src/rocq/Utils/IntMaps.v|Vellvm.Utils.IntMaps|IM_greatest_key_morph"
  IM_greatest_key_morph : ∀ {A : Type u} {B : Type v} (m : IM.t A) (n : IM.t B),
    (∀ k : IM.key, member k m = true ↔ member k n = true) → IM_greatest_key m = IM_greatest_key n
