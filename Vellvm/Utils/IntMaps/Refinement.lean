module

public import Vellvm.Utils.IntMaps.Operations

@[expose] public section
namespace Vellvm.Utils.IntMaps

open Vellvm.Utils.RelationsUtil (prod_rel)
open Vellvm.Numeric.Rocqlib (option_rel)
universe u v

private theorem refine_iff_lookup {A : Type u} {B : Type v} {R : A → B → Prop}
    {m : IntMap A} {n : IntMap B} :
    IM_Refine R m n ↔ ∀ k, option_rel R (lookup k m) (lookup k n) := by
  constructor
  · rintro ⟨dom, val⟩ k
    have hd := dom k
    simp only [member_isSome] at hd
    cases hx : lookup k m <;> cases hy : lookup k n
    · exact .none
    · simp [hx, hy] at hd
    · simp [hx, hy] at hd
    · exact .some _ _ (val k _ _ hx hy)
  · intro h
    constructor
    · intro k
      simp only [member_isSome]
      have hk := h k
      generalize lookup k m = x, lookup k n = y at hk ⊢
      cases hk <;> simp
    · intro k x y hx hy
      have hk := h k
      rw [hx, hy] at hk
      cases hk; assumption

theorem IM_Refine_empty {A : Type u} {B : Type v} (R : A → B → Prop) :
    IM_Refine R (IM.empty A) (IM.empty B) :=
  refine_iff_lookup.mpr fun _ ↦ .none

theorem IM_Refine_add {A : Type u} {B : Type v} (R : A → B → Prop) (m : IntMap A) (n : IntMap B)
    (k : IM.key) (x : A) (y : B) (h : IM_Refine R m n) (hxy : R x y) :
    IM_Refine R (add k x m) (add k y n) := by
  apply refine_iff_lookup.mpr
  intro q
  simp only [lookup_insert]
  split
  · exact .some _ _ hxy
  · exact refine_iff_lookup.mp h q

theorem IM_Refine_Forall2 {A : Type u} {B : Type v} (xs : List (Int × A)) (ys : List (Int × B))
    (R : A → B → Prop) (h : List.Forall₂ (prod_rel Eq R) xs ys) :
    IM_Refine R (IP.of_list xs) (IP.of_list ys) := by
  induction h with
  | nil => exact IM_Refine_empty R
  | @cons x y xs ys h _ ih =>
    change IM_Refine R (add x.1 x.2 (IP.of_list xs)) (add y.1 y.2 (IP.of_list ys))
    rw [h.1]
    exact IM_Refine_add R _ _ _ _ _ ih h.2

theorem IM_Refine_of_list_app {A : Type u} {B : Type v} (R : A → B → Prop)
    (xs xs' : List (IM.key × A)) (ys ys' : List (IM.key × B))
    (h' : List.Forall₂ (prod_rel Eq R) xs' ys') (h : List.Forall₂ (prod_rel Eq R) xs ys) :
    IM_Refine R (IP.of_list (xs' ++ xs)) (IP.of_list (ys' ++ ys)) := by
  apply IM_Refine_Forall2
  induction h' with
  | nil => exact h
  | cons hxy _ ih => exact .cons hxy ih

theorem IM_Refine_lookup {A : Type u} {B : Type v} (R : A → B → Prop) (m : IntMap A) (n : IntMap B)
    (h : IM_Refine R m n) (k : IM.key) : option_rel R (lookup k m) (lookup k n) :=
  refine_iff_lookup.mp h k

theorem IM_Refine_remove {A : Type u} {B : Type v} (R : A → B → Prop) (m : IntMap A) (n : IntMap B)
    (k : IM.key) (h : IM_Refine R m n) : IM_Refine R (delete k m) (delete k n) := by
  apply refine_iff_lookup.mpr
  intro q
  simp only [lookup_delete]
  split
  · exact .none
  · exact IM_Refine_lookup R m n h q

theorem IM_Refine_add_all_index {A : Type u} {B : Type v} (R : A → B → Prop) (xs : List A)
    (ys : List B) (z : Int) (m : IntMap A) (n : IntMap B) (all : List.Forall₂ R xs ys)
    (h : IM_Refine R m n) : IM_Refine R (add_all_index xs z m) (add_all_index ys z n) := by
  induction all generalizing z with
  | nil => exact h
  | cons hxy _ ih => exact IM_Refine_add R _ _ z _ _ (ih (z + 1)) hxy

theorem IM_Refine_add_all_index_acc {A : Type u} {B : Type v} (R : A → B → Prop) (xs : List A)
    (ys : List B) (z : Int) (m : IntMap A) (n : IntMap B) (all : List.Forall₂ R xs ys)
    (h : IM_Refine R m n) : IM_Refine R (add_all_index_acc xs z m) (add_all_index_acc ys z n) := by
  induction all generalizing z m n with
  | nil => exact h
  | cons hxy _ ih => exact ih (z + 1) _ _ (IM_Refine_add R m n z _ _ h hxy)

private theorem greatest_iff_maximal {A : Type u} (m : IM.t A) (k : IM.key) :
    IM_greatest_key m = some k ↔ member k m = true ∧ ∀ j, member j m = true → j ≤ k := by
  have mem (j : Int) : member j m = true ↔ IM.Raw.In j m.this :=
    OrderedAVL.Raw.mem_iff_in j m.is_bst
  have spec {g : Int} (hg : IM_greatest_key m = some g) :
      member g m = true ∧ ∀ j, member j m = true → j ≤ g := by
    refine ⟨(mem g).mpr (OrderedAVL.Raw.mapsTo_iff_in.mp (IM_greatest_key_In m g hg)), ?_⟩
    intro j hj
    have := IM_greatest_key_lt m g hg j ((mem j).mp hj)
    omega
  refine ⟨spec, ?_⟩
  rintro ⟨hk, bound⟩
  obtain ⟨g, hg⟩ := IM_greatest_key_In' m k (OrderedAVL.Raw.mapsTo_iff_in.mpr ((mem k).mp hk))
  have hs := spec hg
  rw [hg, le_antisymm (bound g hs.1) (hs.2 k hk)]

theorem IM_greatest_key_morph {A : Type u} {B : Type v} (m : IM.t A) (n : IM.t B)
    (dom : ∀ k : IM.key, member k m = true ↔ member k n = true) :
    IM_greatest_key m = IM_greatest_key n := by
  apply Option.ext
  intro k
  simp only [greatest_iff_maximal, dom]

end Vellvm.Utils.IntMaps
