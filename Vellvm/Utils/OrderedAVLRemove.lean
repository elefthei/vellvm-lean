/-
Tree algorithms translated from Rocq stdlib 9.2.0, FSets/FMapAVL.v.
Copyright INRIA, CNRS and contributors. GNU Lesser General Public License Version 2.1.
-/
module

public import Vellvm.Utils.OrderedAVLFacts
import Mathlib.Tactic.Tauto

@[expose] public section
namespace Vellvm.OrderedAVL
namespace Raw
open tree
variable {K : Type u} {A : Type v}

private theorem elements_aux_append (t : tree K A) (acc : List (K × A)) :
    elements_aux acc t = elements t ++ acc := by
  induction t generalizing acc with
  | Leaf => rfl
  | Node l k v r h ihl ihr =>
    simp only [elements, elements_aux]
    rw [ihl, ihl ((k, v) :: elements_aux [] r), ihr acc]
    simp [elements, List.append_assoc]

@[simp] theorem elements_leaf : elements (Leaf : tree K A) = [] := rfl

@[simp] theorem elements_node (l r : tree K A) (k : K) (v : A) (h : Int) :
    elements (Node l k v r h) = elements l ++ (k, v) :: elements r :=
  elements_aux_append l _

@[simp] theorem elements_bal (l r : tree K A) (k : K) (v : A) :
    elements (bal l k v r) = elements l ++ (k, v) :: elements r := by
  unfold bal
  repeat' first | split | simp [create, List.append_assoc]

@[simp] theorem map_fst_elements (t : tree K A) : (elements t).map Prod.fst = keys t := by
  induction t <;> simp_all [keys]

@[simp] theorem mapsTo_node {x k : K} {a v : A} {l r : tree K A} {h : Int} :
    MapsTo x a (Node l k v r h) ↔ (x = k ∧ a = v) ∨ MapsTo x a l ∨ MapsTo x a r := by
  constructor
  · intro hm; cases hm <;> simp_all
  · rintro (⟨rfl, rfl⟩ | hl | hr)
    · exact .MapsRoot rfl
    · exact .MapsLeft hl
    · exact .MapsRight hr

@[simp] theorem mapsTo_iff_mem_elements (x : K) (a : A) (t : tree K A) :
    MapsTo x a t ↔ (x, a) ∈ elements t := by
  induction t with
  | Leaf => exact ⟨fun h ↦ (nomatch h), fun h ↦ (nomatch h)⟩
  | Node l k v r h ihl ihr =>
    simp only [mapsTo_node, elements_node, List.mem_append, List.mem_cons, Prod.mk.injEq, ihl, ihr]
    tauto

private theorem elements_remove_min (l : tree K A) (k : K) (v : A) (r : tree K A) :
    (remove_min l k v r).2 :: elements (remove_min l k v r).1 =
      elements l ++ (k, v) :: elements r := by
  induction l generalizing k v r with
  | Leaf => rfl
  | Node ll lk lv lr _ ih _ =>
    rw [remove_min, elements_node, List.append_assoc]
    generalize he : remove_min ll lk lv lr = p
    obtain ⟨t, m⟩ := p
    have h := ih lk lv lr
    rw [he] at h
    simpa only [elements_bal, List.cons_append, List.append_assoc, List.singleton_append] using
      congrArg (· ++ (k, v) :: elements r) h

@[simp] theorem elements_merge (l r : tree K A) :
    elements (merge l r) = elements l ++ elements r := by
  cases l <;> cases r <;> simp only [merge, elements_leaf, List.nil_append, List.append_nil]
  rename_i rl k v rr h
  generalize he : remove_min rl k v rr = p
  obtain ⟨r', k', v'⟩ := p
  have hm := elements_remove_min rl k v rr
  rw [he] at hm
  simp only [elements_bal, elements_node, hm]

private theorem keys_remove_sublist [Ord K] (x : K) (t : tree K A) :
    (keys (remove x t)).Sublist (keys t) := by
  induction t with
  | Leaf => exact .refl _
  | Node l k v r h ihl ihr =>
    simp only [remove, keys]
    split
    · rw [keys_bal]; exact ihl.append (.refl _)
    · rw [← map_fst_elements (merge l r), elements_merge, List.map_append, map_fst_elements,
        map_fst_elements]; exact (List.Sublist.refl _).append (.cons k (.refl _))
    · rw [keys_bal]; exact (List.Sublist.refl _).append (.cons_cons k ihr)

theorem remove_bst [LinearOrder K] (x : K) {t : tree K A} (h : bst t) : bst (remove x t) :=
  (bst_iff_sorted _).mpr (((bst_iff_sorted _).mp h).sublist (keys_remove_sublist x t))

private theorem entry_in {x : K} {v : A} {t : tree K A} (he : (x, v) ∈ elements t) : In x t :=
  mapsTo_iff_in.mp ⟨v, (mapsTo_iff_mem_elements ..).mpr he⟩

theorem find_eq_some_iff [LinearOrder K] (x : K) (v : A) {t : tree K A} (ht : bst t) :
    find x t = some v ↔ MapsTo x v t := by
  induction ht with
  | BSLeaf => exact ⟨fun h ↦ (nomatch h), fun h ↦ (nomatch h)⟩
  | @BSNode l r k a h bl br hl hr ihl ihr =>
    have left (hm : MapsTo x v l) := hl x (mapsTo_iff_in.mp ⟨v, hm⟩)
    have right (hm : MapsTo x v r) := hr x (mapsTo_iff_in.mp ⟨v, hm⟩)
    simp only [find, mapsTo_node]
    split <;> rename_i cmp
    · rw [ihl]; have hx := compare_lt_iff_lt.mp cmp; grind
    · have hx := compare_eq_iff_eq.mp cmp; simp only [Option.some.injEq]; grind
    · rw [ihr]; have hx := compare_gt_iff_gt.mp cmp; grind

theorem mem_eq_isSome_find [Ord K] (x : K) (t : tree K A) : mem x t = (find x t).isSome := by
  induction t with
  | Leaf => rfl
  | Node l k v r h ihl ihr => simp only [mem, find]; split <;> simp [*]

theorem mem_iff_in [LinearOrder K] (x : K) {t : tree K A} (ht : bst t) : mem x t = true ↔ In x t := by
  rw [mem_eq_isSome_find, ← mapsTo_iff_in]
  simp only [← find_eq_some_iff x _ ht]
  cases find x t <;> simp

private theorem entry_remove [LinearOrder K] (x y : K) (a : A) {t : tree K A} (ht : bst t) :
    (y, a) ∈ elements (remove x t) ↔ y ≠ x ∧ (y, a) ∈ elements t := by
  induction ht with
  | BSLeaf => simp [remove]
  | @BSNode l r k v h bl br hl hr ihl ihr =>
    have left (hm : (y, a) ∈ elements l) := hl y (entry_in hm)
    have right (hm : (y, a) ∈ elements r) := hr y (entry_in hm)
    simp only [remove]
    split <;> rename_i cmp <;>
      simp only [elements_bal, elements_merge, elements_node, List.mem_append, List.mem_cons,
        Prod.mk.injEq, ihl, ihr]
    · have hx := compare_lt_iff_lt.mp cmp; grind
    · have hx := compare_eq_iff_eq.mp cmp; grind
    · have hx := compare_gt_iff_gt.mp cmp; grind

private theorem entry_add [LinearOrder K] (x y : K) (v a : A) {t : tree K A} (ht : bst t) :
    (y, a) ∈ elements (add x v t) ↔ (y = x ∧ a = v) ∨ (y ≠ x ∧ (y, a) ∈ elements t) := by
  induction ht with
  | BSLeaf => simp [add]
  | @BSNode l r k b h bl br hl hr ihl ihr =>
    have left (hm : (y, a) ∈ elements l) := hl y (entry_in hm)
    have right (hm : (y, a) ∈ elements r) := hr y (entry_in hm)
    simp only [add]
    split <;> rename_i cmp <;>
      simp only [elements_bal, elements_node, List.mem_append, List.mem_cons, Prod.mk.injEq, ihl, ihr]
    · have hx := compare_lt_iff_lt.mp cmp; grind
    · have hx := compare_eq_iff_eq.mp cmp; grind
    · have hx := compare_gt_iff_gt.mp cmp; grind

theorem find_add [LinearOrder K] (x y : K) (v : A) {t : tree K A} (ht : bst t) :
    find y (add x v t) = if y = x then some v else find y t := by
  apply Option.ext; intro a
  rw [find_eq_some_iff _ _ (add_bst _ _ ht), mapsTo_iff_mem_elements, entry_add _ _ _ _ ht]
  split <;> simp [*, find_eq_some_iff _ _ ht, mapsTo_iff_mem_elements]
  grind

theorem find_remove [LinearOrder K] (x y : K) {t : tree K A} (ht : bst t) :
    find y (remove x t) = if y = x then none else find y t := by
  apply Option.ext; intro a
  rw [find_eq_some_iff _ _ (remove_bst _ ht), mapsTo_iff_mem_elements, entry_remove _ _ _ ht]
  split <;> simp [*, find_eq_some_iff _ _ ht, mapsTo_iff_mem_elements]

private theorem elements_add_min [LinearOrder K] (k : K) (v : A) (t : tree K A)
    (ht : gt_tree k t) : elements (add k v t) = (k, v) :: elements t := by
  induction t with
  | Leaf => simp [add]
  | Node l x a r h ih _ =>
    have hx := compare_lt_iff_lt.mpr (ht x (.InRoot rfl))
    simp [add, hx, ih (fun y hy ↦ ht y (.InLeft hy))]

private theorem elements_add_max [LinearOrder K] (k : K) (v : A) (t : tree K A)
    (ht : lt_tree k t) : elements (add k v t) = elements t ++ [(k, v)] := by
  induction t with
  | Leaf => simp [add]
  | Node l x a r h _ ih =>
    have hx := compare_gt_iff_gt.mpr (ht x (.InRoot rfl))
    simp [add, hx, ih (fun y hy ↦ ht y (.InRight hy)), List.append_assoc]

/-- FMapAVL's join, which also handles large height differences after a split. -/
def join [Ord K] (l : tree K A) (k : K) (v : A) (r : tree K A) : tree K A :=
  match l, r with
  | Leaf, _ => add k v r
  | l, Leaf => add k v l
  | l@(Node ll x a lr lh), r@(Node rl y b rr rh) =>
    if lh > rh + 2 then bal ll x a (join lr k v r)
    else if rh > lh + 2 then bal (join l k v rl) y b rr
    else create l k v r
termination_by sizeOf l + sizeOf r
decreasing_by all_goals subst_vars; simp_wf; omega

theorem elements_join [LinearOrder K] (l : tree K A) (k : K) (v : A) (r : tree K A)
    (hl : lt_tree k l) (hr : gt_tree k r) :
    elements (join l k v r) = elements l ++ (k, v) :: elements r := by
  fun_induction join l k v r
  case case1 => simpa only [elements_leaf, List.nil_append] using elements_add_min k v _ hr
  case case2 => simpa only [elements_leaf] using elements_add_max k v _ hl
  case case3 ih =>
    rw [elements_bal, ih (fun z hz ↦ hl z (.InRight hz)) hr]
    simp [List.append_assoc]
  case case4 ih =>
    rw [elements_bal, ih hl (fun z hz ↦ hr z (.InLeft hz))]
    simp [List.append_assoc]
  case case5 => simp [create]

theorem join_bst [LinearOrder K] {l r : tree K A} {k : K} {v : A}
    (bl : bst l) (br : bst r) (hl : lt_tree k l) (hr : gt_tree k r) : bst (join l k v r) := by
  apply (bst_iff_sorted _).mpr
  rw [← map_fst_elements, elements_join _ _ _ _ hl hr, ← elements_node l r k v 0, map_fst_elements]
  exact (bst_iff_sorted _).mp (.BSNode bl br hl hr)

-- Union never uses split's optional binding: the first tree already supplies its value.
def splitSides [Ord K] (x : K) : tree K A → tree K A × tree K A
  | Leaf => (Leaf, Leaf)
  | Node l k v r _ =>
    match compare x k with
    | .lt => let (ll, rl) := splitSides x l; (ll, join rl k v r)
    | .eq => (l, r)
    | .gt => let (lr, rr) := splitSides x r; (join l k v lr, rr)

-- On a one-sided tree map2 calls map_option, which rejoins even unchanged bindings.
def rejoin [Ord K] : tree K A → tree K A
  | Leaf => Leaf
  | Node l k v r _ => join (rejoin l) k v (rejoin r)

def union [Ord K] : tree K A → tree K A → tree K A
  | Leaf, t => rejoin t
  | t, Leaf => rejoin t
  | Node l k v r _, t =>
    let (l', r') := splitSides k t
    join (union l l') k v (union r r')

private structure Models [LinearOrder K] (t : tree K A) (f : K → Option A) : Prop where
  valid : bst t
  lookup : ∀ y, find y t = f y

private theorem Models.congr [LinearOrder K] {f g : K → Option A} {t : tree K A}
    (ht : Models t f) (he : ∀ y, f y = g y) : Models t g :=
  ⟨ht.valid, fun y ↦ (ht.lookup y).trans (he y)⟩

private theorem support [LinearOrder K] {t : tree K A} {y : K} (ht : bst t) :
    find y t ≠ none ↔ In y t := by
  rw [← mapsTo_iff_in]
  simp only [← find_eq_some_iff _ _ ht]
  cases find y t <;> simp

private def choose [LinearOrder K] (k : K) (v : A) (f g : K → Option A) (y : K) :=
  if y < k then f y else if k < y then g y else some v

private theorem find_node_choose [LinearOrder K] (l r : tree K A) (k : K) (v : A) (h : Int)
    (y : K) : find y (Node l k v r h) = choose k v (find · l) (find · r) y := by
  simp only [find, choose]
  split <;> rename_i cmp
  · simp [compare_lt_iff_lt.mp cmp]
  · simp [compare_eq_iff_eq.mp cmp]
  · have hy := compare_gt_iff_gt.mp cmp; simp [hy, not_lt_of_gt hy]

private theorem join_models [LinearOrder K] {l r : tree K A} {k : K} {v : A} {f g : K → Option A}
    (lm : Models l f) (rm : Models r g)
    (fl : ∀ y, f y ≠ none → y < k) (gr : ∀ y, g y ≠ none → k < y) :
    Models (join l k v r) (choose k v f g) := by
  have hl : lt_tree k l := fun y hy ↦ fl y (lm.lookup y ▸ (support lm.valid).mpr hy)
  have hr : gt_tree k r := fun y hy ↦ gr y (rm.lookup y ▸ (support rm.valid).mpr hy)
  have bj := join_bst (v := v) lm.valid rm.valid hl hr
  have bn : bst (Node l k v r 0) := .BSNode lm.valid rm.valid hl hr
  refine ⟨bj, fun y ↦ ?_⟩
  calc
    find y (join l k v r) = find y (Node l k v r 0) := by
      apply Option.ext; intro a
      simp only [find_eq_some_iff _ _ bj, find_eq_some_iff _ _ bn, mapsTo_iff_mem_elements,
        elements_node, elements_join _ _ _ _ hl hr]
    _ = choose k v f g y := by simp [find_node_choose, choose, lm.lookup, rm.lookup]

private theorem rejoin_models [LinearOrder K] {t : tree K A} (ht : bst t) :
    Models (rejoin t) (find · t) := by
  induction ht with
  | BSLeaf => exact ⟨.BSLeaf, fun _ ↦ rfl⟩
  | @BSNode l r k v h bl br hl hr ihl ihr =>
    apply (join_models ihl ihr (fun y hy ↦ hl y ((support bl).mp hy))
      (fun y hy ↦ hr y ((support br).mp hy))).congr
    intro y; exact (find_node_choose ..).symm

private theorem split_models [LinearOrder K] (x : K) {t : tree K A} (ht : bst t) :
    Models (splitSides x t).1 (fun y ↦ if y < x then find y t else none) ∧
    Models (splitSides x t).2 (fun y ↦ if x < y then find y t else none) := by
  induction ht with
  | BSLeaf =>
    constructor <;> refine ⟨.BSLeaf, fun y ↦ ?_⟩ <;> simp [splitSides, find]
  | @BSNode l r k v h bl br hl hr ihl ihr =>
    have low (y : K) (hy : find y l ≠ none) := hl y ((support bl).mp hy)
    have high (y : K) (hy : find y r ≠ none) := hr y ((support br).mp hy)
    simp only [splitSides]
    split <;> rename_i cmp
    · have hx := compare_lt_iff_lt.mp cmp
      constructor
      · apply ihl.1.congr; intro y; simp only [find_node_choose, choose]; grind
      · apply (join_models (v := v) ihl.2 ⟨br, fun _ ↦ rfl⟩
          (fun y hy ↦ low y (by intro hn; simp [hn] at hy)) high).congr
        intro y; simp only [find_node_choose, choose]; grind
    · obtain rfl := compare_eq_iff_eq.mp cmp
      constructor
      · refine ⟨bl, fun y ↦ ?_⟩
        simp only [find_node_choose, choose]; grind
      · refine ⟨br, fun y ↦ ?_⟩
        simp only [find_node_choose, choose]; grind
    · have hx := compare_gt_iff_gt.mp cmp
      constructor
      · apply (join_models (v := v) ⟨bl, fun _ ↦ rfl⟩ ihr.1 low
          (fun y hy ↦ high y (by intro hn; simp [hn] at hy))).congr
        intro y; simp only [find_node_choose, choose]; grind
      · apply ihr.2.congr; intro y; simp only [find_node_choose, choose]; grind

private theorem or_mask_bound {p : Prop} [Decidable p] {a b : Option A} (ha : a ≠ none → p) :
    a.or (if p then b else none) ≠ none → p := by
  by_cases hp : p
  · exact fun _ ↦ hp
  · have hn : a = none := by cases a <;> simp_all
    simp [hp, hn]

private theorem union_models [LinearOrder K] {s t : tree K A} (hs : bst s) (ht : bst t) :
    Models (union s t) (fun y ↦ (find y s).or (find y t)) := by
  induction hs generalizing t with
  | BSLeaf =>
    exact (rejoin_models ht).congr (fun _ ↦ rfl)
  | @BSNode l r k v h bl br hl hr ihl ihr =>
    cases t with
    | Leaf =>
      apply (rejoin_models (.BSNode bl br hl hr)).congr
      intro y; simp [find]
    | Node tl tk tv tr th =>
      obtain ⟨sl, sr⟩ := split_models k ht
      apply (join_models (v := v) (ihl sl.valid) (ihr sr.valid)
        (fun y hy ↦ or_mask_bound (fun hn ↦ hl y ((support bl).mp hn)) (sl.lookup y ▸ hy))
        (fun y hy ↦ or_mask_bound (fun hn ↦ hr y ((support br).mp hn)) (sr.lookup y ▸ hy))).congr
      intro y
      rw [find_node_choose l r]
      rcases lt_trichotomy y k with hh | rfl | hh
      · simp [choose, sl.lookup, hh]
      · simp [choose]
      · simp [choose, sr.lookup, hh, not_lt_of_gt hh]

theorem union_bst [LinearOrder K] {s t : tree K A} (hs : bst s) (ht : bst t) :
    bst (union s t) := (union_models hs ht).valid

theorem find_union [LinearOrder K] (x : K) {s t : tree K A} (hs : bst s) (ht : bst t) :
    find x (union s t) = (find x s).or (find x t) := (union_models hs ht).lookup x

end Raw

namespace bst
variable {K : Type u} {A : Type v} [LinearOrder K]

def empty : bst K A := ⟨.Leaf, .BSLeaf⟩
def add (k : K) (v : A) (m : bst K A) : bst K A := ⟨_, Raw.add_bst k v m.is_bst⟩
def remove (k : K) (m : bst K A) : bst K A := ⟨_, Raw.remove_bst k m.is_bst⟩
def find (k : K) (m : bst K A) := Raw.find k m.this
def mem (k : K) (m : bst K A) := Raw.mem k m.this
def elements (m : bst K A) := Raw.elements m.this
def union (s t : bst K A) : bst K A := ⟨_, Raw.union_bst s.is_bst t.is_bst⟩

end bst
end Vellvm.OrderedAVL
