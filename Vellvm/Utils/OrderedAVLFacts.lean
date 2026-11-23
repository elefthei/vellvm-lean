module

public import Vellvm.Utils.OrderedAVL
public import Mathlib.Order.Basic
import Mathlib.Tactic.Tauto

@[expose] public section
namespace Vellvm.OrderedAVL.Raw
open tree

variable {K : Type u} {A : Type v}

def keys : tree K A → List K
  | Leaf => []
  | Node l k _ r _ => keys l ++ k :: keys r

@[simp] theorem in_node {x k : K} {l r : tree K A} {a : A} {h : Int} :
    In x (Node l k a r h) ↔ x = k ∨ In x l ∨ In x r := by
  constructor
  · intro hh; cases hh <;> simp_all
  · rintro (h | h | h)
    · exact .InRoot h
    · exact .InLeft h
    · exact .InRight h

@[simp] theorem in_iff_mem_keys (x : K) (t : tree K A) : In x t ↔ x ∈ keys t := by
  induction t with
  | Leaf => exact ⟨fun h ↦ (nomatch h), fun h ↦ (nomatch h)⟩
  | Node l k a r h ihl ihr => simp only [in_node, keys, List.mem_append, List.mem_cons, ihl, ihr]; tauto

theorem bst_iff_sorted [LinearOrder K] (t : tree K A) : bst t ↔ (keys t).Pairwise (· < ·) := by
  induction t with
  | Leaf => exact ⟨fun _ ↦ .nil, fun _ ↦ .BSLeaf⟩
  | Node l k a r h ihl ihr =>
    simp only [keys, List.pairwise_append, List.pairwise_cons]
    constructor
    · intro bt
      cases bt
      rename_i bl hl br hr
      refine ⟨ihl.mp bl, ⟨fun y hy ↦ hr y ((in_iff_mem_keys ..).mpr hy), ihr.mp br⟩, ?_⟩
      intro x hx y hy
      have hlt := hl x ((in_iff_mem_keys ..).mpr hx)
      rcases List.mem_cons.mp hy with rfl | hmem
      · exact hlt
      · exact lt_trans hlt (hr y ((in_iff_mem_keys ..).mpr hmem))
    · rintro ⟨sl, ⟨hr, sr⟩, hlr⟩
      exact .BSNode (ihl.mpr sl) (ihr.mpr sr)
        (fun x hx ↦ hlr x ((in_iff_mem_keys ..).mp hx) k (.head _))
        (fun y hy ↦ hr y ((in_iff_mem_keys ..).mp hy))

@[simp] theorem keys_bal (l : tree K A) (k : K) (v : A) (r : tree K A) :
    keys (bal l k v r) = keys l ++ k :: keys r := by
  unfold bal
  repeat' first | split | simp [create, keys, List.append_assoc]

theorem bal_bst [LinearOrder K] {l r : tree K A} {k : K} {v : A}
    (bl : bst l) (br : bst r) (hl : lt_tree k l) (hr : gt_tree k r) : bst (bal l k v r) := by
  rw [bst_iff_sorted, keys_bal]
  exact (bst_iff_sorted (Node l k v r 0)).mp (.BSNode bl br hl hr)

@[simp] theorem keys_add_mem [LinearOrder K] (x y : K) (v : A) (t : tree K A) :
    y ∈ keys (add x v t) ↔ y = x ∨ y ∈ keys t := by
  induction t with
  | Leaf => simp [add, keys]
  | Node l k a r h ihl ihr =>
    simp only [add]
    split <;> rename_i cmp
    · simp only [keys_bal, keys, List.mem_append, List.mem_cons, ihl]; tauto
    · obtain rfl := compare_eq_iff_eq.mp cmp
      simp only [keys, List.mem_append, List.mem_cons]; tauto
    · simp only [keys_bal, keys, List.mem_append, List.mem_cons, ihr]; tauto

theorem add_bst [LinearOrder K] (x : K) (v : A) {t : tree K A} (h : bst t) : bst (add x v t) := by
  induction h with
  | BSLeaf => exact .BSNode .BSLeaf .BSLeaf (fun _ h ↦ nomatch h) (fun _ h ↦ nomatch h)
  | @BSNode l r k a ht bl br hl hr ihl ihr =>
    simp only [add]
    split <;> rename_i cmp
    · apply bal_bst ihl br _ hr
      intro y hy
      rcases (keys_add_mem ..).mp ((in_iff_mem_keys ..).mp hy) with rfl | hmem
      · exact compare_lt_iff_lt.mp cmp
      · exact hl y ((in_iff_mem_keys ..).mpr hmem)
    · exact .BSNode bl br hl hr
    · apply bal_bst bl ihr hl
      intro y hy
      rcases (keys_add_mem ..).mp ((in_iff_mem_keys ..).mp hy) with rfl | hmem
      · exact compare_gt_iff_gt.mp cmp
      · exact hr y ((in_iff_mem_keys ..).mpr hmem)

end Vellvm.OrderedAVL.Raw
