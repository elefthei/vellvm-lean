module

public import Vellvm.Utils.OrderedAVL

@[expose] public section
namespace Vellvm.Utils.IntMaps

namespace IM
namespace Raw
abbrev key := Int
abbrev tree := OrderedAVL.Raw.tree Int
export OrderedAVL.Raw.tree (Leaf Node)
export OrderedAVL.Raw (MapsTo In lt_tree gt_tree)
end Raw
abbrev key := Int
abbrev bst := OrderedAVL.bst Int
abbrev t := bst
export OrderedAVL.bst (this is_bst)

def MapsTo (k : Int) (v : A) (m : t A) := Raw.MapsTo k v m.this
def In (k : Int) (m : t A) := ∃ v, MapsTo k v m
def Empty (m : t A) := ∀ k v, ¬ MapsTo k v m
end IM

abbrev IntMap := IM.t

def rightmost (fallback : Int) : IM.Raw.tree A → Int
  | .Leaf => fallback
  | .Node _ k _ r _ => rightmost k r

def IM_raw_greatest_key : IM.Raw.tree A → Option Int
  | .Leaf => none
  | .Node _ k _ r _ => some (rightmost k r)

def IM_greatest_key (m : IM.t A) := IM_raw_greatest_key m.this

def next_key (m : IntMap A) : Int :=
  match IM_greatest_key m with
  | some k => 1 + k
  | none => 0

private theorem rightmost_mem (r : IM.Raw.tree A) (k : Int) :
    rightmost k r = k ∨ IM.Raw.In (rightmost k r) r := by
  induction r generalizing k with
  | Leaf => exact .inl rfl
  | Node l x v r h _ ihr =>
    exact .inr (match ihr x with | .inl eq => .InRoot eq | .inr hr => .InRight hr)

private theorem greatest_mem {t : IM.Raw.tree A} {g : Int} (hg : IM_raw_greatest_key t = some g) :
    IM.Raw.In g t := by
  cases t with
  | Leaf => contradiction
  | Node l k a r h =>
    simp only [IM_raw_greatest_key, Option.some.injEq] at hg
    subst g
    exact match rightmost_mem r k with | .inl eq => .InRoot eq | .inr hr => .InRight hr

private theorem rightmost_bound (t : IM.Raw.tree A) (b : Int) (ht : OrderedAVL.Raw.bst t) :
    (∀ x, IM.Raw.In x t → x ≤ rightmost b t) ∧
      (IM.Raw.gt_tree b t → b ≤ rightmost b t) := by
  induction t generalizing b with
  | Leaf => exact ⟨fun _ h ↦ (nomatch h), fun _ ↦ Int.le_refl _⟩
  | Node l k a r h _ ihr =>
    cases ht with
    | BSNode _ br hl hr =>
      obtain ⟨rightBound, rootBound⟩ := ihr k br
      have hk := rootBound hr
      constructor
      · intro x hx
        cases hx with
        | InRoot eq => exact eq ▸ hk
        | InLeft hx => exact Int.le_trans (Int.le_of_lt (hl x hx)) hk
        | InRight hx => exact rightBound x hx
      · intro hb
        exact Int.le_trans (Int.le_of_lt (hb k (.InRoot rfl))) hk

theorem IM_greatest_key_none {A} (m : IM.t A) : IM_greatest_key m = none ↔ IM.Empty m := by
  obtain ⟨t, ht⟩ := m
  cases t with
  | Leaf => exact ⟨fun _ _ _ h ↦ (nomatch h), fun _ ↦ rfl⟩
  | Node l k a r h =>
    exact ⟨fun e ↦ (nomatch e), fun empty ↦ False.elim (empty k a (.MapsRoot rfl))⟩

theorem IM_greatest_key_none' {A} (m : IM.t A) : IM.Empty m → IM_greatest_key m = none :=
  (IM_greatest_key_none m).mpr

theorem IM_greatest_key_none'' {A} (m : IM.t A) : IM_greatest_key m = none → IM.Empty m :=
  (IM_greatest_key_none m).mp

theorem IM_greatest_key_In {A} (m : IM.t A) (gk : Int) : IM_greatest_key m = some gk → IM.In gk m :=
  fun h ↦ OrderedAVL.Raw.mapsTo_iff_in.mpr (greatest_mem h)

theorem IM_greatest_key_In' {A} (m : IM.t A) (k : IM.key) (h : IM.In k m) :
    ∃ gk, IM_greatest_key m = some gk := by
  cases hg : IM_greatest_key m with
  | none => obtain ⟨v, hv⟩ := h; exact False.elim (IM_greatest_key_none'' m hg k v hv)
  | some gk => exact ⟨gk, rfl⟩

theorem IM_greatest_key_lt {A} (m : IM.t A) (gk : Int) (hg : IM_greatest_key m = some gk) :
    IM.Raw.lt_tree (1 + gk) (IM.this m) := by
  obtain ⟨t, ht⟩ := m
  cases t with
  | Leaf => contradiction
  | Node l k a r h =>
    change some (rightmost k r) = some gk at hg
    have he := Option.some.inj hg
    intro x hx
    have hle := (rightmost_bound _ k ht).1 x hx
    change x ≤ rightmost k r at hle
    omega

theorem IM_raw_greatest_key_lr {elt} (m : IM.bst elt) (k : IM.Raw.key) (e : elt)
    (l : IM.Raw.tree elt) (t : Int) (r : IM.Raw.tree elt) (kl kr : Int)
    (hn : IM.this m = IM.Raw.Node l k e r t) (hl : IM_raw_greatest_key l = some kl)
    (hr : IM_raw_greatest_key r = some kr) : kl < kr := by
  have bst := hn ▸ m.is_bst
  cases bst with
  | BSNode _ _ left right => exact Int.lt_trans (left kl (greatest_mem hl)) (right kr (greatest_mem hr))

theorem next_key_correct {A} (m : IM.t A) (a : Int) (h : IM.In a m) : a < next_key m := by
  obtain ⟨k, hk⟩ := IM_greatest_key_In' m a h
  simpa [next_key, hk] using IM_greatest_key_lt m k hk a (OrderedAVL.Raw.mapsTo_iff_in.mp h)

end Vellvm.Utils.IntMaps
